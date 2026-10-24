import MacroPeg.CBV.WordArguments

/-! Arbitrary consuming body control with position-independent word arguments.
The caller retains the argument expression and replays its same word wherever
body control needs it. A real entry rule preserves the user-round boundary. -/
namespace Shallot.MacroPeg.CBV.WordControlFusion
open WordArguments (Word value literal word_firstOrder word_eval value_of_success)
open ReplayControlFusion (Part sourceLeaf)

inductive Plan where
  | leaf : Nat → Plan
  | seq : Plan → Plan → Plan
  | alt : Plan → Plan → Plan
  | star : Plan → Plan
  | notP : Plan → Plan

namespace Plan

def exp (L : Nat → MExp) : Plan → MExp
  | .leaf i => L i
  | .seq a b => .seq (exp L a) (exp L b)
  | .alt a b => .alt (exp L a) (exp L b)
  | .star a => .star (exp L a)
  | .notP a => .notP (exp L a)

theorem firstOrder {L : Nat → MExp} (h : ∀ i, (L i).FirstOrder) : ∀ P, (exp L P).FirstOrder
  | .leaf i => h i
  | .seq a b | .alt a b => ⟨firstOrder h a,firstOrder h b⟩
  | .star a | .notP a => firstOrder h a

theorem eval_congr (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E F : List (List Char)) (L R : Nat → MExp)
    (hOk : OkTV x.length T)
    (hLeaf : ∀ i p, p ≤ x.length → evV g x s T E (L i) p = evV h x t U F (R i) p) :
    ∀ P p, p ≤ x.length → evV g x s T E (exp L P) p = evV h x t U F (exp R P) p
  | .leaf i, p, hp => hLeaf i p hp
  | .seq a b, p, hp => by
    have heq := eval_congr g h x s t T U E F L R hOk hLeaf a p hp
    cases hv : evV g x s T E (exp L a) p with
    | none => simp only [exp,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => simp only [exp,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [exp,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact eval_congr g h x s t T U E F L R hOk hLeaf b q (evV_ok hOk _ p hp q hv)
  | .alt a b, p, hp => by
    have heq := eval_congr g h x s t T U E F L R hOk hLeaf a p hp
    cases hv : evV g x s T E (exp L a) p with
    | none => simp only [exp,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [exp,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact eval_congr g h x s t T U E F L R hOk hLeaf b p hp
      | some q => simp only [exp,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, p, hp => by
    simp only [exp,evV]
    rw [eval_congr g h x s t T U E F L R hOk hLeaf a p hp]
  | .star a, p, hp => by
    simp only [exp,evV_star]
    exact evStar_congr p (fun q hq => eval_congr g h x s t T U E F L R hOk hLeaf a q (by omega))
end Plan

def Supported : MExp → Prop
  | .call _ [a] => Word a
  | .call _ _ => False
  | .seq a b | .alt a b => Supported a ∧ Supported b
  | .star a | .notP a => Supported a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

def ValidPart (r : Part) : Prop := Supported r.body ∧ (r.replay=false → ReplayFallbackFusion.Closed r.body)

def parGrammar (parts : List Part) (specs : List Plan) : MGrammar :=
  ⟨specs.map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩)⟩

def callLeaf (parts : List Part) (a : MExp) (i : Nat) : MExp := match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.replay then .call (i+1) [a] else .call (i+1) []

def gate : MExp := .call 0 []

def enter (parts : List Part) (P : Plan) (a : MExp) : MExp := .seq gate (P.exp (callLeaf parts a))

def render (parts : List Part) (specs : List Plan) : MExp → MExp
  | .call i [a] => match specs[i]? with
    | none => MExp.failAlways
    | some P => .seq (.andP (render parts specs a)) (enter parts P (render parts specs a))
  | .call _ _ => MExp.failAlways
  | .param k => .param k
  | .seq a b => .seq (render parts specs a) (render parts specs b)
  | .alt a b => .alt (render parts specs a) (render parts specs b)
  | .star a => .star (render parts specs a)
  | .notP a => .notP (render parts specs a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def targetRule (parts : List Part) (specs : List Plan) (r : Part) : MRule :=
  ⟨if r.replay then 1 else 0,render parts specs r.body⟩

def seqGrammar (parts : List Part) (specs : List Plan) : MGrammar :=
  ⟨⟨0,.eps⟩ :: parts.map (targetRule parts specs)⟩

theorem supported_firstOrder : ∀ e, Supported e → e.FirstOrder
  | .call _ [a], h => ⟨word_firstOrder a h,True.intro⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder a h.1,supported_firstOrder b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem callLeaf_firstOrder (parts : List Part) (a : MExp) (ha : a.FirstOrder) (i : Nat) :
    (callLeaf parts a i).FirstOrder := by
  unfold callLeaf
  cases parts[i]? with
  | none => trivial
  | some r =>
    dsimp only []
    cases r.replay <;> simp only [Bool.false_eq_true,if_false,if_true]
    · trivial
    · exact ⟨ha,True.intro⟩

theorem render_firstOrder (parts : List Part) (specs : List Plan) : ∀ e, (render parts specs e).FirstOrder
  | .call i [a] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some P => exact ⟨render_firstOrder _ _ a,True.intro,Plan.firstOrder (callLeaf_firstOrder _ _ (render_firstOrder _ _ a)) P⟩
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder _ _ a,render_firstOrder _ _ b⟩
  | .star a | .notP a => render_firstOrder _ _ a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem render_word (parts : List Part) (specs : List Plan) : ∀ a, Word a → render parts specs a = a
  | .lit _, _ | .param _, _ => rfl
  | .seq a b, h => by simp only [render,render_word parts specs a h.1,render_word parts specs b h.2]
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .alt _ _, h | .star _, h | .notP _, h
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem par_firstOrder {parts : List Part} (hf : ∀ r ∈ parts, ValidPart r) (specs : List Plan) :
    (parGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ specs.map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩) at hr
  obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
  apply Plan.firstOrder
  exact ReplayControlFusion.sourceLeaf_firstOrder
    (fun r hr => ⟨supported_firstOrder _ (hf r hr).1,(hf r hr).2⟩)

theorem seq_firstOrder (parts : List Part) (specs : List Plan) : (seqGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ (⟨0,.eps⟩ :: parts.map (targetRule parts specs)) at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder _ _ _

theorem par_rule (parts : List Part) (specs : List Plan) (i : Nat) :
    ruleAtM (parGrammar parts specs).rules i = (specs[i]?).map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem gate_rule (parts : List Part) (specs : List Plan) :
    ruleAtM (seqGrammar parts specs).rules 0 = some ⟨0,.eps⟩ := rfl

theorem seq_rule (parts : List Part) (specs : List Plan) (i : Nat) :
    ruleAtM (seqGrammar parts specs).rules (i+1) = (parts[i]?).map (targetRule parts specs) := by
  simp [seqGrammar,ruleAtM_eq_getElem?]

def Shifted (parts : List Part) (specs : List Plan) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i P, specs[i]? = some P → ∀ w p, p ≤ x.length → valAt (T i [w]) p =
    evV (seqGrammar parts specs) x .callByValueSeq U [] (enter parts P (.lit w)) p

theorem callLeaf_word (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (w : List Char)
    (ha : Word a) (hv : value E a = some w) (i p : Nat) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (callLeaf parts a i) p =
      evV (seqGrammar parts specs) x .callByValueSeq U [] (callLeaf parts (.lit w) i) p := by
  unfold callLeaf
  cases hr : parts[i]? with
  | none => simp [MExp.failAlways,evV]
  | some r =>
    have hh : ruleAtM (seqGrammar parts specs).rules (i+1) = some (targetRule parts specs r) := by
      rw [seq_rule,hr]; rfl
    dsimp only []
    cases hb : r.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [evV_call_seq hh (by simp [targetRule,hb]),evV_call_seq hh (by simp [targetRule,hb])]
      rfl
    · simp only [if_true]
      rw [evV_call_seq hh (by simp [targetRule,hb]),evV_call_seq hh (by simp [targetRule,hb])]
      simp only [evSeqArgs]
      rw [word_eval _ _ _ _ E a ha p,hv]
      rfl

theorem enter_word (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (hU : OkTV x.length U)
    (E : List (List Char)) (a : MExp) (w : List Char) (ha : Word a) (hv : value E a = some w)
    (P : Plan) (p : Nat) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (enter parts P a) p =
      evV (seqGrammar parts specs) x .callByValueSeq U [] (enter parts P (.lit w)) p := by
  unfold enter
  change (match evV (seqGrammar parts specs) x .callByValueSeq U E gate p with
    | some (some q) => evV (seqGrammar parts specs) x .callByValueSeq U E (P.exp (callLeaf parts a)) q
    | other => other) = _
  have hg (E : List (List Char)) : evV (seqGrammar parts specs) x .callByValueSeq U E gate p = valAt (U 0 []) p := by
    rw [gate,evV_call_seq (gate_rule parts specs) rfl]
    rfl
  change _ = match evV (seqGrammar parts specs) x .callByValueSeq U [] gate p with
    | some (some q) => evV (seqGrammar parts specs) x .callByValueSeq U [] (P.exp (callLeaf parts (.lit w))) q
    | other => other
  rw [hg E,hg []]
  cases hh : valAt (U 0 []) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      exact Plan.eval_congr _ _ _ _ _ _ _ _ _ _ _ hU
        (fun i p _ => callLeaf_word parts specs x U E a w ha hv i p) P q (hU 0 [] p q hh)

theorem evaluator_of_shift {parts : List Part} {specs : List Plan} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hOk : OkTV x.length T) (hU : OkTV x.length U) (hshift : Shifted parts specs x T U) :
    ∀ e, Supported e → ∀ E p, p ≤ x.length →
      evV (parGrammar parts specs) x .callByValuePar T E e p =
        evV (seqGrammar parts specs) x .callByValueSeq U E (render parts specs e) p
  | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
  | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _ | .callParam _ _, hf, _, _, _
  | .invoke _ _ _, hf, _, _, _ => False.elim hf
  | .call _ [], hf, _, _, _ | .call _ (_::_::_), hf, _, _, _ => False.elim hf
  | .call i [a], hf, E, p, hp => by
    have heq : evV (parGrammar parts specs) x .callByValuePar T E a p =
        evV (seqGrammar parts specs) x .callByValueSeq U E a p := by
      rw [word_eval _ _ _ _ E a hf p,word_eval _ _ _ _ E a hf p]
      cases value E a <;> rfl
    cases hr : specs[i]? with
    | none => simp [render,evV,par_rule,hr,MExp.failAlways]
    | some r =>
      have hpar : ruleAtM (parGrammar parts specs).rules i = some ⟨1,r.exp (sourceLeaf parts)⟩ := by
        rw [par_rule,hr]; rfl
      simp only [render,hr,render_word parts specs a hf]
      rw [evV_call_par hpar rfl (by decide)]
      have hguard : evV (seqGrammar parts specs) x .callByValueSeq U E (.andP a) p =
          CallLookahead.peek p (evV (parGrammar parts specs) x .callByValuePar T E a p) := by
        rw [CallLookahead.evV_peek,← heq]
      cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
      | none =>
        rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
      | some result => cases result with
        | none =>
          rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
        | some q =>
          rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl))]
          change valAt (T i [pre x p q]) p = _
          have hw := value_of_success _ _ _ _ E a hf p q hp hv
          exact (hshift i r hr (pre x p q) p hp).trans
            (enter_word parts specs x U hU E a (pre x p q) hf hw r p).symm
  | .seq a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hOk hU hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hOk hU hshift b hf.2 E q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hOk hU hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hOk hU hshift b hf.2 E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift hOk hU hshift a hf E p hp]
  | .star a, hf, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hOk hU hshift a hf E q (by omega))




/-- The extra entry rule prevents a failed later replay from answering at
stage zero, before the source rule has been unfolded even once. -/
theorem tables_shifted {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (x : List Char) (k : Nat) :
    Shifted parts specs x (tblV (parGrammar parts specs) x .callByValuePar k)
      (tblV (seqGrammar parts specs) x .callByValueSeq k) := by
  induction k with
  | zero =>
    intro i P hr w p hp
    have hg : evV (seqGrammar parts specs) x .callByValueSeq
        (tblV (seqGrammar parts specs) x .callByValueSeq 0) [] gate p = none := by
      rw [gate,evV_call_seq (gate_rule parts specs) rfl]
      rfl
    rw [enter,evV_seq_none hg]
    rfl
  | succ k ih =>
    intro i P hr w p hp
    have hpar : ruleAtM (parGrammar parts specs).rules i = some ⟨1,P.exp (sourceLeaf parts)⟩ := by
      rw [par_rule,hr]; rfl
    have hg : evV (seqGrammar parts specs) x .callByValueSeq
        (tblV (seqGrammar parts specs) x .callByValueSeq (k+1)) [] gate p = some (some p) := by
      rw [gate,evV_call_seq (gate_rule parts specs) rfl]
      change valAt (tblV (seqGrammar parts specs) x .callByValueSeq (k+1) 0 []) p = _
      rw [valAt_tblV_succ (gate_rule parts specs) [] hp]
      rfl
    rw [valAt_tblV_succ hpar [w] hp,enter,evV_seq_ok hg]
    refine Plan.eval_congr _ _ _ _ _ _ _ _ _ _ _ (tblV_ok _ _ _ k) ?_ P p hp
    intro j z hz
    cases hj : parts[j]? with
    | none => simp [sourceLeaf,callLeaf,hj,MExp.failAlways,evV]
    | some r =>
      have he := hf r (List.mem_of_getElem? hj)
      have hlookup : ruleAtM (seqGrammar parts specs).rules (j+1) = some (targetRule parts specs r) := by
        rw [seq_rule,hj]; rfl
      simp only [sourceLeaf,callLeaf,hj]
      cases hb : r.replay
      · simp only [Bool.false_eq_true,if_false]
        rw [evV_call_seq hlookup (by simp [targetRule,hb])]
        change evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k)
          [w] r.body z = valAt (tblV (seqGrammar parts specs) x .callByValueSeq (k+1) (j+1) []) z
        rw [valAt_tblV_succ hlookup [] hz,ReplayFallbackFusion.closed_env _ _ _ _ r.body (he.2 hb) [w] z]
        exact evaluator_of_shift (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) ih r.body he.1 [] z hz
      · simp only [if_true]
        rw [evV_call_seq hlookup (by simp [targetRule,hb])]
        cases hs : Shallot.stripPrefix? w (sfx x z) with
        | none =>
          have hm : evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k)
              [w] (.param 0) z = some none := by simp [evV,hs]
          have hl : evV (seqGrammar parts specs) x .callByValueSeq (tblV (seqGrammar parts specs) x .callByValueSeq (k+1))
              [] (.lit w) z = some none := by simp [evV,hs]
          rw [evV_seq_fail hm,evSeq_cons_fail hl]
        | some rest =>
          have hm : evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k)
              [w] (.param 0) z = some (some rest.length) := by simp [evV,hs]
          have hl : evV (seqGrammar parts specs) x .callByValueSeq (tblV (seqGrammar parts specs) x .callByValueSeq (k+1))
              [] (.lit w) z = some (some rest.length) := by simp [evV,hs]
          have hq := evV_ok (tblV_ok (seqGrammar parts specs) x .callByValueSeq (k+1)) (.lit w) z hz rest.length hl
          have hw := value_of_success _ _ _ _ [] (.lit w) (by trivial) z rest.length hz hl
          have hword : pre x z rest.length = w := by simpa only [WordArguments.value,Option.some.injEq] using hw.symm
          rw [evV_seq_ok hm,evSeq_cons_ok hl]
          change _ = valAt (tblV (seqGrammar parts specs) x .callByValueSeq (k+1) (j+1) [pre x z rest.length]) rest.length
          rw [hword,valAt_tblV_succ hlookup [w] hq]
          exact evaluator_of_shift (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) ih r.body he.1 [w] rest.length hq

theorem evaluator_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : Supported e) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k) E e p =
      evV (seqGrammar parts specs) x .callByValueSeq (tblV (seqGrammar parts specs) x .callByValueSeq k) E (render parts specs e) p :=
  evaluator_of_shift (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) (tables_shifted hf x k) e he E p hp

theorem decide_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (e : MExp) (he : Supported e) (x : List Char) :
    decideObsV .callByValuePar (parGrammar parts specs) x e =
      decideObsV .callByValueSeq (seqGrammar parts specs) x (render parts specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (parGrammar parts specs) (seqGrammar parts specs) x .callByValuePar .callByValueSeq
    e (render parts specs e) (fun k => evaluator_eq hf x k [] e he x.length (Nat.le_refl _))]

theorem observations_iff {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (e : MExp) (he : Supported e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar parts specs) .callByValuePar e x r ↔
      SObs (seqGrammar parts specs) .callByValueSeq (render parts specs e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf specs) (by decide) (supported_firstOrder e he),
    ← decideObsV_iff (seq_firstOrder parts specs) (by decide) (render_firstOrder parts specs e),decide_eq hf e he x]

theorem language_translation {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (e : MExp) (he : Supported e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar parts specs) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar parts specs,render parts specs e,seq_firstOrder parts specs,render_firstOrder parts specs e,
    fun x => observations_iff hf e he x (some [])⟩


/-- A real consuming prefix precedes capture reuse; repetition can repeat
that pattern while the argument still denotes its original word. -/
theorem consuming_prefix_and_repetition :
    let parts : List Part := [⟨false,.chr 'a'⟩,⟨true,.eps⟩]
    let specs : List Plan := [.seq (.leaf 0) (.leaf 1),.star (.seq (.leaf 0) (.leaf 1))]
    let e : MExp := .call 0 [.lit ['a','a']]
    let loop : MExp := .call 1 [.lit ['a','a']]
    evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar 1) [] e 3 = some (some 0) ∧
    evV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq 1) [] (render parts specs e) 3 = some (some 0) ∧
    evV (parGrammar parts specs) ['a','a','b'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','b'] .callByValuePar 1) [] e 3 = some none ∧
    evV (seqGrammar parts specs) ['a','a','b'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','a','b'] .callByValueSeq 1) [] (render parts specs e) 3 = some none ∧
    evV (parGrammar parts specs) (List.replicate 6 'a') .callByValuePar
      (tblV (parGrammar parts specs) (List.replicate 6 'a') .callByValuePar 1) [] loop 6 = some (some 0) ∧
    evV (seqGrammar parts specs) (List.replicate 6 'a') .callByValueSeq
      (tblV (seqGrammar parts specs) (List.replicate 6 'a') .callByValueSeq 1) [] (render parts specs loop) 6 = some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.WordControlFusion
