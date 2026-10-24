import MacroPeg.CBV.ReplayFallbackFusion

/-! Caller-side control trees can inspect a capture in several branches and
predicates without committing to its advanced endpoint. Captures are runtime
values; only the finite syntax of body control is expanded at call sites. -/
namespace Shallot.MacroPeg.CBV.ReplayControlFusion
open ReplayFallbackFusion (Closed closed_firstOrder closed_env)

structure Part where
  replay : Bool
  body : MExp

inductive Plan where
  | leaf : Nat → Plan
  | alt : Plan → Plan → Plan
  | notP : Plan → Plan
  | guard : Plan → Plan → Plan

namespace Plan

def All (P : Nat → Prop) : Plan → Prop
  | .leaf i => P i
  | .alt a b | .guard a b => All P a ∧ All P b
  | .notP a => All P a

def eval (L : Nat → Res) (p : Nat) : Plan → Res
  | .leaf i => L i
  | .alt a b => ReplayFallbackFusion.orElse (eval L p a) (eval L p b)
  | .notP a => match eval L p a with
    | some (some _) => some none
    | some none => some (some p)
    | none => none
  | .guard a b => match eval L p a with
    | some (some _) => eval L p b
    | other => other

theorem all_of_forall {P : Nat → Prop} (h : ∀ i, P i) : ∀ t, All P t
  | .leaf i => h i
  | .alt a b | .guard a b => ⟨all_of_forall h a,all_of_forall h b⟩
  | .notP a => all_of_forall h a

theorem all_imp {P Q : Nat → Prop} (h : ∀ i, P i → Q i) : ∀ t, All P t → All Q t
  | .leaf i, hi => h i hi
  | .alt a b, hi | .guard a b, hi => ⟨all_imp h a hi.1,all_imp h b hi.2⟩
  | .notP a, hi => all_imp h a hi

theorem eval_congr {L R : Nat → Res} {p : Nat} :
    ∀ P, All (fun i => L i = R i) P → eval L p P = eval R p P
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => by simp only [eval,eval_congr a h.1,eval_congr b h.2]
  | .notP a, h => by simp only [eval,eval_congr a h]

theorem eval_none {L : Nat → Res} {p : Nat} :
    ∀ P, All (fun i => L i = none) P → eval L p P = none
  | .leaf _, h => h
  | .alt a b, h => by simp only [eval,eval_none a h.1,ReplayFallbackFusion.orElse]
  | .guard a b, h => by simp only [eval,eval_none a h.1]
  | .notP a, h => by simp only [eval,eval_none a h]

/-- Interpret a finite control tree using expression leaves. -/
def exp (L : Nat → MExp) : Plan → MExp
  | .leaf i => L i
  | .alt a b => .alt (exp L a) (exp L b)
  | .notP a => .notP (exp L a)
  | .guard a b => .seq (.andP (exp L a)) (exp L b)

theorem exp_firstOrder {L : Nat → MExp} (hL : ∀ i, (L i).FirstOrder) :
    ∀ P, (exp L P).FirstOrder
  | .leaf i => hL i
  | .alt a b | .guard a b => ⟨exp_firstOrder hL a,exp_firstOrder hL b⟩
  | .notP a => exp_firstOrder hL a

/-- Guard failure and undefinedness retain their original partial results. -/
theorem exp_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (L : Nat → MExp) (p : Nat) :
    ∀ P, evV g x s T E (exp L P) p = eval (fun i => evV g x s T E (L i) p) p P
  | .leaf _ => rfl
  | .alt a b => by simp only [exp,evV,exp_eval g x s T E L p a,exp_eval g x s T E L p b,eval,ReplayFallbackFusion.orElse] <;> rfl
  | .notP a => by simp only [exp,evV,exp_eval g x s T E L p a,eval] <;> rfl
  | .guard a b => by
    rw [exp]
    change (match evV g x s T E (.andP (exp L a)) p with
      | some (some q) => evV g x s T E (exp L b) q | other => other) = _
    rw [CallLookahead.evV_peek,exp_eval g x s T E L p a]
    cases h : eval (fun i => evV g x s T E (L i) p) p a with
    | none => simp only [eval,h,CallLookahead.peek]
    | some r => cases r with
      | none => simp only [eval,h,CallLookahead.peek]
      | some q => simp only [eval,h,CallLookahead.peek,exp_eval g x s T E L p b]
end Plan

def ValidPart (r : Part) : Prop := r.body.FirstOrder ∧ (r.replay = false → ReplayFallbackFusion.Closed r.body)
def ValidPlan (parts : List Part) (P : Plan) : Prop := Plan.All (fun i => ∃ r, parts[i]? = some r) P

def sourceLeaf (parts : List Part) (i : Nat) : MExp := match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.replay then .seq (.param 0) r.body else r.body

def parGrammar (parts : List Part) (specs : List Plan) : MGrammar :=
  ⟨specs.map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩)⟩

def callLeaf (parts : List Part) (a : MExp) (i : Nat) : MExp := match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.replay then .call i [a] else .call i []

def render (parts : List Part) (specs : List Plan) : MExp → MExp
  | .call i [a] => match specs[i]? with
    | none => MExp.failAlways
    | some P => .seq (.andP (render parts specs a)) (P.exp (callLeaf parts (render parts specs a)))
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
  ⟨parts.map (targetRule parts specs)⟩

theorem callLeaf_firstOrder (parts : List Part) (a : MExp) (ha : a.FirstOrder) (i : Nat) :
    (callLeaf parts a i).FirstOrder := by
  unfold callLeaf
  cases parts[i]? with
  | none => trivial
  | some r =>
    dsimp only []
    cases hb : r.replay <;> simp only [Bool.false_eq_true,if_false,if_true]
    · trivial
    · exact ⟨ha,True.intro⟩

theorem render_firstOrder (parts : List Part) (specs : List Plan) : ∀ e, (render parts specs e).FirstOrder
  | .call i [a] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some P => exact ⟨render_firstOrder _ _ a,Plan.exp_firstOrder (callLeaf_firstOrder _ _ (render_firstOrder _ _ a)) P⟩
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder _ _ a,render_firstOrder _ _ b⟩
  | .star a | .notP a => render_firstOrder _ _ a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem sourceLeaf_firstOrder {parts : List Part} (hf : ∀ r ∈ parts, ValidPart r) (i : Nat) :
    (sourceLeaf parts i).FirstOrder := by
  unfold sourceLeaf
  cases hr : parts[i]? with
  | none => trivial
  | some r =>
    have he := (hf r (List.mem_of_getElem? hr)).1
    dsimp only []
    cases hb : r.replay <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact he
    · exact ⟨True.intro,he⟩

theorem par_firstOrder {parts : List Part} (hf : ∀ r ∈ parts, ValidPart r) (specs : List Plan) :
    (parGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ specs.map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩) at hr
  obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
  exact Plan.exp_firstOrder (sourceLeaf_firstOrder hf) P

theorem seq_firstOrder (parts : List Part) (specs : List Plan) : (seqGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ parts.map (targetRule parts specs) at hr
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder _ _ _

theorem par_rule (parts : List Part) (specs : List Plan) (i : Nat) :
    ruleAtM (parGrammar parts specs).rules i = (specs[i]?).map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem seq_rule (parts : List Part) (specs : List Plan) (i : Nat) :
    ruleAtM (seqGrammar parts specs).rules i = (parts[i]?).map (targetRule parts specs) := by
  simp [seqGrammar,ruleAtM_eq_getElem?]

def leafRows (parts : List Part) (U : Nat → List (List Char) → Val)
    (w : List Char) (p q i : Nat) : Res := match parts[i]? with
  | none => some none
  | some r => if r.replay then valAt (U i [w]) q else valAt (U i []) p

def Shifted (parts : List Part) (specs : List Plan) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i P, specs[i]? = some P → ∀ w p q, p ≤ x.length → q ≤ x.length →
    sfx x p = w ++ sfx x q → valAt (T i [w]) p = P.eval (leafRows parts U w p q) p


theorem callLeaf_eval (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (p q : Nat)
    (ha : evV (seqGrammar parts specs) x .callByValueSeq U E a p = some (some q)) (i : Nat) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (callLeaf parts a i) p =
      leafRows parts U (pre x p q) p q i := by
  unfold callLeaf leafRows
  cases hr : parts[i]? with
  | none => simp [MExp.failAlways,evV]
  | some r =>
    have hlookup : ruleAtM (seqGrammar parts specs).rules i = some (targetRule parts specs r) := by
      rw [seq_rule,hr]; rfl
    dsimp only []
    cases hb : r.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [evV_call_seq hlookup (by simp [targetRule,hb])]
      rfl
    · simp only [if_true]
      rw [evV_call_seq hlookup (by simp [targetRule,hb]),evSeq_cons_ok ha]
      rfl

theorem evaluator_of_shift {parts : List Part} {specs : List Plan} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hT : SoundTV (parGrammar parts specs) x .callByValuePar T)
    (hOk : OkTV x.length T) (hshift : Shifted parts specs x T U) :
    ∀ e, e.FirstOrder → ∀ E p, p ≤ x.length →
      evV (parGrammar parts specs) x .callByValuePar T E e p =
        evV (seqGrammar parts specs) x .callByValueSeq U E (render parts specs e) p
  | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
  | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _ | .callParam _ _, hf, _, _, _
  | .invoke _ _ _, hf, _, _, _ => False.elim hf
  | .call i [], hf, E, p, hp | .call i (_::_::_), hf, E, p, hp => by
    cases hr : specs[i]? <;> simp [render,evV,par_rule,hr,MExp.failAlways]
  | .call i [a], hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hr : specs[i]? with
    | none => simp [render,evV,par_rule,hr,MExp.failAlways]
    | some r =>
      have hpar : ruleAtM (parGrammar parts specs).rules i = some ⟨1,r.exp (sourceLeaf parts)⟩ := by
        rw [par_rule,hr]; rfl
      simp only [render,hr]
      rw [evV_call_par hpar rfl (by decide)]
      have hguard : evV (seqGrammar parts specs) x .callByValueSeq U E (.andP (render parts specs a)) p =
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
          rw [Plan.exp_eval]
          have hl : (fun j => evV (seqGrammar parts specs) x .callByValueSeq U E
              (callLeaf parts (render parts specs a) j) p) = leafRows parts U (pre x p q) p q := by
            funext j
            exact callLeaf_eval parts specs x U E _ p q (heq.symm.trans hv) j
          rw [hl]
          obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix hT E a hf.1 p q hp hv
          exact hshift i r hr (pre x p q) p q hp hq hs
  | .seq a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 E q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift hT hOk hshift a hf E p hp]
  | .star a, hf, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a hf E q (by omega))



/-- Every finite control tree is related at every physical user-table round.
No semantic assumption on recursively called user rules remains. -/
theorem tables_shifted {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (hv : ∀ P ∈ specs, ValidPlan parts P)
    (x : List Char) (k : Nat) :
    Shifted parts specs x (tblV (parGrammar parts specs) x .callByValuePar k)
      (tblV (seqGrammar parts specs) x .callByValueSeq k) := by
  induction k with
  | zero =>
    intro i P hr w p q hp hq hs
    change none = P.eval (leafRows parts (tblV (seqGrammar parts specs) x .callByValueSeq 0) w p q) p
    symm
    apply Plan.eval_none
    apply Plan.all_imp (t := P) _ (hv P (List.mem_of_getElem? hr))
    intro j hj
    obtain ⟨r,hr⟩ := hj
    simp only [leafRows,hr,tblV,valAt_nil]
    cases r.replay <;> rfl
  | succ k ih =>
    intro i P hr w p q hp hq hs
    have hpar : ruleAtM (parGrammar parts specs).rules i = some ⟨1,P.exp (sourceLeaf parts)⟩ := by
      rw [par_rule,hr]; rfl
    rw [valAt_tblV_succ hpar [w] hp,Plan.exp_eval]
    apply Plan.eval_congr
    apply Plan.all_imp (t := P) _ (hv P (List.mem_of_getElem? hr))
    intro j hj
    obtain ⟨r,hr⟩ := hj
    have he := hf r (List.mem_of_getElem? hr)
    have hlookup : ruleAtM (seqGrammar parts specs).rules j = some (targetRule parts specs r) := by
      rw [seq_rule,hr]; rfl
    simp only [sourceLeaf,leafRows,hr]
    cases hb : r.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [valAt_tblV_succ hlookup [] hp]
      change evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k)
          [w] r.body p = evV (seqGrammar parts specs) x .callByValueSeq
          (tblV (seqGrammar parts specs) x .callByValueSeq k) [] (render parts specs r.body) p
      rw [closed_env _ _ _ _ r.body (he.2 hb) [w] p]
      exact evaluator_of_shift (tblV_sound (par_firstOrder hf specs) (by decide) k) (tblV_ok _ _ _ k)
        ih r.body he.1 [] p hp
    · simp only [if_true]
      rw [valAt_tblV_succ hlookup [w] hq]
      have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs
      simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x hq]
      exact evaluator_of_shift (tblV_sound (par_firstOrder hf specs) (by decide) k) (tblV_ok _ _ _ k)
        ih r.body he.1 [w] q hq

theorem evaluator_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (hv : ∀ P ∈ specs, ValidPlan parts P)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k) E e p =
      evV (seqGrammar parts specs) x .callByValueSeq (tblV (seqGrammar parts specs) x .callByValueSeq k) E (render parts specs e) p :=
  evaluator_of_shift (tblV_sound (par_firstOrder hf specs) (by decide) k) (tblV_ok _ _ _ k)
    (tables_shifted hf hv x k) e he E p hp

theorem decide_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (hv : ∀ P ∈ specs, ValidPlan parts P)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (parGrammar parts specs) x e =
      decideObsV .callByValueSeq (seqGrammar parts specs) x (render parts specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (parGrammar parts specs) (seqGrammar parts specs) x .callByValuePar .callByValueSeq
    e (render parts specs e) (fun k => evaluator_eq hf hv x k [] e he x.length (Nat.le_refl _))]

theorem observations_iff {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (hv : ∀ P ∈ specs, ValidPlan parts P)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar parts specs) .callByValuePar e x r ↔
      SObs (seqGrammar parts specs) .callByValueSeq (render parts specs e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf specs) (by decide) he,
    ← decideObsV_iff (seq_firstOrder parts specs) (by decide) (render_firstOrder parts specs e),decide_eq hf hv e he x]

theorem language_translation {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart r) (hv : ∀ P ∈ specs, ValidPlan parts P)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar parts specs) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar parts specs,render parts specs e,seq_firstOrder parts specs,render_firstOrder parts specs e,
    fun x => observations_iff hf hv e he x (some [])⟩


/-- Both alternatives use the captured value: the second rejects `x z`
before consuming `a` from the original caller position. -/
theorem capture_dependent_fallback :
    let parts : List Part := [⟨true,MExp.failAlways⟩,⟨true,.chr 'z'⟩,⟨false,.chr 'a'⟩]
    let specs : List Plan := [.alt (.leaf 0) (.guard (.notP (.leaf 1)) (.leaf 2))]
    let e : MExp := .call 0 [.lit ['a','b']]
    evV (parGrammar parts specs) ['a','b'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','b'] .callByValuePar 1) [] e 2 = some (some 1) ∧
    evV (seqGrammar parts specs) ['a','b'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','b'] .callByValueSeq 1) [] (render parts specs e) 2 = some (some 1) ∧
    evV (parGrammar parts specs) ['a','b','z'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','b','z'] .callByValuePar 1) [] e 3 = some none ∧
    evV (seqGrammar parts specs) ['a','b','z'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','b','z'] .callByValueSeq 1) [] (render parts specs e) 3 = some none := by
  decide

end Shallot.MacroPeg.CBV.ReplayControlFusion
