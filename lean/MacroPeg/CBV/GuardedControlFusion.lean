import MacroPeg.CBV.GuardedWordSelection

/-! Recursive predicates inside selected arguments retain their real query
semantics and contribute exactly the empty captured word on success. -/
namespace Shallot.MacroPeg.CBV.GuardedControlFusion
open ReplayControlFusion (Part sourceLeaf)
open WordControlFusion (Plan parGrammar callLeaf enter gate par_rule)
open MixedControlFusion (AtOrigin origin_congr GateOK)
open WordArguments (Word value word_eval value_of_success)
open GuardedWordSelection (Shape Checks Agrees)

mutual
def render (parts : List Part) (specs : List Plan) : MExp → MExp
  | .call i [a] => match specs[i]? with
    | none => MExp.failAlways
    | some P => if GuardedWordSelection.shapeB a then
        chooseAt parts specs (.lit []) a (fun w => enter parts P w)
      else .seq (.andP (render parts specs a)) (enter parts P (render parts specs a))
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

  def scanArg (parts : List Part) (specs : List Plan) : MExp → MExp
    | .lit w => .lit w
    | .param k => .param k
    | .seq a b => .seq (scanArg parts specs a) (scanArg parts specs b)
    | .alt a b => .alt (scanArg parts specs a) (scanArg parts specs b)
    | .notP e => .notP (render parts specs e)
    | _ => MExp.failAlways

  def chooseAt (parts : List Part) (specs : List Plan) (before : MExp) : MExp → (MExp → MExp) → MExp
    | .lit w, K => .seq (.andP (.seq before (.lit w))) (K (.lit w))
    | .param k, K => .seq (.andP (.seq before (.param k))) (K (.param k))
    | .notP e, K => .seq (.andP (.seq before (.notP (render parts specs e)))) (K (.lit []))
    | .alt a b, K => RootObservation.branch (.andP (.seq before (scanArg parts specs a)))
        (chooseAt parts specs before a K) (chooseAt parts specs before b K)
    | .seq a b, K => chooseAt parts specs before a
        (fun u => chooseAt parts specs (.seq before u) b (fun v => K (.seq u v)))
    | _, _ => MExp.failAlways
end


theorem scanArg_eq (parts : List Part) (specs : List Plan) :
    ∀ a, scanArg parts specs a = GuardedWordSelection.argRender (render parts specs) a
  | .seq a b | .alt a b => by simp only [scanArg,GuardedWordSelection.argRender,scanArg_eq parts specs a,scanArg_eq parts specs b]
  | .lit _ | .param _ | .notP _ | .eps | .any | .chr _ | .range _ _ | .call _ _ | .star _ | .dbg _
  | .lam _ _ | .callParam _ _ | .invoke _ _ _ => rfl

theorem chooseAt_eq (parts : List Part) (specs : List Plan) : ∀ a before K,
    chooseAt parts specs before a K = GuardedWordSelection.selectAt (render parts specs) before a K
  | .seq a b, before, K => by simp only [chooseAt,GuardedWordSelection.selectAt,chooseAt_eq parts specs a,chooseAt_eq parts specs b]
  | .alt a b, before, K => by simp only [chooseAt,GuardedWordSelection.selectAt,scanArg_eq,chooseAt_eq parts specs a,chooseAt_eq parts specs b]
  | .lit _, _, _ | .param _, _, _ | .notP _, _, _ | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _
  | .call _ _, _, _ | .star _, _, _ | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl

def targetRule (parts : List Part) (specs : List Plan) (r : Part) : MRule :=
  ⟨if r.replay then 1 else 0,render parts specs r.body⟩

def seqGrammar (parts : List Part) (specs : List Plan) : MGrammar :=
  ⟨⟨0,.eps⟩ :: parts.map (targetRule parts specs)⟩

mutual
theorem render_firstOrder (parts : List Part) (specs : List Plan) : ∀ e, (render parts specs e).FirstOrder
  | .call i [a] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some P =>
      dsimp only []
      by_cases hA : GuardedWordSelection.shapeB a = true
      · rw [if_pos hA]
        rw [chooseAt_eq]
        apply GuardedWordSelection.selectAt_firstOrder (render parts specs) a
          ((GuardedWordSelection.shapeB_iff a).mp hA) (predicate_firstOrder parts specs a) (.lit []) True.intro
        intro w hw
        exact ⟨True.intro,Plan.firstOrder (WordControlFusion.callLeaf_firstOrder _ _ (WordArguments.word_firstOrder w hw)) P⟩
      · rw [if_neg hA]
        exact ⟨render_firstOrder _ _ a,True.intro,Plan.firstOrder (WordControlFusion.callLeaf_firstOrder _ _ (render_firstOrder _ _ a)) P⟩
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder _ _ a,render_firstOrder _ _ b⟩
  | .star a | .notP a => render_firstOrder _ _ a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem predicate_firstOrder (parts : List Part) (specs : List Plan) :
    ∀ a, Checks (fun e => (render parts specs e).FirstOrder) a
  | .notP e => render_firstOrder parts specs e
  | .seq a b | .alt a b => ⟨predicate_firstOrder parts specs a,predicate_firstOrder parts specs b⟩
  | .lit _ | .param _ | .eps | .any | .chr _ | .range _ _ | .call _ _ | .star _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
end

def Supported (specs : List Plan) : MExp → Prop
  | .call i [a] => Supported specs a ∧ ∀ P, specs[i]? = some P → Shape a ∨ AtOrigin P
  | .call _ _ => False
  | .seq a b | .alt a b => Supported specs a ∧ Supported specs b
  | .star a | .notP a => Supported specs a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

def ValidPart (specs : List Plan) (r : Part) : Prop :=
  Supported specs r.body ∧ (r.replay=false → ReplayFallbackFusion.Closed r.body)

theorem supported_firstOrder (specs : List Plan) : ∀ e, Supported specs e → e.FirstOrder
  | .call _ [a], h => ⟨supported_firstOrder specs a h.1,True.intro⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder specs a h.1,supported_firstOrder specs b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder specs a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem shape_of_arg : ∀ a, SequenceArguments.Arg a → Shape a
  | .lit _, _ | .param _, _ => trivial
  | .seq a b, h | .alt a b, h => ⟨shape_of_arg a h.1,shape_of_arg b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .star _, h | .notP _, h | .dbg _, h
  | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem selected_fragment_supported (specs : List Plan) : ∀ e, SelectedControlFusion.Supported specs e → Supported specs e
  | .call i [a], h => by
    refine ⟨selected_fragment_supported specs a h.1,?_⟩
    intro P hP
    rcases h.2 P hP with ha | ho
    · exact Or.inl (shape_of_arg a ha)
    · exact Or.inr ho
  | .seq a b, h | .alt a b, h => ⟨selected_fragment_supported specs a h.1,selected_fragment_supported specs b h.2⟩
  | .star a, h | .notP a, h => selected_fragment_supported specs a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem par_firstOrder {parts : List Part} {specs : List Plan} (hf : ∀ r ∈ parts, ValidPart specs r) :
    (parGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ specs.map (fun P => ⟨1,P.exp (sourceLeaf parts)⟩) at hr
  obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
  apply Plan.firstOrder
  exact ReplayControlFusion.sourceLeaf_firstOrder
    (fun r hr => ⟨supported_firstOrder specs _ (hf r hr).1,(hf r hr).2⟩)

theorem seq_firstOrder (parts : List Part) (specs : List Plan) : (seqGrammar parts specs).FirstOrder := by
  intro r hr
  change r ∈ (⟨0,.eps⟩ :: parts.map (targetRule parts specs)) at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder _ _ _

theorem gate_rule (parts : List Part) (specs : List Plan) :
    ruleAtM (seqGrammar parts specs).rules 0 = some ⟨0,.eps⟩ := rfl

theorem seq_rule (parts : List Part) (specs : List Plan) (i : Nat) :
    ruleAtM (seqGrammar parts specs).rules (i+1) = (parts[i]?).map (targetRule parts specs) := by
  simp [seqGrammar,ruleAtM_eq_getElem?]

def Shifted (parts : List Part) (specs : List Plan) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i P, specs[i]? = some P → ∀ w p, p ≤ x.length → valAt (T i [w]) p =
    evV (seqGrammar parts specs) x .callByValueSeq U [] (enter parts P (.lit w)) p

theorem physical_gate_ok (parts : List Part) (specs : List Plan) (x : List Char) (k : Nat) :
    GateOK x (tblV (seqGrammar parts specs) x .callByValueSeq k) := by
  intro p hp q hq
  cases k with
  | zero => cases hq
  | succ k =>
    rw [valAt_tblV_succ (gate_rule parts specs) [] hp] at hq
    simpa only [evV,Option.some.injEq] using hq.symm

theorem callLeaf_congr (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (E F : List (List Char)) (a b : MExp) (p : Nat)
    (ha : evV (seqGrammar parts specs) x .callByValueSeq U E a p =
      evV (seqGrammar parts specs) x .callByValueSeq U F b p) (i : Nat) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (callLeaf parts a i) p =
      evV (seqGrammar parts specs) x .callByValueSeq U F (callLeaf parts b i) p := by
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
      rw [ha]

theorem enter_origin (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (hG : GateOK x U)
    (E : List (List Char)) (a : MExp) (w : List Char) (P : Plan) (hP : AtOrigin P)
    (p : Nat) (hp : p ≤ x.length)
    (ha : evV (seqGrammar parts specs) x .callByValueSeq U E a p =
      evV (seqGrammar parts specs) x .callByValueSeq U [] (.lit w) p) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (enter parts P a) p =
      evV (seqGrammar parts specs) x .callByValueSeq U [] (enter parts P (.lit w)) p := by
  have hg (E : List (List Char)) : evV (seqGrammar parts specs) x .callByValueSeq U E gate p = valAt (U 0 []) p := by
    rw [gate,evV_call_seq (gate_rule parts specs) rfl]
    rfl
  unfold enter
  change (match evV (seqGrammar parts specs) x .callByValueSeq U E gate p with
    | some (some q) => evV (seqGrammar parts specs) x .callByValueSeq U E (P.exp (callLeaf parts a)) q
    | other => other) = (match evV (seqGrammar parts specs) x .callByValueSeq U [] gate p with
    | some (some q) => evV (seqGrammar parts specs) x .callByValueSeq U [] (P.exp (callLeaf parts (.lit w))) q
    | other => other)
  rw [hg E,hg []]
  cases hh : valAt (U 0 []) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      have hq := hG p hp q hh
      subst q
      exact origin_congr _ _ _ _ _ _ _ _ p (callLeaf_congr parts specs x U E [] a (.lit w) p ha) P hP

theorem callLeaf_word (parts : List Part) (specs : List Plan) (x : List Char)
    (U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (w : List Char)
    (ha : Word a) (hv : value E a = some w) (i p : Nat) :
    evV (seqGrammar parts specs) x .callByValueSeq U E (callLeaf parts a i) p =
      evV (seqGrammar parts specs) x .callByValueSeq U [] (callLeaf parts (.lit w) i) p := by
  apply callLeaf_congr
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


mutual
theorem evaluator_of_shift {parts : List Part} {specs : List Plan} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hT : SoundTV (parGrammar parts specs) x .callByValuePar T)
    (hOk : OkTV x.length T) (hU : OkTV x.length U) (hG : GateOK x U) (hshift : Shifted parts specs x T U) :
    ∀ e, Supported specs e → ∀ E p, p ≤ x.length →
      evV (parGrammar parts specs) x .callByValuePar T E e p =
        evV (seqGrammar parts specs) x .callByValueSeq U E (render parts specs e) p
  | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
  | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _ | .callParam _ _, hf, _, _, _
  | .invoke _ _ _, hf, _, _, _ => False.elim hf
  | .call _ [], hf, _, _, _ | .call _ (_::_::_), hf, _, _, _ => False.elim hf
  | .call i [a], hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hU hG hshift a hf.1 E p hp
    cases hr : specs[i]? with
    | none => simp [render,evV,par_rule,hr,MExp.failAlways]
    | some r =>
      have hpar : ruleAtM (parGrammar parts specs).rules i = some ⟨1,r.exp (sourceLeaf parts)⟩ := by
        rw [par_rule,hr]; rfl
      simp only [render,hr]
      rw [evV_call_par hpar rfl (by decide)]
      by_cases hA : GuardedWordSelection.shapeB a = true
      · rw [if_pos hA]
        have hArg := (GuardedWordSelection.shapeB_iff a).mp hA
        rw [chooseAt_eq,GuardedWordSelection.selectAt_eval (parGrammar parts specs) (seqGrammar parts specs)
          x T U E (render parts specs) hT hOk p a hArg
          (predicate_checks hT hOk hU hG hshift a hf.1 E)
          (.lit []) True.intro [] rfl p hp (by simp)
          (fun w => enter parts r w)
          (fun w => evV (seqGrammar parts specs) x .callByValueSeq U [] (enter parts r (.lit w)) p)
          (fun w hw word hval _ => enter_word parts specs x U hU E w word hw hval r p)]
        cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
        | none => rw [evPar_cons_none hv]
        | some result => cases result with
          | none => rw [evPar_cons_fail hv]
          | some q =>
            rw [evPar_cons_ok hv]
            exact hshift i r hr (pre x p q) p hp
      · rw [if_neg hA]
        have ho : AtOrigin r := by
          rcases hf.2 r hr with ha | ho
          · exact False.elim (hA ((GuardedWordSelection.shapeB_iff a).mpr ha))
          · exact ho
        have hguard : evV (seqGrammar parts specs) x .callByValueSeq U E (.andP (render parts specs a)) p =
            CallLookahead.peek p (evV (parGrammar parts specs) x .callByValuePar T E a p) := by
          rw [CallLookahead.evV_peek,← heq]
        cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
        | none => rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
        | some result => cases result with
          | none => rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
          | some q =>
            rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl))]
            change valAt (T i [pre x p q]) p = _
            obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix hT E a (supported_firstOrder specs a hf.1) p q hp hv
            have hlit : evV (seqGrammar parts specs) x .callByValueSeq U [] (.lit (pre x p q)) p = some (some q) := by
              simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hq]
            exact (hshift i r hr (pre x p q) p hp).trans
              (enter_origin parts specs x U hG E (render parts specs a) (pre x p q) r ho p hp
                ((heq.symm.trans hv).trans hlit.symm)).symm
  | .seq a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hU hG hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hU hG hshift b hf.2 E q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hU hG hshift a hf.1 E p hp
    cases hv : evV (parGrammar parts specs) x .callByValuePar T E a p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hU hG hshift b hf.2 E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift hT hOk hU hG hshift a hf E p hp]
  | .star a, hf, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hU hG hshift a hf E q (by omega))




theorem predicate_checks {parts : List Part} {specs : List Plan} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hT : SoundTV (parGrammar parts specs) x .callByValuePar T)
    (hOk : OkTV x.length T) (hU : OkTV x.length U) (hG : GateOK x U) (hshift : Shifted parts specs x T U) :
    ∀ a, Supported specs a → ∀ E,
      Checks (Agrees (parGrammar parts specs) (seqGrammar parts specs) x T U E (render parts specs)) a
  | .notP e, he, E => ⟨supported_firstOrder specs e he,fun p hp => evaluator_of_shift hT hOk hU hG hshift e he E p hp⟩
  | .seq a b, he, E | .alt a b, he, E =>
    ⟨predicate_checks hT hOk hU hG hshift a he.1 E,predicate_checks hT hOk hU hG hshift b he.2 E⟩
  | .lit _, _, _ | .param _, _, _ | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _
  | .call _ _, _, _ | .star _, _, _ | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => trivial
end

theorem tables_shifted {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart specs r) (x : List Char) (k : Nat) :
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
        exact evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k)
          (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) (physical_gate_ok parts specs x k) ih r.body he.1 [] z hz
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
          exact evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k)
            (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) (physical_gate_ok parts specs x k) ih r.body he.1 [w] rest.length hq

theorem evaluator_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart specs r) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : Supported specs e) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar parts specs) x .callByValuePar (tblV (parGrammar parts specs) x .callByValuePar k) E e p =
      evV (seqGrammar parts specs) x .callByValueSeq (tblV (seqGrammar parts specs) x .callByValueSeq k) E (render parts specs e) p :=
  evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k)
    (tblV_ok _ _ _ k) (tblV_ok _ _ _ k) (physical_gate_ok parts specs x k) (tables_shifted hf x k) e he E p hp

theorem decide_eq {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart specs r) (e : MExp) (he : Supported specs e) (x : List Char) :
    decideObsV .callByValuePar (parGrammar parts specs) x e =
      decideObsV .callByValueSeq (seqGrammar parts specs) x (render parts specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (parGrammar parts specs) (seqGrammar parts specs) x .callByValuePar .callByValueSeq
    e (render parts specs e) (fun k => evaluator_eq hf x k [] e he x.length (Nat.le_refl _))]

theorem observations_iff {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart specs r) (e : MExp) (he : Supported specs e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar parts specs) .callByValuePar e x r ↔
      SObs (seqGrammar parts specs) .callByValueSeq (render parts specs e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf) (by decide) (supported_firstOrder specs e he),
    ← decideObsV_iff (seq_firstOrder parts specs) (by decide) (render_firstOrder parts specs e),decide_eq hf e he x]

theorem language_translation {parts : List Part} {specs : List Plan}
    (hf : ∀ r ∈ parts, ValidPart specs r) (e : MExp) (he : Supported specs e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar parts specs) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar parts specs,render parts specs e,seq_firstOrder parts specs,render_firstOrder parts specs e,
    fun x => observations_iff hf e he x (some [])⟩






/-- The query inside the argument is tested after its first `a`, while the
capture still contains just the two consumed characters. -/
theorem predicate_at_argument_position :
    let parts : List Part := [⟨false,.chr 'a'⟩,⟨true,.eps⟩,⟨false,.star .any⟩,⟨false,.chr 'z'⟩]
    let specs : List Plan := [.alt (.seq (.leaf 0) (.leaf 1)) (.leaf 2),.leaf 3]
    let a : MExp := .seq (.lit ['a']) (.seq (.notP (.call 1 [.lit []])) (.alt (.lit ['a']) (.lit ['z'])))
    let e : MExp := .call 0 [a]
    Supported specs e ∧ (∀ r ∈ parts, ValidPart specs r) ∧
    evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar 1) [] e 3 = some (some 0) ∧
    evV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq 1) [] (render parts specs e) 3 = some (some 0) ∧
    evV (parGrammar parts specs) ['a','z','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','z','a'] .callByValuePar 1) [] e 3 = some none ∧
    evV (seqGrammar parts specs) ['a','z','a'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','z','a'] .callByValueSeq 1) [] (render parts specs e) 3 = some none := by
  dsimp only []
  constructor
  · simp [Supported,GuardedWordSelection.Shape]
  · constructor
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [ValidPart,Supported,ReplayFallbackFusion.Closed]
    · decide +kernel

/-- A nonterminating recursive predicate cannot fall through to the next
argument alternative at any finite physical table stage. -/
theorem undefined_predicate_stays_undefined :
    let parts : List Part := [⟨false,.star .any⟩,⟨false,.call 1 [.lit []]⟩]
    let specs : List Plan := [.leaf 0,.leaf 1]
    let a : MExp := .alt (.seq (.notP (.call 1 [.lit []])) (.lit ['a','a'])) (.lit ['a'])
    let e : MExp := .call 0 [a]
    ∀ k, evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar k) [] e 3 = none ∧
    evV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq
      (tblV (seqGrammar parts specs) ['a','a','a'] .callByValueSeq k) [] (render parts specs e) 3 = none := by
  dsimp only []
  let parts : List Part := [⟨false,.star .any⟩,⟨false,.call 1 [.lit []]⟩]
  let specs : List Plan := [.leaf 0,.leaf 1]
  let a : MExp := .alt (.seq (.notP (.call 1 [.lit []])) (.lit ['a','a'])) (.lit ['a'])
  let e : MExp := .call 0 [a]
  have hr : ruleAtM (parGrammar parts specs).rules 1 = some ⟨1,.call 1 [.lit []]⟩ := rfl
  have hroot : ruleAtM (parGrammar parts specs).rules 0 = some ⟨1,.star .any⟩ := rfl
  have hf : ∀ r ∈ parts, ValidPart specs r := by
    intro r hr
    simp only [parts,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [ValidPart,Supported,GuardedWordSelection.Shape,ReplayFallbackFusion.Closed,ReplayFallbackFusion.ClosedArgs]
  have he : Supported specs e := by simp [e,a,Supported,GuardedWordSelection.Shape]
  have cycle : ∀ k, valAt (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar k 1 [[]]) 3 = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ hr [[]] (by decide),evV_call_par hr rfl (by decide)]
      exact ih
  intro k
  have hcall : evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar k) [] (.call 1 [.lit []]) 3 = none := by
    rw [evV_call_par hr rfl (by decide)]
    exact cycle k
  have ha : evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar k) [] a 3 = none := by
    dsimp only [a]
    rw [evV_alt_none (evV_seq_none (evV_not_none hcall))]
  have hsrc : evV (parGrammar parts specs) ['a','a','a'] .callByValuePar
      (tblV (parGrammar parts specs) ['a','a','a'] .callByValuePar k) [] e 3 = none := by
    dsimp only [e]
    rw [evV_call_par hroot rfl (by decide),evPar_cons_none ha]
  exact ⟨hsrc,(evaluator_eq hf ['a','a','a'] k [] e he 3 (by decide)).symm.trans hsrc⟩

end Shallot.MacroPeg.CBV.GuardedControlFusion
