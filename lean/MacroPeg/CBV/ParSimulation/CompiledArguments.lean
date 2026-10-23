import MacroPeg.CBV.ParSimulation.ArgumentRouting

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode ExprAvailable ArgsAvailable StagesAvailable compilerSlotSize compilerFragmentAt
  seqResult seqResult_success seqResult_failure evaluatedCapture_le)

theorem compiledArgument_rules (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args arity callee actuals stage ∈ c.nodes) (failure : Bool) :
    let base := c.address (.args arity callee actuals stage)
    let off := if failure then 20 else 10
    let cw := 3 + c.digits + 2 * arity
    let w := cw + 2 * stage
    ruleAtM c.target.rules (base + off) = some ⟨w + 1, existsBody (base + off) (base + off + 1) w⟩ ∧
    ruleAtM c.target.rules (base + off + 1) = some ⟨w + 1,
      argumentCandidateBody (c.address (.expr arity a))
        (c.address (.args arity callee actuals (stage + 1)) + primarySlot failure) cw w⟩ := by
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  cases failure with
  | false =>
    constructor
    · have h := c.at (.args arity callee actuals stage) hn 10 (by unfold compilerSlotSize; omega)
      simpa [fragments, argumentFragments, compilerFragmentAt, hr, ha, ht, hget, CompilerConfig.address] using h
    · have h := c.at (.args arity callee actuals stage) hn 11 (by unfold compilerSlotSize; omega)
      simpa [fragments, argumentFragments, compilerFragmentAt, hr, ha, ht, hget,
        primarySlot, CompilerConfig.address, Nat.add_assoc] using h
  | true =>
    constructor
    · have h := c.at (.args arity callee actuals stage) hn 20 (by unfold compilerSlotSize; omega)
      simpa [fragments, argumentFragments, compilerFragmentAt, hr, ha, ht, hget, CompilerConfig.address] using h
    · have h := c.at (.args arity callee actuals stage) hn 21 (by unfold compilerSlotSize; omega)
      simpa [fragments, argumentFragments, compilerFragmentAt, hr, ha, ht, hget,
        primarySlot, CompilerConfig.address, Nat.add_assoc] using h

private theorem complement_exists (n : Nat) (A : Res) (F : Nat → Res) (v : Option Nat) :
    (∃ k, 0 ≤ k ∧ k ≤ n ∧ A = some (some (n - k)) ∧ F (n - k) = some v) ↔
      ∃ j, j ≤ n ∧ A = some (some j) ∧ F j = some v := by
  constructor
  · rintro ⟨k, _, _, hA, hF⟩
    exact ⟨n - k, by omega, hA, hF⟩
  · rintro ⟨j, hj, hA, hF⟩
    have hBack : n - (n - j) = j := by omega
    exact ⟨n - j, by omega, by omega, by simpa only [hBack] using hA, by simpa only [hBack] using hF⟩

theorem compiledArguments_step (c : CompilerConfig) (hg : c.source.FirstOrder)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E C : CapturedEnv)
    (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hfo : a.FirstOrder)
    (hn : .args E.length callee actuals stage ∈ c.nodes)
    (hArg : ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ExprCorrect c x ds E a p q)
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (hNext : ∀ j, j ≤ p → ArgsCorrect c x ds E (C ++ [(p, j)]) callee actuals (stage + 1) j q) :
    ArgsCorrect c x ds E C callee actuals stage p q := by
  let base := c.address (.args E.length callee actuals stage)
  let state := statePositions x.length ds (E ++ C) p q
  let A := sourceResult c x ds E a p
  let F := fun j => argumentResult c x ds E (C ++ [(p, j)]) callee (actuals.drop (stage + 1)) j
  have hState : state.length = 3 + c.digits + 2 * E.length + 2 * stage := by
    simp only [state, statePositions, List.length_cons, List.length_append, envPositions_length, hd, hc]; omega
  have hEach : ∀ (failure : Bool) k, k ≤ x.length → Predicate c.target .callByValuePar
      (.call (base + (if failure then 20 else 10) + 1) (.lit (x.take k) :: prefixValues x state)) x
      (A = some (some (x.length - k)) ∧ F (x.length - k) = some (if failure then none else some q)) := by
    intro failure k hk
    have hBack : x.length - (x.length - k) = k := by omega
    have hLeft := (hArg p hp (x.length - k) (by omega)).1
    have hContinuation : A = some (some (x.length - k)) → Predicate c.target .callByValuePar
        (c.argumentCall E.length callee actuals (stage + 1) failure
          (stageValues x ds E (C ++ [(p, x.length - k)]) (x.length - k) q)) x
        (F (x.length - k) = some (if failure then none else some q)) := by
      intro hSuccess
      have hjp : x.length - k ≤ p := evaluatedCapture_le hg (by decide) hfo (decodeEnv x E)
        (CBVtoCBN.clockValue x.length ds) hp hSuccess
      cases failure
      · exact (hNext (x.length - k) hjp).1
      · exact (hNext (x.length - k) hjp).2
    have ht := hLeft.guarded hContinuation
    have hRules := compiledArgument_rules c E.length callee actuals stage hr ha hget hn failure
    dsimp only at hRules
    have hv := prefixValues_args c.target x (k :: state)
    apply predicate_call hRules.2 (by simp only [prefixValues_length, List.length_cons, hState]) hv
    change Predicate c.target .callByValuePar
      (MExp.subst (.lit (x.take k) :: stageValues x ds E C p q)
        (argumentCandidateBody (c.address (.expr E.length a))
          (c.address (.args E.length callee actuals (stage + 1)) + primarySlot failure)
          (3 + c.digits + 2 * E.length) (3 + c.digits + 2 * E.length + 2 * stage))) x _
    have hSub := argumentCandidate_state_subst c x ds hd E C stage hc
      (c.address (.expr E.length a)) (c.address (.args E.length callee actuals (stage + 1)) + primarySlot failure)
      p q (x.length - k)
    rw [hBack] at hSub
    rw [hSub]
    simpa only [CompilerConfig.exprCall, CompilerConfig.argumentCall, primarySlot, Bool.false_eq_true,
      if_false, Nat.add_zero] using ht
  have hExists : ∀ failure : Bool, Predicate c.target .callByValuePar
      (.call (base + (if failure then 20 else 10)) (.lit [] :: stageValues x ds E C p q)) x
      (∃ j, j ≤ x.length ∧ A = some (some j) ∧ F j = some (if failure then none else some q)) := by
    intro failure
    have hRules := compiledArgument_rules c E.length callee actuals stage hr ha hget hn failure
    dsimp only at hRules
    have hLookup : ruleAtM c.target.rules (base + (if failure then 20 else 10)) =
        some ⟨state.length + 1, existsBody (base + (if failure then 20 else 10))
          (base + (if failure then 20 else 10) + 1) state.length⟩ := by rw [hState]; exact hRules.1
    have ht := exists_predicate state hLookup x
      (fun k => A = some (some (x.length - k)) ∧ F (x.length - k) = some (if failure then none else some q))
      (hEach failure) 0 (by omega)
    exact ht.congr (complement_exists x.length A F _)
  have hBound : OkR x.length A := sourceResult_ok c x ds E a p hp
  have hSuccess := (hExists false).congr (seqResult_success x.length A F hBound q).symm
  have hFailure := ((hArg p hp q hq).2.alt (hExists true)).congr (seqResult_failure x.length A F hBound).symm
  have hDrop : actuals.drop stage = a :: actuals.drop (stage + 1) := by
    rw [List.drop_eq_getElem?_toList_append, hget]; rfl
  have hResult : argumentResult c x ds E C callee (actuals.drop stage) p = seqResult A F := by
    rw [hDrop, argumentResult_cons]
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  have hAll := stageValues_subst_all c x ds hd E C stage hc p q
  constructor
  · change Predicate c.target .callByValuePar (c.argumentCall E.length callee actuals stage false (stageValues x ds E C p q)) x _
    rw [hResult, c.argument_unfold x ds hd E C callee actuals stage hc hn p q false]
    simp [argumentRule, argumentFragments, compilerFragmentAt, hr, ha, ht, hget,
      primarySlot, MExp.subst, MExp.substArgs, hAll]
    exact hSuccess
  · change Predicate c.target .callByValuePar (c.argumentCall E.length callee actuals stage true (stageValues x ds E C p q)) x _
    rw [hResult, c.argument_unfold x ds hd E C callee actuals stage hc hn p q true]
    simp [argumentRule, argumentFragments, compilerFragmentAt, hr, ha, ht, hget,
      primarySlot, MExp.subst, MExp.substArgs, hAll]
    rw [stageValues_subst_caller c x ds hd E C p q]
    exact hFailure

theorem compiledArguments_done (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (hc : C.length = actuals.length)
    (hn : .args E.length callee actuals actuals.length ∈ c.nodes) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (p q : Nat) (hLookup : LookupCorrect c x ds C callee p q) :
    ArgsCorrect c x ds E C callee actuals actuals.length p q := by
  constructor
  · change Predicate c.target .callByValuePar (c.argumentCall E.length callee actuals actuals.length false (stageValues x ds E C p q)) x _
    rw [List.drop_length, argumentResult_nil, c.argument_unfold x ds hd E C callee actuals actuals.length hc hn p q false]
    simp [argumentRule, argumentFragments, compilerFragmentAt, hr, ha, primarySlot, MExp.subst, CBVtoCBN.substArgs_append]
    rw [← CBVtoCBN.substArgs_append, stageValues_subst_finish c x ds hd E C actuals.length hc p q]
    exact hLookup.1
  · change Predicate c.target .callByValuePar (c.argumentCall E.length callee actuals actuals.length true (stageValues x ds E C p q)) x _
    rw [List.drop_length, argumentResult_nil, c.argument_unfold x ds hd E C callee actuals actuals.length hc hn p q true]
    simp [argumentRule, argumentFragments, compilerFragmentAt, hr, ha, primarySlot, MExp.subst, CBVtoCBN.substArgs_append]
    rw [← CBVtoCBN.substArgs_append, stageValues_subst_finish c x ds hd E C actuals.length hc p q]
    exact hLookup.2

/-- All real capture stages follow from proper-argument correctness and
the table lookup at the current clock. Capture validity is maintained by
the source suffix invariant, rather than imposed as a new assumption. -/
theorem compiledArguments_correct (c : CompilerConfig) (hg : c.source.FirstOrder)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv)
    (callee : Nat) (actuals : List MExp) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (hfo : MExp.FirstOrderArgs actuals) (hav : StagesAvailable c.nodes E.length callee actuals)
    (hArg : ∀ a ∈ actuals, SyntaxCorrect c x ds E a)
    (hLookup : ∀ C, ValidEnv x.length C → C.length = rule.arity →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → LookupCorrect c x ds C callee p q) :
    ∀ stage C, stage ≤ actuals.length → C.length = stage → ValidEnv x.length C →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ArgsCorrect c x ds E C callee actuals stage p q := by
  have aux : ∀ remaining stage C, stage + remaining = actuals.length → C.length = stage → ValidEnv x.length C →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ArgsCorrect c x ds E C callee actuals stage p q := by
    intro remaining
    induction remaining with
    | zero =>
      intro stage C hlen hc hv p hp q hq
      have heq : stage = actuals.length := by omega
      rw [heq] at hc ⊢
      exact compiledArguments_done c x ds hd E C callee actuals hc (hav _ (by omega)) hr ha p q
        (hLookup C hv (hc.trans ha.symm) p hp q hq)
    | succ remaining ih =>
      intro stage C hlen hc hv p hp q hq
      have hb : stage < actuals.length := by omega
      have hget : actuals[stage]? = some actuals[stage] := List.getElem?_eq_getElem hb
      have hm := List.mem_of_getElem? hget
      have hafo : actuals[stage].FirstOrder := by
        have aux : ∀ es : List MExp, MExp.FirstOrderArgs es → ∀ e ∈ es, e.FirstOrder := by
          intro es
          induction es with
          | nil => intro _ e he; cases he
          | cons e es ih =>
            intro hf a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hf.1
            · exact ih hf.2 a ha
        exact aux actuals hfo _ hm
      apply compiledArguments_step c hg x ds hd E C callee actuals stage hc hr ha hget hafo
        (hav stage (by omega)) (hArg _ hm) p q hp hq
      intro j hj
      apply ih (stage + 1) (C ++ [(p, j)]) (by omega)
      · simp [hc]
      · exact hv.append_capture hp hj
      · omega
      · exact hq
  intro stage C hstage hc hv
  exact aux (actuals.length - stage) stage C (by omega) hc hv

end Shallot.MacroPeg.CBV.ParSimulation
