import MacroPeg.CBV.ParSimulation.CompiledControl

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode ExprAvailable compilerSlotSize compilerFragmentAt seqResult_success seqResult_failure)

theorem compiledSequence_rules (c : CompilerConfig) (arity : Nat) (a b : MExp)
    (hn : .expr arity (.seq a b) ∈ c.nodes) :
    let base := c.address (.expr arity (.seq a b))
    let w := 3 + c.digits + 2 * arity
    let rest := w - 2
    ruleAtM c.target.rules (base + 10) = some ⟨w + 1, existsBody (base + 10) (base + 11) w⟩ ∧
    ruleAtM c.target.rules (base + 11) =
      some ⟨w + 1, sequenceTestBody (c.address (.expr arity a)) (c.address (.expr arity b)) rest⟩ ∧
    ruleAtM c.target.rules (base + 20) = some ⟨w, existsBody (base + 20) (base + 21) (w - 1)⟩ ∧
    ruleAtM c.target.rules (base + 21) =
      some ⟨w, sequenceFailureTestBody (c.address (.expr arity a)) (c.address (.expr arity b) + 2) rest⟩ := by
  constructor
  · have h := c.at (.expr arity (.seq a b)) hn 10 (by unfold compilerSlotSize; omega)
    simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h
  · constructor
    · have h := c.at (.expr arity (.seq a b)) hn 11 (by unfold compilerSlotSize; omega)
      simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h
    · constructor
      · have h := c.at (.expr arity (.seq a b)) hn 20 (by unfold compilerSlotSize; omega)
        simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h
      · have h := c.at (.expr arity (.seq a b)) hn 21 (by unfold compilerSlotSize; omega)
        simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h

theorem compiledSequence_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a b : MExp) (hav : ExprAvailable c.nodes E.length (.seq a b))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (hL : ∀ j, j ≤ x.length → ExprCorrect c x ds E a p j)
    (hR : ∀ i, i ≤ x.length → ∀ j, j ≤ x.length → ExprCorrect c x ds E b i j) :
    ExprCorrect c x ds E (.seq a b) p q := by
  let rest := restPositions x.length ds E
  let base := c.address (.expr E.length (.seq a b))
  let w := 3 + c.digits + 2 * E.length
  let successCtx := (x.length - p) :: (x.length - q) :: rest
  let failureCtx := (x.length - p) :: rest
  have hRest : rest.length = w - 2 := by rw [restPositions_length, hd]; dsimp only [w]; omega
  have hSuccessLen : successCtx.length = w := by simp only [successCtx, List.length_cons]; dsimp only [w] at *; omega
  have hFailureLen : failureCtx.length = w - 1 := by simp only [failureCtx, List.length_cons]; dsimp only [w] at *; omega
  obtain ⟨hSearchS, hCandidateS, hSearchF, hCandidateF⟩ := compiledSequence_rules c E.length a b hav.self
  have hSearchS' : ruleAtM c.target.rules (base + 10) =
      some ⟨successCtx.length + 1, existsBody (base + 10) (base + 11) successCtx.length⟩ := by
    rw [hSuccessLen]; exact hSearchS
  have hSearchF' : ruleAtM c.target.rules (base + 20) =
      some ⟨failureCtx.length + 1, existsBody (base + 20) (base + 21) failureCtx.length⟩ := by
    have hw : failureCtx.length + 1 = w := by rw [hFailureLen]; dsimp only [w]; omega
    rw [hw, hFailureLen]; exact hSearchF
  have hEachS : ∀ k, k ≤ x.length → Predicate c.target .callByValuePar
      (.call (base + 11) (.lit (x.take k) :: prefixValues x successCtx)) x
      (sourceResult c x ds E a p = some (some (x.length - k)) ∧
        sourceResult c x ds E b (x.length - k) = some (some q)) := by
    intro k hk
    have hLeft := (hL (x.length - k) (by omega)).1
    have hRight := (hR (x.length - k) (by omega) q hq).1
    have hBack : x.length - (x.length - k) = k := by omega
    have hv := prefixValues_args c.target x (k :: successCtx)
    apply predicate_call hCandidateS (by simp only [prefixValues_length, List.length_cons, hSuccessLen]; rfl) hv
    change Predicate c.target .callByValuePar
      (MExp.subst (.lit (x.take k) :: .lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: prefixValues x rest)
        (sequenceTestBody (c.address (.expr E.length a)) (c.address (.expr E.length b)) (w - 2))) x _
    rw [← hRest, show rest.length = (prefixValues x rest).length by simp, sequenceTestBody_subst]
    simpa only [CompilerConfig.exprCall, primarySlot, Bool.false_eq_true, if_false, Nat.add_zero,
      stateValues, statePositions, rest, restPositions, prefixValues, hBack] using hLeft.seq hRight
  have hEachF : ∀ k, k ≤ x.length → Predicate c.target .callByValuePar
      (.call (base + 21) (.lit (x.take k) :: prefixValues x failureCtx)) x
      (sourceResult c x ds E a p = some (some (x.length - k)) ∧
        sourceResult c x ds E b (x.length - k) = some none) := by
    intro k hk
    have hLeft := (hL (x.length - k) (by omega)).1
    have hRight := compiledFailureAdapter_test c x ds hd E b hav.seq.2.self
      (x.length - k) (hR (x.length - k) (by omega) x.length (by omega))
    have hBack : x.length - (x.length - k) = k := by omega
    have hv := prefixValues_args c.target x (k :: failureCtx)
    apply predicate_call hCandidateF
      (by simp only [prefixValues_length, List.length_cons, hFailureLen]; dsimp only [w]; omega) hv
    change Predicate c.target .callByValuePar
      (MExp.subst (.lit (x.take k) :: .lit (x.take (x.length - p)) :: prefixValues x rest)
        (sequenceFailureTestBody (c.address (.expr E.length a)) (c.address (.expr E.length b) + 2) (w - 2))) x _
    rw [← hRest, show rest.length = (prefixValues x rest).length by simp, sequenceFailureTestBody_subst]
    simpa only [CompilerConfig.exprCall, primarySlot, Bool.false_eq_true, if_false, Nat.add_zero,
      stateValues, statePositions, rest, restPositions, prefixValues, hBack] using hLeft.seq hRight
  have hExistsS := exists_predicate successCtx hSearchS' x
    (fun k => sourceResult c x ds E a p = some (some (x.length - k)) ∧
      sourceResult c x ds E b (x.length - k) = some (some q)) hEachS 0 (by omega)
  have hExistsF := exists_predicate failureCtx hSearchF' x
    (fun k => sourceResult c x ds E a p = some (some (x.length - k)) ∧
      sourceResult c x ds E b (x.length - k) = some none) hEachF 0 (by omega)
  have hRange := sourceResult_ok c x ds E a p hp
  have hS := hExistsS.congr (show
      (∃ k, 0 ≤ k ∧ k ≤ x.length ∧ sourceResult c x ds E a p = some (some (x.length - k)) ∧
        sourceResult c x ds E b (x.length - k) = some (some q)) ↔
      sourceResult c x ds E (.seq a b) p = some (some q) from by
    change _ ↔ CBVtoCBN.seqResult (sourceResult c x ds E a p) (fun j => sourceResult c x ds E b j) = _
    rw [seqResult_success x.length _ _ hRange q]
    constructor
    · rintro ⟨k, _, _, hA, hB⟩
      exact ⟨x.length - k, by omega, hA, hB⟩
    · rintro ⟨j, hj, hA, hB⟩
      have hBack : x.length - (x.length - j) = j := by omega
      exact ⟨x.length - j, by omega, by omega, by simpa only [hBack] using hA, by simpa only [hBack] using hB⟩)
  have hF := ((hL q hq).2.alt hExistsF).congr (show
      (sourceResult c x ds E a p = some none ∨
        ∃ k, 0 ≤ k ∧ k ≤ x.length ∧ sourceResult c x ds E a p = some (some (x.length - k)) ∧
          sourceResult c x ds E b (x.length - k) = some none) ↔
      sourceResult c x ds E (.seq a b) p = some none from by
    change _ ↔ CBVtoCBN.seqResult (sourceResult c x ds E a p) (fun j => sourceResult c x ds E b j) = _
    rw [seqResult_failure x.length _ _ hRange]
    constructor
    · rintro (h | ⟨k, _, _, hA, hB⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x.length - k, by omega, hA, hB⟩
    · rintro (h | ⟨j, hj, hA, hB⟩)
      · exact Or.inl h
      · have hBack : x.length - (x.length - j) = j := by omega
        exact Or.inr ⟨x.length - j, by omega, by omega, by simpa only [hBack] using hA, by simpa only [hBack] using hB⟩)
  have hs := stateValues_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hav.self x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, MExp.substArgs, hs]
    exact hS
  · rw [c.expr_unfold hav.self x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, MExp.substArgs, hs]
    rw [stateValues_subst_rest c x ds hd E p q]
    exact hF

end Shallot.MacroPeg.CBV.ParSimulation
