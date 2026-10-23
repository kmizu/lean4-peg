import MacroPeg.CBV.ParSimulation.CompilerAdapters

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode compilerSlotSize compilerFragmentAt ExprAvailable)

theorem compiledAlt_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a b : MExp) (hn : .expr E.length (.alt a b) ∈ c.nodes) (p q : Nat)
    (ha : ExprCorrect c x ds E a p q) (hb : ExprCorrect c x ds E b p q) :
    ExprCorrect c x ds E (.alt a b) p q := by
  have hs := stateValues_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    exact alternative_success ha.1 ha.2 hb.1
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    exact alternative_failure ha.2 hb.2

theorem compiledStar_rules (c : CompilerConfig) (arity : Nat) (a : MExp)
    (hn : .expr arity (.star a) ∈ c.nodes) :
    let base := c.address (.expr arity (.star a))
    let w := 3 + c.digits + 2 * arity
    let rest := w - 2
    ruleAtM c.target.rules (base + 10) =
      some ⟨w, repetitionBody 0 (c.address (.expr arity a) + 2) (base + 11) rest⟩ ∧
    ruleAtM c.target.rules (base + 11) = some ⟨w + 1, existsBody (base + 11) (base + 12) w⟩ ∧
    ruleAtM c.target.rules (base + 12) =
      some ⟨w + 1, repetitionCandidateBody 1 (c.address (.expr arity a)) (base + 10) rest⟩ := by
  constructor
  · have h := c.at (.expr arity (.star a)) hn 10 (by unfold compilerSlotSize; omega)
    simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h
  · constructor
    · have h := c.at (.expr arity (.star a)) hn 11 (by unfold compilerSlotSize; omega)
      simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h
    · have h := c.at (.expr arity (.star a)) hn 12 (by unfold compilerSlotSize; omega)
      simpa [fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using h

/-- Repetition's actual emitted rules preserve source success, explicit
failure, and the distinction between bottom and a failed source operand. -/
theorem compiledStar_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : MExp) (hav : ExprAvailable c.nodes E.length (.star a))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (h : ∀ i, i ≤ x.length → ∀ j, j ≤ x.length → ExprCorrect c x ds E a i j) :
    ExprCorrect c x ds E (.star a) p q := by
  let rest := restPositions x.length ds E
  let w := 3 + c.digits + 2 * E.length
  have hRest : rest.length = w - 2 := by rw [restPositions_length, hd]; dsimp only [w]; omega
  have hW : rest.length + 2 = w := by rw [hRest]; dsimp only [w]; omega
  have hW' : rest.length + 3 = w + 1 := by omega
  have hRules := compiledStar_rules c E.length a hav.self
  dsimp only at hRules
  obtain ⟨h0, h1, h2⟩ := hRules
  have h0' : ruleAtM c.target.rules (c.address (.expr E.length (.star a)) + 10) =
      some ⟨rest.length + 2, repetitionBody 0 (c.address (.expr E.length a) + 2)
        (c.address (.expr E.length (.star a)) + 11) rest.length⟩ := by
    rw [hW, hRest]
    exact h0
  have h1' : ruleAtM c.target.rules (c.address (.expr E.length (.star a)) + 11) =
      some ⟨rest.length + 3, existsBody (c.address (.expr E.length (.star a)) + 11)
        (c.address (.expr E.length (.star a)) + 12) (rest.length + 2)⟩ := by
    rw [hW, hW']
    exact h1
  have h2' : ruleAtM c.target.rules (c.address (.expr E.length (.star a)) + 12) =
      some ⟨rest.length + 3, repetitionCandidateBody 1 (c.address (.expr E.length a))
        (c.address (.expr E.length (.star a)) + 10) rest.length⟩ := by
    rw [hW', hRest]
    exact h2
  have hS : ∀ i, i ≤ x.length → ∀ j, j ≤ x.length → Predicate c.target .callByValuePar
      (.call (c.address (.expr E.length a))
        (.lit (x.take (x.length - i)) :: .lit (x.take (x.length - j)) :: prefixValues x rest)) x
      (sourceResult c x ds E a i = some (some j)) := by
    intro i hi j hj
    simpa only [CompilerConfig.exprCall, primarySlot, Bool.false_eq_true, if_false, Nat.add_zero,
      stateValues, statePositions, rest, restPositions, prefixValues] using (h i hi j hj).1
  have hF : ∀ i, i ≤ x.length → Predicate c.target .callByValuePar
      (.call (c.address (.expr E.length a) + 2) (.lit (x.take (x.length - i)) :: prefixValues x rest)) x
      (sourceResult c x ds E a i = some none) := by
    intro i hi
    exact compiledFailureAdapter_test c x ds hd E a hav.star.self i (h i hi x.length (by omega))
  have ht := repetition_test rest h0' h1' h2' c.order_rule c.equal_rule x
    (fun i => sourceResult c x ds E a i) hS hF p q hp hq
  have hs := stateValues_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hav.self x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    exact ht
  · rw [c.expr_unfold hav.self x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, MExp.failAlways]
    exact repetition_failure_test c.target x (fun i => sourceResult c x ds E a i) p

theorem notCandidateBody_subst (success : Nat) (j p : MExp) (ctx : List MExp) :
    MExp.subst (j :: p :: ctx) (notCandidateBody success ctx.length) =
      .call success (p :: j :: ctx) := by
  simp [notCandidateBody, MExp.subst, MExp.substArgs, argAt,
    CBVtoCBN.subst_paramsFrom_cons, CBVtoCBN.subst_paramsFrom]

theorem compiledNot_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : MExp) (hn : .expr E.length (.notP a) ∈ c.nodes)
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (h : ∀ j, j ≤ x.length → ExprCorrect c x ds E a p j) :
    ExprCorrect c x ds E (.notP a) p q := by
  let rest := restPositions x.length ds E
  let ctx := (x.length - p) :: rest
  let base := c.address (.expr E.length (.notP a))
  let w := 3 + c.digits + 2 * E.length
  have hRest : rest.length = w - 2 := by rw [restPositions_length, hd]; dsimp only [w]; omega
  have hCtx : ctx.length = w - 1 := by simp only [ctx, List.length_cons]; dsimp only [w] at *; omega
  have hSearch : ruleAtM c.target.rules (base + 10) =
      some ⟨ctx.length + 1, existsBody (base + 10) (base + 11) ctx.length⟩ := by
    have hr := c.at (.expr E.length (.notP a)) hn 10 (by unfold compilerSlotSize; omega)
    have hw : ctx.length + 1 = w := by rw [hCtx]; dsimp only [w]; omega
    rw [hw, hCtx]
    simpa [base, w, fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using hr
  have hCandidate : ruleAtM c.target.rules (base + 11) =
      some ⟨w, notCandidateBody (c.address (.expr E.length a)) rest.length⟩ := by
    have hr := c.at (.expr E.length (.notP a)) hn 11 (by unfold compilerSlotSize; omega)
    rw [hRest]
    simpa [base, w, fragments, expressionFragments, compilerFragmentAt, CompilerConfig.address] using hr
  have hEach : ∀ k, k ≤ x.length → Predicate c.target .callByValuePar
      (.call (base + 11) (.lit (x.take k) :: prefixValues x ctx)) x
      (sourceResult c x ds E a p = some (some (x.length - k))) := by
    intro k hk
    have hBack : x.length - (x.length - k) = k := by omega
    have hSource := (h (x.length - k) (by omega)).1
    have hArgs := prefixValues_args c.target x (k :: ctx)
    apply predicate_call hCandidate (by simp only [prefixValues_length, List.length_cons, hCtx]; dsimp only [w]; omega) hArgs
    change Predicate c.target .callByValuePar
      (MExp.subst (.lit (x.take k) :: .lit (x.take (x.length - p)) :: prefixValues x rest)
        (notCandidateBody (c.address (.expr E.length a)) rest.length)) x _
    rw [show rest.length = (prefixValues x rest).length by simp, notCandidateBody_subst]
    simpa only [CompilerConfig.exprCall, primarySlot, Bool.false_eq_true, if_false, Nat.add_zero,
      stateValues, statePositions, rest, restPositions, prefixValues, hBack] using hSource
  have hExists := exists_predicate ctx hSearch x
    (fun k => sourceResult c x ds E a p = some (some (x.length - k))) hEach 0 (by omega)
  have hSpec : (∃ k, 0 ≤ k ∧ k ≤ x.length ∧ sourceResult c x ds E a p = some (some (x.length - k))) ↔
      ∃ j, j ≤ x.length ∧ sourceResult c x ds E a p = some (some j) := by
    constructor
    · rintro ⟨k, _, _, he⟩
      exact ⟨x.length - k, by omega, he⟩
    · rintro ⟨j, hj, he⟩
      refine ⟨x.length - j, by omega, by omega, ?_⟩
      have hBack : x.length - (x.length - j) = j := by omega
      simpa only [hBack] using he
  have ht := (hExists.congr hSpec).congr
    (CBVtoCBN.notResult_failure x.length p (sourceResult c x ds E a p)
      (sourceResult_ok c x ds E a p hp)).symm
  have hs := stateValues_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, MExp.substArgs, hs]
    have hEqual := (Predicate.of_obs (equal_obs c.equal_rule x (x.length - p) (x.length - q)
      (by omega) (by omega))).congr (show x.length - p = x.length - q ↔ p = q by omega)
    exact negation_success hEqual (h q hq).2
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, MExp.substArgs]
    have hArgs : MExp.substArgs (stateValues x ds E p q)
        (CBVtoCBN.paramsFrom 2 (w - 2)) = prefixValues x rest := by
      change MExp.substArgs (.lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: prefixValues x rest)
        (CBVtoCBN.paramsFrom 2 (w - 2)) = _
      rw [← hRest, show rest.length = (prefixValues x rest).length by simp]
      rw [CBVtoCBN.subst_paramsFrom_cons, CBVtoCBN.subst_paramsFrom_cons, CBVtoCBN.subst_paramsFrom]
    rw [hArgs]
    exact ht

end Shallot.MacroPeg.CBV.ParSimulation
