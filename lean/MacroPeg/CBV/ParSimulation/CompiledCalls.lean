import MacroPeg.CBV.ParSimulation.CompiledArguments

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode ExprAvailable compilerSlotSize compilerFragmentAt)

theorem sourceCall_result (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (callee : Nat) (actuals : List MExp) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length) (p : Nat) :
    sourceResult c x ds E (.call callee actuals) p = argumentResult c x ds E [] callee actuals p := by
  unfold sourceResult argumentResult
  rw [CBVtoCBN.evV_call_finishSeq hr ha]
  simp [decodeEnv]

theorem compiledCall_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp) (hn : .expr E.length (.call callee actuals) ∈ c.nodes)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (p q : Nat) (hArgs : ArgsCorrect c x ds E [] callee actuals 0 p q) :
    ExprCorrect c x ds E (.call callee actuals) p q := by
  have hs := stateValues_subst_all c x ds hd E p q
  have hSource := sourceCall_result c x ds E callee actuals hr ha p
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    rw [hSource]
    simpa only [CompilerConfig.argumentCall, CompilerConfig.address, primarySlot, Bool.false_eq_true, if_false,
      Nat.add_zero, stageValues, List.append_nil, List.drop_zero] using hArgs.1
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    rw [hSource]
    simpa only [CompilerConfig.argumentCall, CompilerConfig.address, primarySlot, Bool.true_eq, if_true,
      stageValues, List.append_nil, List.drop_zero] using hArgs.2

private theorem compiledCall_invalid (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp)
    (hn : .expr E.length (.call callee actuals) ∈ c.nodes) (p q : Nat)
    (hSource : sourceResult c x ds E (.call callee actuals) p = some none)
    (hStage : ∀ failure, ruleAtM c.target.rules
      (c.address (.args E.length callee actuals 0) + primarySlot failure) =
      some ⟨3 + c.digits + 2 * E.length, if failure then .eps else MExp.failAlways⟩) :
    ExprCorrect c x ds E (.call callee actuals) p q := by
  have hs := stateValues_subst_all c x ds hd E p q
  have hv := prefixValues_args c.target x (statePositions x.length ds E p q)
  change DerivesArgsPar c.target .callByValuePar x (stateValues x ds E p q) (stateValues x ds E p q) at hv
  have hArgs : (stateValues x ds E p q).length = 3 + c.digits + 2 * E.length := by rw [stateValues_length, hd]
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    apply predicate_call (hStage false) hArgs.symm hv
    constructor
    · intro h
      rw [hSource] at h
      cases h
    · intro _
      exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, MExp.subst, hs]
    apply predicate_call (hStage true) hArgs.symm hv
    constructor
    · intro _
      exact ⟨_, .eps x, rfl⟩
    · intro h
      exact False.elim (h hSource)

theorem compiledCall_missing (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp)
    (hav : ExprAvailable c.nodes E.length (.call callee actuals))
    (hr : ruleAtM c.source.rules callee = none) (p q : Nat) :
    ExprCorrect c x ds E (.call callee actuals) p q := by
  apply compiledCall_invalid c x ds hd E callee actuals hav.self p q (by simp [sourceResult, evV, hr])
  intro failure
  have h := c.at (.args E.length callee actuals 0) (hav.call.2 0 (by omega)) (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  cases failure <;> simpa [fragments, argumentFragments, compilerFragmentAt, hr, primarySlot] using h

theorem compiledCall_badArity (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp)
    (hav : ExprAvailable c.nodes E.length (.call callee actuals)) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity ≠ actuals.length) (p q : Nat) :
    ExprCorrect c x ds E (.call callee actuals) p q := by
  apply compiledCall_invalid c x ds hd E callee actuals hav.self p q (by simp [sourceResult, evV, hr, ha])
  intro failure
  have h := c.at (.args E.length callee actuals 0) (hav.call.2 0 (by omega)) (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  cases failure <;> simpa [fragments, argumentFragments, compilerFragmentAt, hr, ha, primarySlot] using h

end Shallot.MacroPeg.CBV.ParSimulation
