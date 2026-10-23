import MacroPeg.CBVtoCBN.CompilerPlan

namespace Shallot.MacroPeg.CBVtoCBN

private def RulesFO (rs : List MRule) : Prop := ∀ r ∈ rs, r.body.FirstOrder
private def FragmentsFO (fs : CompileFragments) : Prop := ∀ f ∈ fs, RulesFO f.2

@[local simp] private theorem rulesFO_nil : RulesFO [] := by intro r hr; cases hr
@[local simp] private theorem rulesFO_cons (r : MRule) (rs : List MRule) :
    RulesFO (r :: rs) ↔ r.body.FirstOrder ∧ RulesFO rs := by
  simp only [RulesFO, List.mem_cons, forall_eq_or_imp]

@[local simp] private theorem fragmentsFO_nil : FragmentsFO [] := by intro f hf; cases hf
@[local simp] private theorem fragmentsFO_cons (f : Nat × List MRule) (fs : CompileFragments) :
    FragmentsFO (f :: fs) ↔ RulesFO f.2 ∧ FragmentsFO fs := by
  simp only [FragmentsFO, List.mem_cons, forall_eq_or_imp]

@[local simp] private theorem foArgs_append (a b : List MExp) :
    MExp.FirstOrderArgs (a ++ b) ↔ MExp.FirstOrderArgs a ∧ MExp.FirstOrderArgs b := by
  induction a with
  | nil => simp [MExp.FirstOrderArgs]
  | cons a as ih => simp [MExp.FirstOrderArgs, ih, and_assoc]

@[local simp] private theorem rulesFO_pair (entry test m : Nat) : RulesFO (pairSearchBlock entry test m) :=
  pairSearchBlock_firstOrder _ _ _
@[local simp] private theorem rulesFO_seqOk (entry left right m : Nat) : RulesFO (sequenceSuccessBlock entry left right m) :=
  sequenceSuccessBlock_firstOrder _ _ _ _
@[local simp] private theorem rulesFO_seqFail (entry leftOk leftFail rightFail m : Nat) :
    RulesFO (sequenceFailureBlock entry leftOk leftFail rightFail m) := sequenceFailureBlock_firstOrder _ _ _ _ _
@[local simp] private theorem rulesFO_star (entry success failure m : Nat) : RulesFO (repetitionBlock entry success failure m) :=
  repetitionBlock_firstOrder _ _ _ _
@[local simp] private theorem rulesFO_parameter (entry matcher : Nat) : RulesFO (parameterFailureBlock entry matcher) :=
  parameterFailureBlock_firstOrder _ _
@[local simp] private theorem rulesFO_capture (entry argument next : Nat) (thread : Bool) (m : Nat) :
    RulesFO (captureBlock entry argument next thread m) := captureBlock_firstOrder _ _ _ _ _
@[local simp] private theorem rulesFO_clock (entry next onZero d m : Nat) : RulesFO (clockBlock entry next onZero d m) :=
  clockBlock_firstOrder _ _ _ _ _

attribute [local simp] MExp.FirstOrder MExp.FirstOrderArgs paramsFrom_firstOrder
attribute [local simp] compilerCall primaryRule compilerFailRule compilerFailureAdapter compilerAtomBodies
attribute [local simp] terminalSuccessP terminalFailureP parameterSuccessP lePositionP equalPositionP exactLengthP fitsLengthP
attribute [local simp] altSuccessP andP Atom.exp MExp.failAlways

private theorem compilerExpressionFragments_fo (source : MGrammar) (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) : FragmentsFO (compilerExpressionFragments source nodes digits base arity e) := by
  cases e with
  | eps => simp [compilerExpressionFragments]
  | any => simp [compilerExpressionFragments]
  | chr c => simp [compilerExpressionFragments]
  | range lo hi => simp [compilerExpressionFragments]
  | lit w => simp [compilerExpressionFragments]
  | param k =>
    by_cases hk : k < arity <;> simp [compilerExpressionFragments, hk]
  | alt a b => simp [compilerExpressionFragments]
  | seq a b => simp [compilerExpressionFragments]
  | star a => simp [compilerExpressionFragments]
  | notP a => simp [compilerExpressionFragments]
  | call callee args =>
    cases hr : ruleAtM source.rules callee with
    | none => simp [compilerExpressionFragments, hr]
    | some rule =>
      by_cases ha : rule.arity = args.length <;> simp [compilerExpressionFragments, hr, ha]
  | dbg a => simp [compilerExpressionFragments]
  | lam n a => simp [compilerExpressionFragments]
  | callParam k args => simp [compilerExpressionFragments]
  | invoke n a args => simp [compilerExpressionFragments]

private theorem compilerArgumentFragments_fo (source : MGrammar) (s : Strategy) (nodes : List CompileNode)
    (digits base arity callee : Nat) (actuals : List MExp) (stage : Nat) :
    FragmentsFO (compilerArgumentFragments source s nodes digits base arity callee actuals stage) := by
  cases hr : ruleAtM source.rules callee with
  | none => simp [compilerArgumentFragments, hr]
  | some rule =>
    by_cases ha : rule.arity = actuals.length
    · by_cases ht : stage = actuals.length
      · simp [compilerArgumentFragments, hr, ha, ht]
      · cases he : actuals[stage]? <;> simp [compilerArgumentFragments, hr, ha, ht, he]
    · simp [compilerArgumentFragments, hr, ha]

private theorem compilerLookupFragments_fo (source : MGrammar) (nodes : List CompileNode) (digits base callee : Nat) :
    FragmentsFO (compilerLookupFragments source nodes digits base callee) := by
  cases hr : ruleAtM source.rules callee <;> simp [compilerLookupFragments, hr]

private theorem compilerFragments_fo (source : MGrammar) (s : Strategy) (nodes : List CompileNode)
    (digits base : Nat) (node : CompileNode) :
    FragmentsFO (compilerFragments source s nodes digits base node) := by
  cases node with
  | expr a e => exact compilerExpressionFragments_fo _ _ _ _ _ _
  | args a i as t => exact compilerArgumentFragments_fo _ _ _ _ _ _ _ _ _
  | lookup i => exact compilerLookupFragments_fo _ _ _ _ _

private theorem compilerFragmentAt_fo (fs : CompileFragments) (hf : FragmentsFO fs) (slot : Nat) :
    (compilerFragmentAt fs slot).body.FirstOrder := by
  induction fs with
  | nil => trivial
  | cons f fs ih =>
    rcases f with ⟨offset, rules⟩
    simp only [compilerFragmentAt]
    split
    · cases he : rules[slot - offset]? with
      | none => trivial
      | some rule =>
        exact hf (offset, rules) (by simp) rule (List.mem_of_getElem? he)
    · exact ih (fun f hmem => hf f (List.mem_cons_of_mem _ hmem))

/-- Every generated rule is first-order, for either strategy.
Language preservation for the unrestricted translator is established in `Recognition`. -/
theorem compileCandidate_firstOrder (source : MGrammar) (s : Strategy) (start : MExp)
    (alphabet : List Char) (digits : Nat) : (compileCandidate source s start alphabet digits).FirstOrder := by
  intro rule hr
  simp only [compileCandidate] at hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [compilerFrontRules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact spanEqBody_firstOrder _ _
    · exact ⟨emptyInputP_firstOrder _ _ _, ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩⟩
    · exact findLengthBody_firstOrder _ _
    · exact ⟨trivial, trivial, trivial, trivial, trivial, repeatPair_firstOrder (a := .param 0) (b := .eps) trivial trivial _⟩
  · simp only [compilerGeneratedRules, compilerNodeRules] at hr
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hr
    obtain ⟨slot, _, he⟩ := List.mem_map.mp hi
    subst rule
    exact compilerFragmentAt_fo _ (compilerFragments_fo _ _ _ _ _ _) slot

end Shallot.MacroPeg.CBVtoCBN
