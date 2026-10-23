import MacroPeg.CBV.ParSimulation.Compiler

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters
open CBVtoCBN (CompileNode CompileFragments compilerFragmentAt compilerFailRule
  paramsFrom_firstOrder emptyInputP_firstOrder)

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

@[local simp] private theorem foArgs_replicate (e : MExp) (he : e.FirstOrder) (n : Nat) :
    MExp.FirstOrderArgs (List.replicate n e) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨he, ih⟩

@[local simp] private theorem rulesFO_clock (entry equal next onZero digits ctxSize : Nat) :
    RulesFO (clockBlock entry equal next onZero digits ctxSize) := clockBlock_firstOrder _ _ _ _ _ _

attribute [local simp] MExp.FirstOrder MExp.FirstOrderArgs paramsFrom_firstOrder
attribute [local simp] failureAdapter terminalSuccess terminalFailure parameterSuccess
attribute [local simp] parameterFailure endpoint atPosition MExp.andP MExp.failAlways CBVtoCBN.Atom.exp
attribute [local simp] existsBody_firstOrder sequenceTestBody_firstOrder sequenceFailureTestBody_firstOrder
attribute [local simp] repetitionBody_firstOrder repetitionCandidateBody_firstOrder
attribute [local simp] parameterCandidateBody_firstOrder

@[local simp] private theorem rulesFO_parameter (entry order matcher : Nat) :
    RulesFO (parameterFailureRules entry order matcher) := by simp [parameterFailureRules]

private theorem expressionFragments_fo (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) : FragmentsFO (expressionFragments nodes digits base arity e) := by
  cases e with
  | param k => by_cases hk : k < arity <;> simp [expressionFragments, hk]
  | notP a => simp [expressionFragments, notCandidateBody]
  | eps | any | chr _ | range _ _ | lit _ | alt _ _ | seq _ _ | star _ | call _ _
    | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ => simp [expressionFragments]

private theorem argumentFragments_fo (source : MGrammar) (nodes : List CompileNode)
    (digits base arity callee : Nat) (actuals : List MExp) (stage : Nat) :
    FragmentsFO (argumentFragments source nodes digits base arity callee actuals stage) := by
  cases hr : ruleAtM source.rules callee with
  | none => simp [argumentFragments, hr]
  | some rule =>
    by_cases ha : rule.arity = actuals.length
    · by_cases ht : stage = actuals.length
      · simp [argumentFragments, hr, ha, ht]
      · cases he : actuals[stage]? <;>
          simp [argumentFragments, hr, ha, ht, he, argumentCandidateBody]
    · simp [argumentFragments, hr, ha]

private theorem lookupFragments_fo (source : MGrammar) (nodes : List CompileNode) (digits base callee : Nat) :
    FragmentsFO (lookupFragments source nodes digits base callee) := by
  cases hr : ruleAtM source.rules callee <;> simp [lookupFragments, hr]

private theorem fragments_fo (source : MGrammar) (nodes : List CompileNode)
    (digits base : Nat) (node : CompileNode) : FragmentsFO (fragments source nodes digits base node) := by
  cases node with
  | expr a e => exact expressionFragments_fo _ _ _ _ _
  | args a i as t => exact argumentFragments_fo _ _ _ _ _ _ _ _
  | lookup i => exact lookupFragments_fo _ _ _ _ _

private theorem fragmentAt_fo (fs : CompileFragments) (hf : FragmentsFO fs) (slot : Nat) :
    (compilerFragmentAt fs slot).body.FirstOrder := by
  induction fs with
  | nil => trivial
  | cons f fs ih =>
    rcases f with ⟨offset, rules⟩
    simp only [compilerFragmentAt]
    split
    · cases he : rules[slot - offset]? with
      | none => trivial
      | some rule => exact hf (offset, rules) (by simp) rule (List.mem_of_getElem? he)
    · exact ih (fun f hmem => hf f (List.mem_cons_of_mem _ hmem))

/-- The executable candidate always generates a first-order Par grammar.
This is a syntactic theorem, independent of the pending language theorem. -/
theorem compileCandidate_firstOrder (source : MGrammar) (start : MExp)
    (alphabet : List Char) (digits : Nat) : (compileCandidate source start alphabet digits).FirstOrder := by
  intro rule hr
  simp only [compileCandidate] at hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [frontRules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact equalBody_firstOrder 0
    · exact leBody_firstOrder 1 0
    · exact intervalBody_firstOrder 2 0 alphabet
    · exact ⟨emptyInputP_firstOrder _ _ _, ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩⟩
    · exact ⟨trivial, trivial, trivial, foArgs_replicate (.param 0) trivial _⟩
    all_goals trivial
  · simp only [generatedRules, nodeRules] at hr
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hr
    obtain ⟨slot, _, he⟩ := List.mem_map.mp hi
    subst rule
    exact fragmentAt_fo _ (fragments_fo _ _ _ _ _) slot

end Shallot.MacroPeg.CBV.ParSimulation
