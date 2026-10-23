import MacroPeg.CBVtoCBN.CompilerState

namespace Shallot.MacroPeg.CBVtoCBN

def primarySlot (failure : Bool) : Nat := if failure then 1 else 0

def expressionRule (source : MGrammar) (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) (failure : Bool) : MRule :=
  compilerFragmentAt (compilerExpressionFragments source nodes digits base arity e) (primarySlot failure)

theorem expressionRule_arity (source : MGrammar) (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) (failure : Bool) :
    (expressionRule source nodes digits base arity e failure).arity = 5 + 2 * digits + 4 * arity := by
  cases failure <;> cases e <;>
    simp only [expressionRule, primarySlot, compilerExpressionFragments, primaryRule]
  all_goals first
    | rfl
    | split <;> first | rfl | (split <;> rfl)

theorem evalArgs_subst_all (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (p q : Nat) :
    MExp.substArgs (evalArgs x ds E p q) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)) = evalArgs x ds E p q := by
  have hlen := evalArgs_length x ds E p q
  rw [hd] at hlen
  rw [← hlen]
  exact subst_paramsFrom _

/-- Unfolding an actual generated primary predicate discharges its address and arity obligations. -/
theorem CompilerConfig.expr_unfold (c : CompilerConfig) {arity : Nat} {e : MExp}
    (hn : .expr arity e ∈ c.nodes) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (he : E.length = arity) (p q : Nat) (failure : Bool) (P : Prop) :
    RootTest c.target (c.exprCall arity e failure (evalArgs x ds E p q)) x P ↔
      RootTest c.target (MExp.subst (evalArgs x ds E p q)
        (expressionRule c.source c.nodes c.digits (c.address (.expr arity e)) arity e failure).body) x P := by
  have hslot : primarySlot failure < compilerSlotSize c.digits := by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega
  have hr := c.at (.expr arity e) hn (primarySlot failure) hslot
  change ruleAtM c.target.rules (c.address (.expr arity e) + primarySlot failure) =
    some (expressionRule c.source c.nodes c.digits (c.address (.expr arity e)) arity e failure) at hr
  exact rootTest_call_iff hr (by rw [expressionRule_arity, evalArgs_length, hd, he]) x P

theorem Atom.subst (args : List MExp) (a : Atom) : MExp.subst args a.exp = a.exp := by cases a <;> rfl

theorem expressionRule_atom (source : MGrammar) (nodes : List CompileNode) (digits base arity : Nat)
    (a : Atom) (failure : Bool) :
    expressionRule source nodes digits base arity a.exp failure =
      ⟨5 + 2 * digits + 4 * arity, if failure then (compilerAtomBodies a).2 else (compilerAtomBodies a).1⟩ := by
  cases a <;> cases failure <;> rfl

/-- Every terminal case of the candidate's actual code agrees with the bounded source evaluation. -/
theorem compiledAtom_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : Atom) (hn : .expr E.length a.exp ∈ c.nodes)
    (p q : Nat) (hp : p ≤ x.length) : ExprCorrect c x ds E a.exp p q := by
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false, expressionRule_atom]
    have hsub : MExp.subst (evalArgs x ds E p q) (compilerAtomBodies a).1 =
        terminalSuccessP (skipN (x.length - p)) (skipN q) a.exp := by
      simp [compilerAtomBodies, terminalSuccessP, exactLengthP, andP, MExp.subst, evalArgs, argAt, Atom.subst]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (compilerAtomBodies a).1) x _
    rw [hsub]
    exact atomSuccess_test _ _ _ _ _ _ a p q hp
  · rw [c.expr_unfold hn x ds hd E rfl p q true, expressionRule_atom]
    have hsub : MExp.subst (evalArgs x ds E p q) (compilerAtomBodies a).2 =
        terminalFailureP (skipN (x.length - p)) a.exp := by
      simp [compilerAtomBodies, terminalFailureP, andP, MExp.subst, evalArgs, argAt, Atom.subst]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (compilerAtomBodies a).2) x _
    rw [hsub]
    exact atomFailure_test _ _ _ _ _ _ a p hp

/-- Alternative predicates of two compiled operands combine without merging unknown with source failure. -/
theorem compiledAlt_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a b : MExp) (hn : .expr E.length (.alt a b) ∈ c.nodes) (p q : Nat)
    (ha : ExprCorrect c x ds E a p q) (hb : ExprCorrect c x ds E b p q) :
    ExprCorrect c x ds E (.alt a b) p q := by
  have hs := evalArgs_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (altSuccessP
      (.call (c.address (.expr E.length a)) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)))
      (.call (c.address (.expr E.length a) + 1) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)))
      (.call (c.address (.expr E.length b)) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length))))) x _
    simp only [altSuccessP, MExp.subst, hs]
    exact altSuccess_test ha.1 ha.2 hb.1
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (.seq
      (.call (c.address (.expr E.length a) + 1) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)))
      (.call (c.address (.expr E.length b) + 1) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length))))) x _
    simp only [MExp.subst, hs]
    exact altFailure_test ha.2 hb.2

end Shallot.MacroPeg.CBVtoCBN
