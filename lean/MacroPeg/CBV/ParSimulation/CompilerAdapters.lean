import MacroPeg.CBV.ParSimulation.CompiledParameters

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode compilerSlotSize compilerFragmentAt paramsFrom subst_paramsFrom_cons subst_paramsFrom)

theorem predicate_call {g : MGrammar} {i : Nat} {rule : MRule} {args vals : List MExp}
    {x : List Char} {P : Prop}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length)
    (hv : DerivesArgsPar g .callByValuePar x args vals)
    (ht : Predicate g .callByValuePar (MExp.subst vals rule.body) x P) :
    Predicate g .callByValuePar (.call i args) x P :=
  ⟨fun h => par_call hr ha hv (ht.1 h), fun h => par_call hr ha hv (ht.2 h)⟩

def restPositions (n : Nat) (ds : List Nat) (E : CapturedEnv) : List Nat :=
  n :: (ds ++ envPositions n E)

theorem restPositions_length (n : Nat) (ds : List Nat) (E : CapturedEnv) :
    (restPositions n ds E).length = 1 + ds.length + 2 * E.length := by
  simp only [restPositions, List.length_cons, List.length_append, envPositions_length]
  omega

theorem sourceResult_ok (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (E : CapturedEnv) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    OkR x.length (sourceResult c x ds E e p) :=
  evV_ok (tblV_ok c.source x .callByValueSeq _) e p hp

theorem stateValues_subst_all (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (p q : Nat) :
    MExp.substArgs (stateValues x ds E p q) (paramsFrom 0 (3 + c.digits + 2 * E.length)) =
      stateValues x ds E p q := by
  rw [show 3 + c.digits + 2 * E.length = (stateValues x ds E p q).length by rw [stateValues_length, hd]]
  exact subst_paramsFrom _

theorem stateValues_subst_rest (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (p q : Nat) :
    MExp.substArgs (stateValues x ds E p q) (paramsFrom 2 (3 + c.digits + 2 * E.length - 2)) =
      prefixValues x (restPositions x.length ds E) := by
  have hLen : 3 + c.digits + 2 * E.length - 2 =
      (prefixValues x (restPositions x.length ds E)).length := by
    simp only [prefixValues_length, restPositions_length, hd]; omega
  change MExp.substArgs
    (.lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: prefixValues x (restPositions x.length ds E))
    (paramsFrom 2 _) = _
  rw [hLen, subst_paramsFrom_cons, subst_paramsFrom_cons, subst_paramsFrom]

theorem expressionAdapter_rule (nodes : List CompileNode) (digits base arity : Nat) (e : MExp) :
    compilerFragmentAt (expressionFragments nodes digits base arity e) 2 =
      failureAdapter (base + 1) (3 + digits + 2 * arity) := by
  cases e <;> simp only [expressionFragments]
  all_goals first | rfl | (split <;> rfl)

theorem failureAdapter_subst (failure : Nat) (p : MExp) (ctx : List MExp) :
    MExp.subst (p :: ctx) (failureAdapter failure (ctx.length + 2)).body =
      .call failure (p :: .lit [] :: ctx) := by
  simp only [failureAdapter, MExp.subst, MExp.substArgs, argAt, Nat.add_sub_cancel_right]
  rw [subst_paramsFrom_cons, subst_paramsFrom]

theorem compiledFailureAdapter_test (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (e : MExp) (hn : .expr E.length e ∈ c.nodes)
    (p : Nat) (h : ExprCorrect c x ds E e p x.length) :
    Predicate c.target .callByValuePar
      (.call (c.address (.expr E.length e) + 2)
        (prefixValues x ((x.length - p) :: restPositions x.length ds E))) x
      (sourceResult c x ds E e p = some none) := by
  have hr := c.at (.expr E.length e) hn 2 (by unfold compilerSlotSize; omega)
  change ruleAtM c.target.rules (c.address (.expr E.length e) + 2) =
    some (compilerFragmentAt (expressionFragments c.nodes c.digits (c.address (.expr E.length e)) E.length e) 2) at hr
  rw [expressionAdapter_rule] at hr
  have hv := prefixValues_args c.target x ((x.length - p) :: restPositions x.length ds E)
  apply predicate_call hr (by simp [failureAdapter, restPositions_length, hd]; omega) hv
  have hwidth : 3 + c.digits + 2 * E.length =
      (prefixValues x (restPositions x.length ds E)).length + 2 := by
    simp only [prefixValues_length, restPositions_length, hd]; omega
  change Predicate c.target .callByValuePar (MExp.subst
    (.lit (x.take (x.length - p)) :: prefixValues x (restPositions x.length ds E))
    (failureAdapter (c.address (.expr E.length e) + 1) (3 + c.digits + 2 * E.length)).body) x _
  rw [hwidth, failureAdapter_subst]
  simpa only [CompilerConfig.exprCall, primarySlot, if_true, stateValues, statePositions,
    Nat.sub_self, List.take_zero, restPositions, prefixValues] using h.2

end Shallot.MacroPeg.CBV.ParSimulation
