import MacroPeg.CBVtoCBN.ArgumentRules

namespace Shallot.MacroPeg.CBVtoCBN

theorem argumentEval_test (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args E.length callee actuals stage ∈ c.nodes)
    (p q j : Nat) (h : ExprCorrect c x ds E a p j) :
    RootTest c.target (.call (c.address (.args E.length callee actuals stage) + 5)
      (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: stageRest x ds E C q)) x
      (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p = some (some j)) := by
  rw [rootTest_call_iff (compiledArgument_evalRule c E.length callee actuals stage hr ha hget hn)
    (by simp only [List.length_cons, stageRest_length, hd, hc]; omega)]
  have hR : (evalRest x ds E).length = 5 + 2 * c.digits + 4 * E.length - 4 := by rw [evalRest_length, hd]; omega
  change RootTest c.target (.call (c.address (.expr E.length a))
    (MExp.substArgs ([skipN p, skipN (x.length - p), skipN j, skipN (x.length - j), skipN q, skipN (x.length - q)] ++
      (evalRest x ds E ++ envArgs x.length C)) (argumentEvalParams (5 + 2 * c.digits + 4 * E.length - 4)))) x _
  rw [← hR, subst_argumentEvalParams]
  simpa [CompilerConfig.exprCall, evalArgs] using h.1

theorem argumentFailure_test (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args E.length callee actuals stage ∈ c.nodes)
    (p q : Nat) (h : ExprCorrect c x ds E a p q) :
    RootTest c.target (.call (c.address (.args E.length callee actuals stage) + 6) (stageArgs x ds E C p q)) x
      (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p = some none) := by
  rw [rootTest_call_iff (compiledArgument_failRule c E.length callee actuals stage hr ha hget hn)
    (by rw [stageArgs_length, hd, hc])]
  have hlen := evalArgs_length x ds E p q
  rw [hd] at hlen
  change RootTest c.target (.call (c.address (.expr E.length a) + 1)
    (MExp.substArgs (evalArgs x ds E p q ++ envArgs x.length C) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)))) x _
  rw [← hlen, subst_paramsFrom_take]
  simpa [CompilerConfig.exprCall] using h.2

theorem captureNextArgs_stage (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q j : Nat) (thread : Bool) :
    captureNextArgs thread (skipN j) (skipN (x.length - j)) (skipN p) (skipN (x.length - p)) (stageRest x ds E C q) =
      [skipN p, skipN (x.length - p), skipN j, skipN (x.length - j)] ++ stageArgs x ds E C (if thread then j else p) q := by
  cases thread <;> rfl

theorem argumentNext_test (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args E.length callee actuals stage ∈ c.nodes)
    (p q j : Nat) (thread failure : Bool)
    (h : ArgsCorrect c x ds E (C ++ [(p, j)]) callee actuals (stage + 1) (if thread then j else p) q) :
    RootTest c.target (.call (c.address (.args E.length callee actuals stage) + 7 + primarySlot failure)
      (captureNextArgs thread (skipN j) (skipN (x.length - j)) (skipN p) (skipN (x.length - p)) (stageRest x ds E C q))) x
      (argumentResult c x ds E (C ++ [(p, j)]) callee (actuals.drop (stage + 1)) (if thread then j else p) =
        some (if failure then none else some q)) := by
  rw [captureNextArgs_stage]
  have hlen := stageArgs_length x ds E C (if thread then j else p) q
  rw [hd, hc] at hlen
  rw [rootTest_call_iff (compiledArgument_nextRule c E.length callee actuals stage hr ha hget hn failure)
    (by simp only [List.length_append, List.length_cons, List.length_nil, stageArgs_length, hd, hc]; omega)]
  change RootTest c.target (.call (c.address (.args E.length callee actuals (stage + 1)) + primarySlot failure)
    (MExp.substArgs ([skipN p, skipN (x.length - p), skipN j, skipN (x.length - j)] ++
      stageArgs x ds E C (if thread then j else p) q)
      (paramsFrom 4 (5 + 2 * c.digits + 4 * E.length + 4 * stage) ++ paramsFrom 0 4))) x _
  rw [← hlen, subst_captureRotate]
  have hargs : stageArgs x ds E C (if thread then j else p) q ++ [skipN p, skipN (x.length - p), skipN j, skipN (x.length - j)] =
      stageArgs x ds E (C ++ [(p, j)]) (if thread then j else p) q := by
    simp [stageArgs, envArgs_append, envArgs, List.append_assoc]
  rw [hargs]
  cases failure
  · simpa [CompilerConfig.argumentCall, primarySlot, stageArgs] using h.1
  · simpa [CompilerConfig.argumentCall, primarySlot, stageArgs] using h.2

end Shallot.MacroPeg.CBVtoCBN
