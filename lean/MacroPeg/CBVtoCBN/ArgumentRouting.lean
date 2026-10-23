import MacroPeg.CBVtoCBN.ArgumentSemantics

namespace Shallot.MacroPeg.CBVtoCBN

def argumentEvalParams (rest : Nat) : List MExp :=
  .param 0 :: .param 1 :: .param 2 :: .param 3 :: paramsFrom 6 rest

theorem subst_argumentEvalParams (p ps j js q qs : MExp) (R C : List MExp) :
    MExp.substArgs ([p, ps, j, js, q, qs] ++ (R ++ C)) (argumentEvalParams R.length) = [p, ps, j, js] ++ R := by
  have hR := subst_paramsFrom_slice [p, ps, j, js, q, qs] R C
  simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] at hR
  simp only [argumentEvalParams, MExp.substArgs, MExp.subst, List.cons_append, List.nil_append, argAt]
  rw [hR]

theorem subst_captureRotate (a b c d : MExp) (args : List MExp) :
    MExp.substArgs ([a, b, c, d] ++ args) (paramsFrom 4 args.length ++ paramsFrom 0 4) = args ++ [a, b, c, d] := by
  have hA := subst_paramsFrom_slice [a, b, c, d] args []
  have hS := subst_paramsFrom_take [a, b, c, d] args
  simp only [List.length_cons, List.length_nil, List.append_nil, List.cons_append, List.nil_append] at hA hS
  simp only [substArgs_append, List.cons_append, List.nil_append]
  rw [hA, hS]

theorem subst_dropMiddle (pre middle tail : List MExp) :
    MExp.substArgs (pre ++ (middle ++ tail))
      (paramsFrom 0 pre.length ++ paramsFrom (pre.length + middle.length) tail.length) = pre ++ tail := by
  have hP := subst_paramsFrom_take pre (middle ++ tail)
  have hT := subst_paramsFrom_slice (pre ++ middle) tail []
  simp only [List.length_append, List.append_nil, List.append_assoc] at hT
  rw [substArgs_append, hP, hT]

def argumentRule (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat) (failure : Bool) : MRule :=
  compilerFragmentAt (compilerArgumentFragments c.source c.strategy c.nodes c.digits
    (c.address (.args arity callee actuals stage)) arity callee actuals stage) (primarySlot failure)

theorem argumentRule_arity (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp)
    (stage : Nat) (failure : Bool) :
    (argumentRule c arity callee actuals stage failure).arity = 5 + 2 * c.digits + 4 * arity + 4 * stage := by
  cases hr : ruleAtM c.source.rules callee with
  | none => cases failure <;> simp [argumentRule, compilerArgumentFragments, hr, compilerFragmentAt, primarySlot, primaryRule]
  | some rule =>
    by_cases ha : rule.arity = actuals.length
    · by_cases ht : stage = actuals.length
      · cases failure <;> simp [argumentRule, compilerArgumentFragments, hr, ha, ht, compilerFragmentAt, primarySlot, primaryRule]
      · cases he : actuals[stage]? <;> cases failure <;>
          simp [argumentRule, compilerArgumentFragments, hr, ha, ht, he, compilerFragmentAt, primarySlot, primaryRule]
    · cases failure <;> simp [argumentRule, compilerArgumentFragments, hr, ha, compilerFragmentAt, primarySlot, primaryRule]

theorem CompilerConfig.argument_unfold (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    (hn : .args E.length callee actuals stage ∈ c.nodes) (p q : Nat) (failure : Bool) (P : Prop) :
    RootTest c.target (c.argumentCall E.length callee actuals stage failure (stageArgs x ds E C p q)) x P ↔
      RootTest c.target (MExp.subst (stageArgs x ds E C p q) (argumentRule c E.length callee actuals stage failure).body) x P := by
  have hr := c.at (.args E.length callee actuals stage) hn (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  change ruleAtM c.target.rules (c.address (.args E.length callee actuals stage) + primarySlot failure) =
    some (argumentRule c E.length callee actuals stage failure) at hr
  exact rootTest_call_iff hr (by rw [argumentRule_arity, stageArgs_length, hd, hc]) x P

/-- Finishing argument capture discards the caller environment and installs the captured values. -/
theorem compiledArguments_done (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (hc : C.length = actuals.length)
    (hn : .args E.length callee actuals actuals.length ∈ c.nodes) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (p q : Nat) (hl : LookupCorrect c x ds C callee p q) : ArgsCorrect c x ds E C callee actuals actuals.length p q := by
  let pre := [skipN p, skipN (x.length - p), skipN q, skipN (x.length - q), skipN x.length] ++ clockArgs x.length ds
  have hpre : pre.length = 5 + 2 * c.digits := by simp [pre, clockArgs_length, hd]; omega
  have hmiddle : (envArgs x.length E).length = 4 * E.length := envArgs_length _ _
  have htail : (envArgs x.length C).length = 4 * actuals.length := by rw [envArgs_length, hc]
  have hperm := subst_dropMiddle pre (envArgs x.length E) (envArgs x.length C)
  have hargs : stageArgs x ds E C p q = pre ++ (envArgs x.length E ++ envArgs x.length C) := by
    simp [stageArgs, evalArgs, evalRest, pre, List.append_assoc]
  have hresult : argumentResult c x ds E C callee [] p =
      valAt (tblV c.source x c.strategy (clockValue x.length ds) callee (decodeEnv x C)) p := by
    simp [argumentResult, evSeqArgs, evParArgs, finishSeq, finishPar]
  constructor
  · change RootTest c.target (c.argumentCall E.length callee actuals actuals.length false (stageArgs x ds E C p q)) x _
    rw [c.argument_unfold x ds hd E C callee actuals actuals.length hc hn p q false]
    simp [argumentRule, compilerArgumentFragments, compilerFragmentAt, hr, ha, primarySlot, primaryRule]
    change RootTest c.target (.call (c.address (.lookup callee))
      (MExp.substArgs (stageArgs x ds E C p q)
        (paramsFrom 0 (5 + 2 * c.digits) ++ paramsFrom (5 + 2 * c.digits + 4 * E.length) (4 * actuals.length)))) x _
    rw [hargs, ← hpre, ← hmiddle, ← htail, hperm]
    simpa only [CompilerConfig.lookupCall, primarySlot, if_false, Bool.false_eq_true, Nat.add_zero,
      pre, evalArgs, evalRest, List.cons_append, List.nil_append, hresult] using hl.1
  · change RootTest c.target (c.argumentCall E.length callee actuals actuals.length true (stageArgs x ds E C p q)) x _
    rw [c.argument_unfold x ds hd E C callee actuals actuals.length hc hn p q true]
    simp [argumentRule, compilerArgumentFragments, compilerFragmentAt, hr, ha, primarySlot, primaryRule]
    change RootTest c.target (.call (c.address (.lookup callee) + 1)
      (MExp.substArgs (stageArgs x ds E C p q)
        (paramsFrom 0 (5 + 2 * c.digits) ++ paramsFrom (5 + 2 * c.digits + 4 * E.length) (4 * actuals.length)))) x _
    rw [hargs, ← hpre, ← hmiddle, ← htail, hperm]
    simpa only [CompilerConfig.lookupCall, primarySlot, if_true, pre, evalArgs, evalRest,
      List.cons_append, List.nil_append, hresult] using hl.2

end Shallot.MacroPeg.CBVtoCBN
