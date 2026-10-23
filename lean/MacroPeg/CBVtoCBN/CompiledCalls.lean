import MacroPeg.CBVtoCBN.CompiledParameters

namespace Shallot.MacroPeg.CBVtoCBN

/-- The source meaning of an argument stage includes all previously captured values in order. -/
def argumentResult (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (remaining : List MExp) (p : Nat) : Res :=
  let T := tblV c.source x c.strategy (clockValue x.length ds)
  if c.strategy = .callByValueSeq then
    finishSeq (fun W q => valAt (T callee (decodeEnv x C ++ W)) q)
      (evSeqArgs c.source x c.strategy T (decodeEnv x E) remaining p)
  else
    finishPar (fun W => valAt (T callee (decodeEnv x C ++ W)) p)
      (evParArgs c.source x c.strategy T (decodeEnv x E) remaining p)

def CompilerConfig.argumentCall (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp)
    (stage : Nat) (failure : Bool) (args : List MExp) : MExp :=
  .call (c.address (.args arity callee actuals stage) + primarySlot failure) args

def ArgsCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (actuals : List MExp) (stage p q : Nat) : Prop :=
  let result := argumentResult c x ds E C callee (actuals.drop stage) p
  let args := evalArgs x ds E p q ++ envArgs x.length C
  RootTest c.target (c.argumentCall E.length callee actuals stage false args) x (result = some (some q)) ∧
    RootTest c.target (c.argumentCall E.length callee actuals stage true args) x (result = some none)

theorem argumentResult_zero (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (callee : Nat) (actuals : List MExp) (p : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length) :
    argumentResult c x ds E [] callee actuals p =
      evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) (.call callee actuals) p := by
  unfold argumentResult
  dsimp only
  by_cases hs : c.strategy = .callByValueSeq
  · rw [if_pos hs]
    have h := evV_call_finishSeq (x := x)
      (T := tblV c.source x c.strategy (clockValue x.length ds)) (E := decodeEnv x E) hr ha p
    simpa only [hs, decodeEnv, List.map_nil, List.nil_append] using h.symm
  · rw [if_neg hs]
    have h := evV_call_finishPar (x := x)
      (T := tblV c.source x c.strategy (clockValue x.length ds)) (E := decodeEnv x E) hr ha hs p
    simpa only [decodeEnv, List.map_nil, List.nil_append] using h.symm

/-- A valid generated source call delegates precisely to the initial argument stage. -/
theorem compiledCall_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp) (hn : .expr E.length (.call callee actuals) ∈ c.nodes)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (p q : Nat) (h : ArgsCorrect c x ds E [] callee actuals 0 p q) :
    ExprCorrect c x ds E (.call callee actuals) p q := by
  have hs := h.1
  have hf := h.2
  simp only [CompilerConfig.argumentCall, primarySlot, envArgs, List.append_nil, List.drop_zero] at hs hf
  rw [argumentResult_zero c x ds E callee actuals p hr ha] at hs hf
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simp [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, ha, primaryRule]
    simp only [compilerCall, MExp.subst, evalArgs_subst_all c x ds hd E p q]
    simpa [CompilerConfig.address] using hs
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simp [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, ha, primaryRule]
    simp only [compilerCall, MExp.subst, evalArgs_subst_all c x ds hd E p q]
    simpa [CompilerConfig.address] using hf

/-- Missing callees explicitly fail before any argument evaluation, as in the source semantics. -/
theorem compiledCall_missing (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp) (hn : .expr E.length (.call callee actuals) ∈ c.nodes)
    (hr : ruleAtM c.source.rules callee = none) (p q : Nat) : ExprCorrect c x ds E (.call callee actuals) p q := by
  have hs := rootTest_fail c.target x
  have hf := rootTest_eps c.target x
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, primaryRule,
      MExp.failAlways, MExp.subst, evV] using hs
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, primaryRule,
      MExp.subst, evV] using hf

theorem compiledCall_badArity (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (callee : Nat) (actuals : List MExp) (hn : .expr E.length (.call callee actuals) ∈ c.nodes)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity ≠ actuals.length)
    (p q : Nat) : ExprCorrect c x ds E (.call callee actuals) p q := by
  have hs := rootTest_fail c.target x
  have hf := rootTest_eps c.target x
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, ha, primaryRule,
      MExp.failAlways, MExp.subst, evV] using hs
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hr, ha, primaryRule,
      MExp.subst, evV] using hf

end Shallot.MacroPeg.CBVtoCBN
