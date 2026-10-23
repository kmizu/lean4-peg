import MacroPeg.CBVtoCBN.CompilerBlocks

namespace Shallot.MacroPeg.CBVtoCBN

theorem expressionAdapter_rule (source : MGrammar) (nodes : List CompileNode) (digits base arity : Nat) (e : MExp) :
    compilerFragmentAt (compilerExpressionFragments source nodes digits base arity e) 2 =
      compilerFailureAdapter (base + 1) (5 + 2 * digits + 4 * arity) := by
  cases e <;> simp only [compilerExpressionFragments, primaryRule]
  all_goals first | rfl | (split <;> first | rfl | (split <;> rfl))

theorem failureAdapter_subst (failure : Nat) (p ps N : MExp) (tail : List MExp) :
    MExp.subst (p :: ps :: N :: tail) (compilerFailureAdapter failure (tail.length + 5)).body =
      .call failure (p :: ps :: .eps :: N :: N :: tail) := by
  have hs : tail.length + 5 - 4 = tail.length + 1 := by omega
  simp only [compilerFailureAdapter, MExp.subst, MExp.substArgs, argAt, hs]
  have h := subst_paramsFrom (N :: tail)
  simp only [List.length_cons] at h
  rw [subst_paramsFrom_cons, subst_paramsFrom_cons, h]

/-- The real failure adapter calls the primary predicate with a valid unused endpoint zero. -/
theorem compiledFailureAdapter_test (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (e : MExp) (hn : .expr E.length e ∈ c.nodes) (p : Nat)
    (h : ExprCorrect c x ds E e p 0) :
    RootTest c.target (.call (c.address (.expr E.length e) + 2)
      (skipN p :: skipN (x.length - p) :: evalRest x ds E)) x
      (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) e p = some none) := by
  have hr := c.at (.expr E.length e) hn 2 (by unfold compilerSlotSize; omega)
  change ruleAtM c.target.rules (c.address (.expr E.length e) + 2) =
    some (compilerFragmentAt (compilerExpressionFragments c.source c.nodes c.digits
      (c.address (.expr E.length e)) E.length e) 2) at hr
  rw [expressionAdapter_rule] at hr
  rw [rootTest_call_iff hr (by simp only [compilerFailureAdapter, List.length_cons, evalRest_length, hd]; omega)]
  have hwidth : 5 + 2 * c.digits + 4 * E.length =
      (clockArgs x.length ds ++ envArgs x.length E).length + 5 := by
    simp only [List.length_append, clockArgs_length, envArgs_length, hd]; omega
  change RootTest c.target (MExp.subst
    (skipN p :: skipN (x.length - p) :: skipN x.length :: (clockArgs x.length ds ++ envArgs x.length E))
    (compilerFailureAdapter (c.address (.expr E.length e) + 1) (5 + 2 * c.digits + 4 * E.length)).body) x _
  rw [hwidth, failureAdapter_subst]
  simpa only [CompilerConfig.exprCall, evalArgs, evalRest, Nat.sub_zero, skipN, if_true] using h.2

/-- Both helper fragments for a sequence are present at their actual addresses in the candidate. -/
theorem compiledSequence_blocks (c : CompilerConfig) (arity : Nat) (a b : MExp)
    (hn : .expr arity (.seq a b) ∈ c.nodes) :
    let base := c.address (.expr arity (.seq a b))
    let rest := 5 + 2 * c.digits + 4 * arity - 4
    RulesAt c.target (base + 10) (sequenceSuccessBlock (base + 10)
      (c.address (.expr arity a)) (c.address (.expr arity b)) rest) ∧
    RulesAt c.target (base + 20) (sequenceFailureBlock (base + 20)
      (c.address (.expr arity a)) (c.address (.expr arity a) + 2) (c.address (.expr arity b) + 2) rest) := by
  let node := CompileNode.expr arity (.seq a b)
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  constructor
  · apply c.block_at node hn (fs.take 1) 10 _ (fs.drop 2)
    · rfl
    · simp [sequenceSuccessBlock, pairSearchBlock, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerExpressionFragments]
  · apply c.block_at node hn (fs.take 2) 20 _ []
    · rfl
    · simp [sequenceFailureBlock, pairSearchBlock, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerExpressionFragments, sequenceSuccessBlock, pairSearchBlock]

/-- Success and failure of generated sequencing agree with the bounded source evaluator.
The hypotheses are the recursively established predicates of the two proper source subexpressions. -/
theorem compiledSequence_correct (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (a b : MExp)
    (hav : ExprAvailable c.nodes E.length (.seq a b)) (p q : Nat) (hp : p ≤ x.length)
    (hl : ∀ j, j ≤ x.length → ExprCorrect c x ds E a p j)
    (hr : ∀ j, j ≤ x.length → ExprCorrect c x ds E b j q)
    (hr0 : ∀ j, j ≤ x.length → ExprCorrect c x ds E b j 0) :
    ExprCorrect c x ds E (.seq a b) p q := by
  have hn := hav.self
  let rest := evalRest x ds E
  have hrest : rest.length = 5 + 2 * c.digits + 4 * E.length - 4 := by rw [evalRest_length, hd]; omega
  have hblocks := compiledSequence_blocks c E.length a b hn
  dsimp only at hblocks
  rw [← hrest] at hblocks
  have hbound := evV_ok (g := c.source) (s := c.strategy) (E := decodeEnv x E) (tblV_ok c.source x c.strategy (clockValue x.length ds)) a p hp
  have h0 := hblocks.1.sequenceSuccess_test rest x p q _ _ hbound
    (fun j hj => (hl j hj).1) (fun j hj => (hr j hj).1)
  have h1 := hblocks.2.sequenceFailure_test rest x p _ _ hbound
    (fun j hj => (hl j hj).1)
    (compiledFailureAdapter_test c x ds hd E a hav.seq.1.self p (hl 0 (by omega)))
    (fun j hj => compiledFailureAdapter_test c x ds hd E b hav.seq.2.self j (hr0 j hj))
  have hs := evalArgs_subst_all c x ds hd E p q
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q)
      (.call (c.address (.expr E.length (.seq a b)) + 10) (.eps :: paramsFrom 0 (5 + 2 * c.digits + 4 * E.length)))) x _
    simp only [MExp.subst, MExp.substArgs, hs]
    exact h0
  · rw [c.expr_unfold hn x ds hd E rfl p q true]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q)
      (.call (c.address (.expr E.length (.seq a b)) + 20) (.param 0 :: .param 1 :: paramsFrom 4 (5 + 2 * c.digits + 4 * E.length - 4)))) x _
    have htail : MExp.substArgs (evalArgs x ds E p q) (paramsFrom 4 rest.length) = rest := by
      simpa [evalArgs, rest] using subst_paramsFrom_slice
        [skipN p, skipN (x.length - p), skipN q, skipN (x.length - q)] rest []
    simp only [evalArgs] at htail
    rw [← hrest]
    simp only [MExp.subst, MExp.substArgs, evalArgs, argAt]
    rw [htail]
    exact h1

end Shallot.MacroPeg.CBVtoCBN
