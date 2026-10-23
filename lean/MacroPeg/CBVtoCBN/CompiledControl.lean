import MacroPeg.CBVtoCBN.CompiledSequence

namespace Shallot.MacroPeg.CBVtoCBN

theorem RulesAt.anyPair_test {g : MGrammar} {entry test : Nat} (ctx : List MExp)
    (h : RulesAt g entry (pairSearchBlock entry test ctx.length)) (x : List Char) (P : Nat → Prop)
    (ht : ∀ j, j ≤ x.length → RootTest g (.call test (skipN j :: skipN (x.length - j) :: ctx)) x (P j)) :
    RootTest g (.call entry (.eps :: ctx)) x (∃ j, j ≤ x.length ∧ P j) := by
  apply Shallot.MacroPeg.CBVtoCBN.anyPair_test ctx (entry := entry) (seed := entry + 1) (helper := entry + 2) (test := test) _ _ _ x P ht
  · simpa only [pairSearchBlock, List.length_cons, List.length_nil, ruleAtM, Nat.add_zero] using h 0 (by simp [pairSearchBlock])
  · simpa only [pairSearchBlock, ruleAtM] using h 1 (by simp [pairSearchBlock])
  · simpa only [pairSearchBlock, ruleAtM] using h 2 (by simp [pairSearchBlock])

theorem RulesAt.repetition_test {g : MGrammar} {entry success failure : Nat} (rest : List MExp)
    (h : RulesAt g entry (repetitionBlock entry success failure rest.length))
    (x : List Char) (f : Nat → Res)
    (hs : ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → RootTest g
      (.call success (skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x (f p = some (some q)))
    (hf : ∀ p, p ≤ x.length → RootTest g (.call failure (skipN p :: skipN (x.length - p) :: rest)) x (f p = some none))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    RootTest g (.call entry (skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x
      (evStar f p = some (some q)) := by
  obtain ⟨pre, tail, hpre, hg⟩ := h.split (by simp [repetitionBlock])
  have h0 := repetitionBlock_test pre tail success failure rest x f
    (by simpa only [hpre, ← hg] using hs) (by simpa only [hpre, ← hg] using hf) p q hp hq
  simpa only [hpre, ← hg] using h0

theorem compiledStar_block (c : CompilerConfig) (arity : Nat) (a : MExp)
    (hn : .expr arity (.star a) ∈ c.nodes) :
    let base := c.address (.expr arity (.star a))
    RulesAt c.target (base + 10) (repetitionBlock (base + 10)
      (c.address (.expr arity a)) (c.address (.expr arity a) + 2) (5 + 2 * c.digits + 4 * arity - 4)) := by
  let node := CompileNode.expr arity (.star a)
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  apply c.block_at node hn (fs.take 1) 10 _ []
  · rfl
  · simp [repetitionBlock, pairSearchBlock, compilerSlotSize]
    omega
  · simp [fs, node, compilerFragments, compilerExpressionFragments]

theorem compiledStar_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : MExp) (hav : ExprAvailable c.nodes E.length (.star a))
    (h : ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ExprCorrect c x ds E a p q)
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) : ExprCorrect c x ds E (.star a) p q := by
  let rest := evalRest x ds E
  have hrest : rest.length = 5 + 2 * c.digits + 4 * E.length - 4 := by rw [evalRest_length, hd]; omega
  have hb := compiledStar_block c E.length a hav.self
  dsimp only at hb
  rw [← hrest] at hb
  have ht := hb.repetition_test rest x
    (fun p => evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p)
    (fun p hp q hq => (h p hp q hq).1)
    (fun p hp => compiledFailureAdapter_test c x ds hd E a hav.star.self p (h p hp 0 (by omega))) p q hp hq
  constructor
  · rw [c.expr_unfold hav.self x ds hd E rfl p q false]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (compilerCall
      (c.address (.expr E.length (.star a)) + 10) (5 + 2 * c.digits + 4 * E.length))) x _
    simp only [compilerCall, MExp.subst, evalArgs_subst_all c x ds hd E p q]
    exact ht
  · rw [c.expr_unfold hav.self x ds hd E rfl p q true]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) MExp.failAlways) x _
    simp only [MExp.failAlways, MExp.subst]
    exact repetitionFailure_test c.target x _ p

/-- Negation's failure predicate uses a bounded search over successful operand endpoints. -/
theorem compiledNot_blocks (c : CompilerConfig) (arity : Nat) (a : MExp)
    (hn : .expr arity (.notP a) ∈ c.nodes) :
    let base := c.address (.expr arity (.notP a))
    let rest := 5 + 2 * c.digits + 4 * arity - 4
    RulesAt c.target (base + 10) (pairSearchBlock (base + 10) (base + 13) (rest + 2)) ∧
    ruleAtM c.target.rules (base + 13) = some ⟨rest + 4, .call (c.address (.expr arity a))
      (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 4 rest)⟩ := by
  let node := CompileNode.expr arity (.notP a)
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  constructor
  · apply c.block_at node hn (fs.take 1) 10 _ (fs.drop 2)
    · rfl
    · simp [pairSearchBlock, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerExpressionFragments]
  · have h := c.at node hn 13 (by unfold compilerSlotSize; omega)
    simpa [node, compilerFragments, compilerExpressionFragments, compilerFragmentAt, pairSearchBlock, CompilerConfig.address] using h

theorem compiledNot_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : MExp) (hav : ExprAvailable c.nodes E.length (.notP a))
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (h : ∀ j, j ≤ x.length → ExprCorrect c x ds E a p j) : ExprCorrect c x ds E (.notP a) p q := by
  let rest := evalRest x ds E
  let ctx := skipN p :: skipN (x.length - p) :: rest
  have hrest : rest.length = 5 + 2 * c.digits + 4 * E.length - 4 := by rw [evalRest_length, hd]; omega
  have hblocks := compiledNot_blocks c E.length a hav.self
  dsimp only at hblocks
  rw [← hrest] at hblocks
  have hctx : ctx.length = rest.length + 2 := by simp only [ctx, List.length_cons]
  have hc : ∀ j, j ≤ x.length → RootTest c.target
      (.call (c.address (.expr E.length (.notP a)) + 13) (skipN j :: skipN (x.length - j) :: ctx)) x
      (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p = some (some j)) := by
    intro j hj
    rw [rootTest_call_iff hblocks.2 (by simp only [List.length_cons, hctx])]
    have hs := subst_paramsFrom_slice [skipN j, skipN (x.length - j), skipN p, skipN (x.length - p)] rest []
    simp only [List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hs
    simp only [ctx, MExp.subst, MExp.substArgs, argAt]
    rw [hs]
    exact (h j hj).1
  have hs := hblocks.1
  rw [← hctx] at hs
  have he := hs.anyPair_test ctx x
    (fun j => evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p = some (some j)) hc
  constructor
  · rw [c.expr_unfold hav.self x ds hd E rfl p q false]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q) (.seq (equalPositionP (.param 0) (.param 3))
      (.call (c.address (.expr E.length a) + 1) (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length))))) x _
    simp only [MExp.subst, equalPositionP, exactLengthP, andP]
    rw [evalArgs_subst_all c x ds hd E p q]
    simp only [evalArgs, argAt]
    have heq := equalPosition_obs (skipN_rep c.target p) (skipN_rep c.target (x.length - q)) x (by omega)
    rw [show x.length - (x.length - q) = q by omega] at heq
    exact notSuccess_test (RootTest.of_obs heq) (h q hq).2
  · rw [c.expr_unfold hav.self x ds hd E rfl p q true]
    change RootTest c.target (MExp.subst (evalArgs x ds E p q)
      (.call (c.address (.expr E.length (.notP a)) + 10) (.eps :: .param 0 :: .param 1 :: paramsFrom 4 (5 + 2 * c.digits + 4 * E.length - 4)))) x _
    have ht := subst_paramsFrom_slice [skipN p, skipN (x.length - p), skipN q, skipN (x.length - q)] rest []
    simp only [List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at ht
    rw [← hrest]
    simp only [MExp.subst, MExp.substArgs, evalArgs, argAt]
    rw [ht]
    exact notFailure_test (evV_ok (g := c.source) (s := c.strategy) (E := decodeEnv x E)
      (tblV_ok c.source x c.strategy (clockValue x.length ds)) a p hp) he

end Shallot.MacroPeg.CBVtoCBN
