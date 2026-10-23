import MacroPeg.CBVtoCBN.CompiledControl

namespace Shallot.MacroPeg.CBVtoCBN

theorem argAt_append_offset (pre args : List MExp) (k : Nat) :
    argAt (pre ++ args) (pre.length + k) = argAt args k := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show pre.length + 1 + k = (pre.length + k) + 1 by omega, argAt, ih]

theorem envArgs_get (n : Nat) (E : CapturedEnv) (k a b : Nat) (he : E[k]? = some (a, b)) :
    argAt (envArgs n E) (4 * k) = some (skipN a) ∧
    argAt (envArgs n E) (4 * k + 1) = some (skipN (n - a)) ∧
    argAt (envArgs n E) (4 * k + 2) = some (skipN b) ∧
    argAt (envArgs n E) (4 * k + 3) = some (skipN (n - b)) := by
  induction E generalizing k with
  | nil => simp at he
  | cons span E ih =>
    cases k with
    | zero =>
      have hs : span = (a, b) := Option.some.inj he
      subst span
      exact ⟨rfl, rfl, rfl, rfl⟩
    | succ k =>
      have ht : E[k]? = some (a, b) := he
      simpa only [envArgs, Nat.mul_add, Nat.mul_one, Nat.add_assoc, argAt] using ih k ht

theorem subst_envArgs_get (pre : List MExp) (n : Nat) (E : CapturedEnv) (k a b : Nat)
    (he : E[k]? = some (a, b)) :
    MExp.subst (pre ++ envArgs n E) (.param (pre.length + 4 * k)) = skipN a ∧
    MExp.subst (pre ++ envArgs n E) (.param (pre.length + 4 * k + 1)) = skipN (n - a) ∧
    MExp.subst (pre ++ envArgs n E) (.param (pre.length + 4 * k + 2)) = skipN b ∧
    MExp.subst (pre ++ envArgs n E) (.param (pre.length + 4 * k + 3)) = skipN (n - b) := by
  have hs := envArgs_get n E k a b he
  simp [MExp.subst, Nat.add_assoc, argAt_append_offset, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

theorem evalArgs_env_get (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (p q k a b : Nat) (he : E[k]? = some (a, b)) :
    MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k)) = skipN a ∧
    MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k + 1)) = skipN (x.length - a) ∧
    MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k + 2)) = skipN b ∧
    MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k + 3)) = skipN (x.length - b) := by
  let pre := [skipN p, skipN (x.length - p), skipN q, skipN (x.length - q), skipN x.length] ++ clockArgs x.length ds
  have hlen : pre.length = 5 + 2 * c.digits := by simp [pre, clockArgs_length, hd]; omega
  have hs := subst_envArgs_get pre x.length E k a b he
  have ha : pre ++ envArgs x.length E = evalArgs x ds E p q := by
    simp [pre, evalArgs, evalRest]
  simpa only [ha, hlen] using hs

theorem subst_parameterSuccessP (args : List MExp) (matcher : Nat) (a b p q : MExp) :
    MExp.subst args (parameterSuccessP matcher a b p q) =
      parameterSuccessP matcher (MExp.subst args a) (MExp.subst args b) (MExp.subst args p) (MExp.subst args q) := by
  simp [parameterSuccessP, lePositionP, fitsLengthP, andP, MExp.subst, MExp.substArgs]

theorem compiledParameter_block (c : CompilerConfig) (arity k : Nat) (hk : k < arity)
    (hn : .expr arity (.param k) ∈ c.nodes) :
    let base := c.address (.expr arity (.param k))
    RulesAt c.target (base + 10) (parameterFailureBlock (base + 10) 0) := by
  let node := CompileNode.expr arity (.param k)
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  apply c.block_at node hn (fs.take 1) 10 _ []
  · simp [fs, node, compilerFragments, compilerExpressionFragments, hk]
  · simp [parameterFailureBlock, pairSearchBlock, compilerSlotSize]
    omega
  · simp [fs, node, compilerFragments, compilerExpressionFragments, hk]

theorem RulesAt.parameterFailure_test {g : MGrammar} {entry matcher : Nat}
    (h : RulesAt g entry (parameterFailureBlock entry matcher))
    (hm : ruleAtM g.rules matcher = some ⟨4, spanEqBody matcher unicodeAlphabet⟩)
    (x : List Char) (a b p : Nat) (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) :
    RootTest g (.call entry [skipN p, skipN (x.length - p), skipN (x.length - a), skipN b]) x
      (Shallot.stripPrefix? (pre x a b) (sfx x p) = none) := by
  obtain ⟨preRules, tail, hpre, hg⟩ := h.split (by simp [parameterFailureBlock])
  have hm' := hm
  rw [hg] at hm'
  have ht := parameterFailureBlock_test preRules tail matcher (by simpa only [hpre] using hm') x a b p ha hb hp
  simpa only [hpre, ← hg] using ht

/-- Captured parameter lookup in the actual generated grammar preserves both source outcomes. -/
theorem compiledParameter_correct (c : CompilerConfig) (ha : c.alphabet = unicodeAlphabet)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
    (k : Nat) (hn : .expr E.length (.param k) ∈ c.nodes) (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    ExprCorrect c x ds E (.param k) p q := by
  have hm : ruleAtM c.target.rules 0 = some ⟨4, spanEqBody 0 c.alphabet⟩ := rfl
  rw [ha] at hm
  by_cases hk : k < E.length
  · obtain ⟨span, hspan⟩ : ∃ span, E[k]? = some span := ⟨E[k], List.getElem?_eq_getElem hk⟩
    rcases span with ⟨a, b⟩
    have hvalid := hv (a, b) (List.mem_of_getElem? hspan)
    have hsource : (decodeEnv x E)[k]? = some (pre x a b) := by simp [decodeEnv, List.getElem?_map, hspan]
    have hs := evalArgs_env_get c x ds hd E p q k a b hspan
    constructor
    · rw [c.expr_unfold hn x ds hd E rfl p q false]
      simp [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hk, primaryRule]
      change RootTest c.target (MExp.subst (evalArgs x ds E p q)
        (parameterSuccessP 0 (.param (5 + 2 * c.digits + 4 * k + 1)) (.param (5 + 2 * c.digits + 4 * k + 2))
          (.param 1) (.param 2))) x _
      rw [subst_parameterSuccessP, hs.2.1, hs.2.2.1]
      change RootTest c.target (parameterSuccessP 0 (skipN (x.length - a)) (skipN b)
        (skipN (x.length - p)) (skipN q)) x _
      exact parameterSource_success hm x c.strategy _ _ k a b p q hsource hvalid.2 hvalid.1 hp hq
    · rw [c.expr_unfold hn x ds hd E rfl p q true]
      simp [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hk, primaryRule]
      change RootTest c.target (MExp.subst (evalArgs x ds E p q) (.call
        (c.address (.expr E.length (.param k)) + 10)
        [.param 0, .param 1, .param (5 + 2 * c.digits + 4 * k + 1), .param (5 + 2 * c.digits + 4 * k + 2)])) x _
      change RootTest c.target (.call (c.address (.expr E.length (.param k)) + 10)
        [MExp.subst (evalArgs x ds E p q) (.param 0), MExp.subst (evalArgs x ds E p q) (.param 1),
         MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k + 1)),
         MExp.subst (evalArgs x ds E p q) (.param (5 + 2 * c.digits + 4 * k + 2))]) x _
      rw [hs.2.1, hs.2.2.1]
      change RootTest c.target (.call (c.address (.expr E.length (.param k)) + 10)
        [skipN p, skipN (x.length - p), skipN (x.length - a), skipN b]) x _
      exact parameterSource_failure x c.strategy _ _ k (pre x a b) p hsource
        ((compiledParameter_block c E.length k hk hn).parameterFailure_test hm x a b p hvalid.2 hvalid.1 hp)
  · have hsource : (decodeEnv x E)[k]? = none := List.getElem?_eq_none (by rw [decodeEnv_length]; omega)
    have ht := parameterMissing_tests c.target c.source x c.strategy
      (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) k p q hsource
    constructor
    · rw [c.expr_unfold hn x ds hd E rfl p q false]
      simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hk, primaryRule,
        MExp.failAlways, MExp.subst] using ht.1
    · rw [c.expr_unfold hn x ds hd E rfl p q true]
      simpa [expressionRule, primarySlot, compilerExpressionFragments, compilerFragmentAt, hk, primaryRule, MExp.subst] using ht.2

end Shallot.MacroPeg.CBVtoCBN
