import MacroPeg.CBV.ParSimulation.CompilerState

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode RulesAt compilerSlotSize compilerFragmentAt unicodeAlphabet)

private theorem argAt_append_offset (pre args : List MExp) (k : Nat) :
    argAt (pre ++ args) (pre.length + k) = argAt args k := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show pre.length + 1 + k = (pre.length + k) + 1 by omega, argAt, ih]

theorem envValues_get (x : List Char) (E : CapturedEnv) (k a b : Nat) (hE : E[k]? = some (a, b)) :
    argAt (prefixValues x (envPositions x.length E)) (2 * k) = some (.lit (x.take (x.length - a))) ∧
    argAt (prefixValues x (envPositions x.length E)) (2 * k + 1) = some (.lit (x.take (x.length - b))) := by
  induction E generalizing k with
  | nil => simp at hE
  | cons span E ih =>
    cases k with
    | zero =>
      have hs : span = (a, b) := Option.some.inj hE
      subst span
      exact ⟨rfl, rfl⟩
    | succ k =>
      have ht : E[k]? = some (a, b) := hE
      simpa only [envPositions, prefixValues, Nat.mul_add, Nat.mul_one, Nat.add_assoc, argAt] using ih k ht

theorem stateValues_env_get (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (p q k a b : Nat) (hE : E[k]? = some (a, b)) :
    MExp.subst (stateValues x ds E p q) (.param (3 + c.digits + 2 * k)) = .lit (x.take (x.length - a)) ∧
    MExp.subst (stateValues x ds E p q) (.param (3 + c.digits + 2 * k + 1)) = .lit (x.take (x.length - b)) := by
  let preArgs := prefixValues x ([x.length - p, x.length - q, x.length] ++ ds)
  have hLen : preArgs.length = 3 + c.digits := by simp [preArgs, hd]; omega
  have hState : preArgs ++ prefixValues x (envPositions x.length E) = stateValues x ds E p q := by
    simp [preArgs, stateValues, statePositions, prefixValues_append, prefixValues]
  have h := envValues_get x E k a b hE
  rw [← hState]
  simp [MExp.subst, ← hLen, Nat.add_assoc, argAt_append_offset, h.1, h.2]

theorem subst_parameterSuccess (args : List MExp) (order matcher : Nat) (a b p q : MExp) :
    MExp.subst args (parameterSuccess order matcher a b p q) =
      parameterSuccess order matcher (MExp.subst args a) (MExp.subst args b)
        (MExp.subst args p) (MExp.subst args q) := by
  simp [parameterSuccess, MExp.subst, MExp.substArgs]

theorem compiledParameter_block (c : CompilerConfig) (arity k : Nat) (hk : k < arity)
    (hn : .expr arity (.param k) ∈ c.nodes) :
    RulesAt c.target (c.address (.expr arity (.param k)) + 10)
      (parameterFailureRules (c.address (.expr arity (.param k)) + 10) 1 2) := by
  let node := CompileNode.expr arity (.param k)
  let fs := fragments c.source c.nodes c.digits (c.address node) node
  apply c.block_at node hn (fs.take 1) 10 _ []
  · simp [fs, node, fragments, expressionFragments, hk]
  · simp [parameterFailureRules, compilerSlotSize]; omega
  · simp [fs, node, fragments, expressionFragments, hk]

theorem parameterFailureRules_test {g : MGrammar} {entry order equal matcher : Nat}
    (h : RulesAt g entry (parameterFailureRules entry order matcher))
    (ho : ruleAtM g.rules order = some ⟨2, leBody order equal⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (hm : ruleAtM g.rules matcher = some ⟨4, intervalBody matcher equal unicodeAlphabet⟩)
    (x : List Char) (a b p : Nat) (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) :
    Predicate g .callByValuePar
      (.call entry [.lit (x.take (x.length - a)), .lit (x.take (x.length - b)), .lit (x.take (x.length - p))]) x
      (Shallot.stripPrefix? (pre x a b) (sfx x p) = none) := by
  have h0 : ruleAtM g.rules entry = some
      ⟨3, parameterFailure (entry + 1) (.param 0) (.param 1) (.param 2)⟩ := by
    simpa only [Nat.add_zero, parameterFailureRules, ruleAtM] using h 0 (by simp [parameterFailureRules])
  have h1 : ruleAtM g.rules (entry + 1) = some ⟨4, existsBody (entry + 1) (entry + 2) 3⟩ :=
    h 1 (by simp [parameterFailureRules])
  have h2 : ruleAtM g.rules (entry + 2) = some ⟨4, parameterCandidateBody order matcher⟩ :=
    h 2 (by simp [parameterFailureRules])
  have ht := captured_failure_test ho he hm h1 h2 x a b p ha hb hp
  have hv := prefixValues_args g x [x.length - a, x.length - b, x.length - p]
  constructor
  · intro hs
    exact par_call h0 rfl hv (by simpa only [MExp.subst, MExp.substArgs, parameterFailure, prefixValues, argAt] using ht.1 hs)
  · intro hs
    exact par_call h0 rfl hv (by simpa only [MExp.subst, MExp.substArgs, parameterFailure, prefixValues, argAt] using ht.2 hs)

/-- Captured parameters in the actual generated grammar agree with the
source evaluator, including an out-of-range source parameter reference. -/
theorem compiledParameter_correct (c : CompilerConfig) (hAlphabet : c.alphabet = unicodeAlphabet)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
    (k : Nat) (hn : .expr E.length (.param k) ∈ c.nodes) (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    ExprCorrect c x ds E (.param k) p q := by
  have hm := c.interval_rule
  rw [hAlphabet] at hm
  by_cases hk : k < E.length
  · obtain ⟨span, hspan⟩ : ∃ span, E[k]? = some span := ⟨E[k], List.getElem?_eq_getElem hk⟩
    rcases span with ⟨a, b⟩
    have hValid := hv (a, b) (List.mem_of_getElem? hspan)
    have hSource : (decodeEnv x E)[k]? = some (pre x a b) := by simp [decodeEnv, List.getElem?_map, hspan]
    have hs := stateValues_env_get c x ds hd E p q k a b hspan
    constructor
    · rw [c.expr_unfold hn x ds hd E rfl p q false]
      simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, hk]
      change Predicate c.target .callByValuePar
        (MExp.subst (stateValues x ds E p q) (parameterSuccess 1 2
          (.param (3 + c.digits + 2 * k)) (.param (3 + c.digits + 2 * k + 1)) (.param 0) (.param 1))) x _
      rw [subst_parameterSuccess, hs.1, hs.2]
      exact parameter_source_success c.order_rule c.equal_rule hm x .callByValueSeq _ _
        k a b p q hSource hValid.2 hValid.1 hp hq
    · rw [c.expr_unfold hn x ds hd E rfl p q true]
      simp [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, hk]
      change Predicate c.target .callByValuePar
        (.call (c.address (.expr E.length (.param k)) + 10)
          [MExp.subst (stateValues x ds E p q) (.param (3 + c.digits + 2 * k)),
           MExp.subst (stateValues x ds E p q) (.param (3 + c.digits + 2 * k + 1)),
           MExp.subst (stateValues x ds E p q) (.param 0)]) x _
      rw [hs.1, hs.2]
      apply parameter_source_failure x .callByValueSeq _ _ k (pre x a b) p hSource
      exact parameterFailureRules_test (compiledParameter_block c E.length k hk hn)
        c.order_rule c.equal_rule hm x a b p hValid.2 hValid.1 hp
  · have hSource : (decodeEnv x E)[k]? = none := by
      apply List.getElem?_eq_none
      simp only [decodeEnv, List.length_map]
      omega
    have ht := parameter_missing_tests c.target c.source x .callByValueSeq
      (tblV c.source x .callByValueSeq (CBVtoCBN.clockValue x.length ds)) (decodeEnv x E) k p q hSource
    constructor
    · rw [c.expr_unfold hn x ds hd E rfl p q false]
      simpa [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, hk, MExp.subst, MExp.failAlways, sourceResult] using ht.1
    · rw [c.expr_unfold hn x ds hd E rfl p q true]
      simpa [expressionRule, primarySlot, expressionFragments, compilerFragmentAt, hk, MExp.subst, sourceResult] using ht.2

end Shallot.MacroPeg.CBV.ParSimulation
