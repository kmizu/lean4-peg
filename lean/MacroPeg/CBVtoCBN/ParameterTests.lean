import MacroPeg.CBVtoCBN.LeafTests

namespace Shallot.MacroPeg.CBVtoCBN

/-- A successful literal match at a suffix is determined by the remaining length. -/
theorem stripPrefix_length_iff (x w : List Char) (p q : Nat) (hp : p ≤ x.length) :
    (Shallot.stripPrefix? w (sfx x p)).map List.length = some q ↔
      q ≤ p ∧ Shallot.stripPrefix? w (sfx x p) = some (sfx x q) := by
  constructor
  · intro h
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => simp [hs] at h
    | some rest =>
      have hlen : rest.length = q := Option.some.inj (by simpa only [hs, Option.map_some] using h)
      have he := (stripPrefix_exact w (sfx x p) rest).mp hs
      have ht := congrArg List.length he
      rw [length_sfx x hp, List.length_append, hlen] at ht
      refine ⟨by omega, ?_⟩
      have hx : x = (x.take (x.length - p) ++ w) ++ rest := by
        calc
          x = x.take (x.length - p) ++ sfx x p := (List.take_append_drop _ x).symm
          _ = x.take (x.length - p) ++ (w ++ rest) := congrArg (fun ys => x.take (x.length - p) ++ ys) he
          _ = (x.take (x.length - p) ++ w) ++ rest := (List.append_assoc _ _ _).symm
      have hr := sfx_suffix hx
      rw [hlen] at hr
      rw [hr]
  · rintro ⟨hq, hs⟩
    rw [hs]
    simp only [Option.map_some, length_sfx x (by omega : q ≤ x.length)]

/-- Interval comparison realizes the literal captured by CBV in any grammar containing the matcher rule. -/
theorem capturedValue_test {g : MGrammar} {matcher : Nat}
    (hm : ruleAtM g.rules matcher = some ⟨4, spanEqBody matcher unicodeAlphabet⟩)
    (x : List Char) (a b p q : Nat) (ha : a ≤ x.length) (hb : b ≤ a)
    (hp : p ≤ x.length) (hq : q ≤ p) :
    RootTest g (.call matcher [skipN (x.length - a), skipN b, skipN (x.length - p), skipN q]) x
      (Shallot.stripPrefix? (pre x a b) (sfx x p) = some (sfx x q)) := by
  have h := spanEq_obs hm x (fun c _ => unicodeAlphabet_mem c)
    (x.length - a) (x.length - b) (x.length - p) (x.length - q)
    (by omega) (by omega) (by omega) (by omega)
  rw [show x.length - (x.length - b) = b by omega,
    show x.length - (x.length - q) = q by omega] at h
  apply (RootTest.of_obs h).congr
  rw [spanSlice_pre x a b ha hb, spanSlice_pre x p q hp hq]
  exact (pre_literal_iff x a b p q hp hq).symm

/-- Success of a captured parameter, guarded so the interval matcher only receives valid target intervals. -/
def parameterSuccessP (matcher : Nat) (capturedStartComplement capturedEnd positionComplement remaining : MExp) : MExp :=
  .seq (lePositionP remaining positionComplement)
    (.call matcher [capturedStartComplement, capturedEnd, positionComplement, remaining])

theorem parameterSuccess_firstOrder (matcher : Nat) {a b p q : MExp}
    (ha : a.FirstOrder) (hb : b.FirstOrder) (hp : p.FirstOrder) (hq : q.FirstOrder) :
    (parameterSuccessP matcher a b p q).FirstOrder :=
  ⟨(positionTests_firstOrder hq hp).2.1, ha, hb, hp, hq, trivial⟩

theorem parameterSuccess_test {g : MGrammar} {matcher : Nat}
    (hm : ruleAtM g.rules matcher = some ⟨4, spanEqBody matcher unicodeAlphabet⟩)
    (x : List Char) (a b p q : Nat) (ha : a ≤ x.length) (hb : b ≤ a)
    (hp : p ≤ x.length) (_hq : q ≤ x.length) :
    RootTest g (parameterSuccessP matcher (skipN (x.length - a)) (skipN b)
      (skipN (x.length - p)) (skipN q)) x
      ((Shallot.stripPrefix? (pre x a b) (sfx x p)).map List.length = some q) := by
  have hg := lePosition_obs (skipN_rep g q) (skipN_rep g (x.length - p)) x (by omega)
  rw [show x.length - (x.length - p) = p by omega] at hg
  apply ((RootTest.of_obs hg).guarded (fun hqp => capturedValue_test hm x a b p q ha hb hp hqp)).congr
  exact (stripPrefix_length_iff x (pre x a b) p q hp).symm

/-- Candidate counter `q` precedes the fixed current-position and captured-value context. -/
def parameterCandidateBody (matcher : Nat) : MExp :=
  parameterSuccessP matcher (.param 4) (.param 5) (.param 3) (.param 0)

theorem parameterCandidate_subst (matcher : Nat) (q q' p p' a b : MExp) :
    MExp.subst [q, q', p, p', a, b] (parameterCandidateBody matcher) = parameterSuccessP matcher a b p' q := by
  simp [parameterCandidateBody, parameterSuccessP, lePositionP, fitsLengthP, andP,
    MExp.subst, MExp.substArgs, argAt]

/-- Negation is used here only on the total existence test for a literal's matching endpoint. -/
def parameterFailureBody (search : Nat) : MExp := .notP (.call search (.eps :: paramsFrom 0 4))

def parameterFailureBlock (entry matcher : Nat) : List MRule :=
  ⟨4, parameterFailureBody (entry + 1)⟩ ::
    (pairSearchBlock (entry + 1) (entry + 4) 4 ++ [⟨6, parameterCandidateBody matcher⟩])

theorem parameterFailureBlock_firstOrder (entry matcher : Nat) :
    ∀ rule ∈ parameterFailureBlock entry matcher, rule.body.FirstOrder := by
  intro rule hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨trivial, paramsFrom_firstOrder _ _⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact pairSearchBlock_firstOrder _ _ _ rule hr
  · have he := List.mem_singleton.mp hr
    subst rule
    exact parameterSuccess_firstOrder _ trivial trivial trivial trivial

theorem parameterFailureBlock_test (preRules tail : List MRule) (matcher : Nat)
    (hm : ruleAtM (preRules ++ (parameterFailureBlock preRules.length matcher ++ tail)) matcher =
      some ⟨4, spanEqBody matcher unicodeAlphabet⟩)
    (x : List Char) (a b p : Nat) (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) :
    RootTest ⟨preRules ++ (parameterFailureBlock preRules.length matcher ++ tail)⟩
      (.call preRules.length [skipN p, skipN (x.length - p), skipN (x.length - a), skipN b]) x
      (Shallot.stripPrefix? (pre x a b) (sfx x p) = none) := by
  let g : MGrammar := ⟨preRules ++ (parameterFailureBlock preRules.length matcher ++ tail)⟩
  let ctx := [skipN p, skipN (x.length - p), skipN (x.length - a), skipN b]
  have h0 : ruleAtM g.rules preRules.length = some ⟨4, parameterFailureBody (preRules.length + 1)⟩ := by
    rw [show preRules.length = preRules.length + 0 by omega]
    exact (ruleAtM_append_offset preRules _ 0).trans rfl
  have h1 : ruleAtM g.rules (preRules.length + 1) = some
      ⟨ctx.length + 1, anyPositionBody (preRules.length + 1) (preRules.length + 2) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [parameterFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_assoc]
  have h2 : ruleAtM g.rules (preRules.length + 2) = some
      ⟨ctx.length + 1, pairSeedBody (preRules.length + 3) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [parameterFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_assoc]
  have h3 : ruleAtM g.rules (preRules.length + 3) = some
      ⟨ctx.length + 2, complementContextBody (preRules.length + 3) (preRules.length + 4) ctx.length⟩ := by
    rw [ruleAtM_append_offset]
    simp [parameterFailureBlock, pairSearchBlock, ctx, ruleAtM, Nat.add_assoc]
  have h4 : ruleAtM g.rules (preRules.length + 4) = some ⟨6, parameterCandidateBody matcher⟩ := by
    rw [ruleAtM_append_offset]
    rfl
  have ht : ∀ q, q ≤ x.length → RootTest g
      (.call (preRules.length + 4) (skipN q :: skipN (x.length - q) :: ctx)) x
      ((Shallot.stripPrefix? (pre x a b) (sfx x p)).map List.length = some q) := by
    intro q hq
    rw [rootTest_call_iff h4 rfl, parameterCandidate_subst]
    exact parameterSuccess_test hm x a b p q ha hb hp hq
  have hs := anyPair_test ctx h1 h2 h3 x
    (fun q => (Shallot.stripPrefix? (pre x a b) (sfx x p)).map List.length = some q) ht
  rw [rootTest_call_iff h0 rfl]
  change RootTest g (.notP (.call (preRules.length + 1) (.eps :: ctx))) x _
  apply hs.notP.congr
  constructor
  · intro hn
    cases he : Shallot.stripPrefix? (pre x a b) (sfx x p) with
    | none => rfl
    | some rest =>
      have hsplit := (stripPrefix_exact _ _ _).mp he
      have hlen := congrArg List.length hsplit
      rw [length_sfx x hp, List.length_append] at hlen
      exact False.elim (hn ⟨rest.length, by omega, by simp [he]⟩)
  · intro he
    simp only [he, Option.map_none, reduceCtorEq, and_false, exists_const, not_false_eq_true]

/-- Parameter lookup agrees with the source evaluator when the environment stores this captured interval. -/
theorem parameterSource_success {target source : MGrammar} {matcher : Nat}
    (hm : ruleAtM target.rules matcher = some ⟨4, spanEqBody matcher unicodeAlphabet⟩)
    (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char))
    (k a b p q : Nat) (he : E[k]? = some (pre x a b))
    (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    RootTest target (parameterSuccessP matcher (skipN (x.length - a)) (skipN b)
      (skipN (x.length - p)) (skipN q)) x
      (evV source x s T E (.param k) p = some (some q)) := by
  apply (parameterSuccess_test hm x a b p q ha hb hp hq).congr
  simp only [evV, he]
  cases Shallot.stripPrefix? (pre x a b) (sfx x p) <;> simp

theorem parameterSource_failure {target source : MGrammar} {test : MExp}
    (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char))
    (k : Nat) (w : List Char) (p : Nat) (he : E[k]? = some w)
    (ht : RootTest target test x (Shallot.stripPrefix? w (sfx x p) = none)) :
    RootTest target test x (evV source x s T E (.param k) p = some none) := by
  apply ht.congr
  simp only [evV, he]
  cases Shallot.stripPrefix? w (sfx x p) <;> simp

theorem parameterMissing_tests (target source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (k p q : Nat) (he : E[k]? = none) :
    RootTest target MExp.failAlways x (evV source x s T E (.param k) p = some (some q)) ∧
      RootTest target .eps x (evV source x s T E (.param k) p = some none) := by
  constructor
  · exact (rootTest_fail target x).congr (by simp [evV, he])
  · exact (rootTest_eps target x).congr (by simp [evV, he])

end Shallot.MacroPeg.CBVtoCBN
