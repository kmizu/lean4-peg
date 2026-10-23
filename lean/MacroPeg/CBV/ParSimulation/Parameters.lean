import MacroPeg.CBV.ParSimulation.Terminals
import MacroPeg.CBV.PrefixOrder
import MacroPeg.CBVtoCBN.ParameterTests

namespace Shallot.MacroPeg.CBV.ParSimulation

open RootObservation PrefixCounters
open CBVtoCBN (spanSlice_pre pre_literal_iff stripPrefix_length_iff unicodeAlphabet unicodeAlphabet_mem)

def parameterSuccess (order matcher : Nat) (a b p q : MExp) : MExp :=
  .seq (.call order [p, q]) (.call matcher [a, b, p, q])

theorem parameterSuccess_firstOrder (order matcher : Nat) {a b p q : MExp}
    (ha : a.FirstOrder) (hb : b.FirstOrder) (hp : p.FirstOrder) (hq : q.FirstOrder) :
    (parameterSuccess order matcher a b p q).FirstOrder :=
  ⟨⟨hp, hq, trivial⟩, ha, hb, hp, hq, trivial⟩

/-- A captured source substring is replayed by comparing its two stored
endpoints with the candidate matched interval, entirely at the input root. -/
theorem captured_success_test {g : MGrammar} {order equal matcher : Nat}
    (ho : ruleAtM g.rules order = some ⟨2, leBody order equal⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (hm : ruleAtM g.rules matcher = some ⟨4, intervalBody matcher equal unicodeAlphabet⟩)
    (x : List Char) (a b p q : Nat) (ha : a ≤ x.length) (hb : b ≤ a)
    (hp : p ≤ x.length) (hq : q ≤ x.length) :
    Predicate g .callByValuePar
      (parameterSuccess order matcher
        (.lit (x.take (x.length - a))) (.lit (x.take (x.length - b)))
        (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q)))) x
      ((Shallot.stripPrefix? (pre x a b) (sfx x p)).map List.length = some q) := by
  have hOrder := le_predicate ho he x (x.length - p) (x.length - q) (by omega) (by omega)
  have hGuard : Predicate g .callByValuePar
      (.call order [.lit (x.take (x.length - p)), .lit (x.take (x.length - q))]) x (q ≤ p) :=
    hOrder.congr (by omega)
  apply (hGuard.guarded (fun hqp => ?_)).congr
    (stripPrefix_length_iff x (pre x a b) p q hp).symm
  have h := interval_obs hm he x (fun c _ => unicodeAlphabet_mem c)
    (x.length - a) (x.length - b) (x.length - p) (x.length - q)
    (by omega) (by omega) (by omega) (by omega)
  rw [spanSlice_pre x a b ha hb, spanSlice_pre x p q hp hqp] at h
  exact (Predicate.of_obs h).congr (pre_literal_iff x a b p q hp hqp).symm

def parameterCandidateBody (order matcher : Nat) : MExp :=
  parameterSuccess order matcher (.param 1) (.param 2) (.param 3) (.param 0)

theorem parameterCandidateBody_firstOrder (order matcher : Nat) :
    (parameterCandidateBody order matcher).FirstOrder :=
  parameterSuccess_firstOrder _ _ trivial trivial trivial trivial

theorem parameterCandidateBody_subst (order matcher : Nat) (q a b p : MExp) :
    MExp.subst [q, a, b, p] (parameterCandidateBody order matcher) =
      parameterSuccess order matcher a b p q := by
  simp [parameterCandidateBody, parameterSuccess, MExp.subst, MExp.substArgs, argAt]

def parameterFailure (search : Nat) (a b p : MExp) : MExp :=
  .notP (.call search [.lit [], a, b, p])

theorem parameterFailure_firstOrder (search : Nat) {a b p : MExp}
    (ha : a.FirstOrder) (hb : b.FirstOrder) (hp : p.FirstOrder) :
    (parameterFailure search a b p).FirstOrder := ⟨trivial, ha, hb, hp, trivial⟩

/-- Literal replay has a finite endpoint search. Only this total existence
test is negated to derive explicit parameter failure. -/
theorem captured_failure_test {g : MGrammar} {order equal matcher search candidate : Nat}
    (ho : ruleAtM g.rules order = some ⟨2, leBody order equal⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (hm : ruleAtM g.rules matcher = some ⟨4, intervalBody matcher equal unicodeAlphabet⟩)
    (hs : ruleAtM g.rules search = some ⟨4, existsBody search candidate 3⟩)
    (hc : ruleAtM g.rules candidate = some ⟨4, parameterCandidateBody order matcher⟩)
    (x : List Char) (a b p : Nat) (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) :
    Predicate g .callByValuePar
      (parameterFailure search (.lit (x.take (x.length - a))) (.lit (x.take (x.length - b)))
        (.lit (x.take (x.length - p)))) x
      (Shallot.stripPrefix? (pre x a b) (sfx x p) = none) := by
  let ctx := [x.length - a, x.length - b, x.length - p]
  let P : Nat → Prop := fun j =>
    (Shallot.stripPrefix? (pre x a b) (sfx x p)).map List.length = some (x.length - j)
  have hEach : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call candidate (.lit (x.take j) :: prefixValues x ctx)) x (P j) := by
    intro j hj
    have ht := captured_success_test ho he hm x a b p (x.length - j) ha hb hp (by omega)
    have hv := prefixValues_args g x (j :: ctx)
    simp only [ctx, prefixValues] at hv
    have hIndex : x.length - (x.length - j) = j := by omega
    rw [hIndex] at ht
    constructor
    · intro h
      apply par_call hc rfl hv
      rw [parameterCandidateBody_subst]
      exact ht.1 h
    · intro h
      apply par_call hc rfl hv
      rw [parameterCandidateBody_subst]
      exact ht.2 h
  have hSearch := exists_predicate ctx hs x P hEach 0 (by omega)
  apply hSearch.notP.congr
  constructor
  · intro hn
    cases hRun : Shallot.stripPrefix? (pre x a b) (sfx x p) with
    | none => rfl
    | some rest =>
      have hlen := stripPrefix_length _ _ _ hRun
      rw [length_sfx x hp] at hlen
      apply False.elim
      apply hn
      refine ⟨x.length - rest.length, by omega, by omega, ?_⟩
      simp only [P, hRun, Option.map_some, Option.some.injEq]
      omega
  · intro hRun
    rintro ⟨j, _, _, hj⟩
    simp only [P, hRun, Option.map_none] at hj
    cases hj

theorem parameter_source_success {g source : MGrammar} {order equal matcher : Nat}
    (ho : ruleAtM g.rules order = some ⟨2, leBody order equal⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (hm : ruleAtM g.rules matcher = some ⟨4, intervalBody matcher equal unicodeAlphabet⟩)
    (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char))
    (k a b p q : Nat) (hE : E[k]? = some (pre x a b))
    (ha : a ≤ x.length) (hb : b ≤ a) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    Predicate g .callByValuePar
      (parameterSuccess order matcher
        (.lit (x.take (x.length - a))) (.lit (x.take (x.length - b)))
        (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q)))) x
      (evV source x s T E (.param k) p = some (some q)) := by
  apply (captured_success_test ho he hm x a b p q ha hb hp hq).congr
  simp only [evV, hE]
  cases Shallot.stripPrefix? (pre x a b) (sfx x p) <;> simp

theorem parameter_source_failure {g source : MGrammar} {test : MExp}
    (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char))
    (k : Nat) (w : List Char) (p : Nat) (hE : E[k]? = some w)
    (ht : Predicate g .callByValuePar test x (Shallot.stripPrefix? w (sfx x p) = none)) :
    Predicate g .callByValuePar test x (evV source x s T E (.param k) p = some none) := by
  apply ht.congr
  simp only [evV, hE]
  cases Shallot.stripPrefix? w (sfx x p) <;> simp

theorem parameter_missing_tests (g source : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (k p q : Nat) (hE : E[k]? = none) :
    Predicate g .callByValuePar MExp.failAlways x (evV source x s T E (.param k) p = some (some q)) ∧
    Predicate g .callByValuePar .eps x (evV source x s T E (.param k) p = some none) := by
  constructor
  · constructor
    · intro h
      simp [evV, hE] at h
    · intro _
      exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩
  · constructor
    · intro _
      exact ⟨_, .eps x, rfl⟩
    · intro h
      exact False.elim (h (by simp [evV, hE]))

end Shallot.MacroPeg.CBV.ParSimulation
