import MacroPeg.CBV.PrefixDecrement

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom_cons subst_paramsFrom)

def anyFrom (P : Nat → Bool) (k : Nat) : Nat → Bool
  | 0 => P k
  | d + 1 => P k || anyFrom P (k + 1) d

theorem anyFrom_true_iff (P : Nat → Bool) (k d : Nat) :
    anyFrom P k d = true ↔ ∃ j, k ≤ j ∧ j ≤ k + d ∧ P j = true := by
  induction d generalizing k with
  | zero =>
    simp only [anyFrom]
    constructor
    · intro h
      exact ⟨k, Nat.le_refl _, by omega, h⟩
    · rintro ⟨j, hj, hj', h⟩
      have he : j = k := by omega
      simpa only [he] using h
  | succ d ih =>
    rw [anyFrom, Bool.or_eq_true_iff, ih]
    constructor
    · rintro (h | ⟨j, hj, hj', h⟩)
      · exact ⟨k, Nat.le_refl _, by omega, h⟩
      · exact ⟨j, by omega, by omega, h⟩
    · rintro ⟨j, hj, hj', h⟩
      by_cases he : j = k
      · exact Or.inl (by simpa only [he] using h)
      · exact Or.inr ⟨j, by omega, by omega, h⟩

/-- Test all input positions while preserving a tuple of enclosing counters. -/
def existsBody (self test ctxSize : Nat) : MExp :=
  .alt (.call test (.param 0 :: paramsFrom 1 ctxSize))
    (.seq (.notP (atEnd (.param 0)))
      (.call self (.seq (.param 0) .any :: paramsFrom 1 ctxSize)))

theorem existsBody_firstOrder (self test ctxSize : Nat) :
    (existsBody self test ctxSize).FirstOrder :=
  ⟨⟨trivial, paramsFrom_firstOrder 1 ctxSize⟩,
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, paramsFrom_firstOrder 1 ctxSize⟩⟩

theorem existsBody_subst (self test : Nat) (k : MExp) (ctx : List MExp) :
    MExp.subst (k :: ctx) (existsBody self test ctx.length) =
      .alt (.call test (k :: ctx))
        (.seq (.notP (atEnd k)) (.call self (.seq k .any :: ctx))) := by
  simp [existsBody, atEnd, MExp.andP, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

/-- Exhaustive search is a finite test when the queried position predicates
are finite tests. A missing observation is never treated as a false test. -/
theorem exists_body_obs {g : MGrammar} {self test : Nat} (ctx : List Nat)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 1, existsBody self test ctx.length⟩)
    (x : List Char) (P : Nat → Bool)
    (hP : ∀ j, j ≤ x.length → Test g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x ctx)) x (P j))
    (k : Nat) (hk : k ≤ x.length) :
    Test g .callByValuePar
      (MExp.subst (.lit (x.take k) :: prefixValues x ctx) (existsBody self test ctx.length)) x
      (anyFrom P k (x.length - k)) := by
  have aux : ∀ d k, k + d = x.length →
      Test g .callByValuePar
        (MExp.subst (.lit (x.take k) :: prefixValues x ctx) (existsBody self test ctx.length)) x
        (anyFrom P k d) := by
    intro d
    induction d with
    | zero =>
      intro k he
      have hkn : k = x.length := by omega
      have hctx : ctx.length = (prefixValues x ctx).length := by simp
      rw [hctx, existsBody_subst]
      have hend := end_obs g x k (by omega)
      simp only [if_pos hkn] at hend
      have hFail : SObs g .callByValuePar
          (.seq (.notP (atEnd (.lit (x.take k))))
            (.call self (.seq (.lit (x.take k)) .any :: prefixValues x ctx))) x none :=
        seq_fail (not_ok hend)
      have hTest := hP k (by omega)
      exact (alt_fail_right_iff hFail _).2 hTest
    | succ d ih =>
      intro k he
      have hkn : k < x.length := by omega
      have hctx : ctx.length = (prefixValues x ctx).length := by simp
      rw [hctx, existsBody_subst]
      have hend := end_obs g x k (by omega)
      simp only [if_neg (show k ≠ x.length from by omega)] at hend
      obtain ⟨t, hGrow⟩ := grow_obs g x k hkn
      have hv : DerivesArgsPar g .callByValuePar x
          (.seq (.lit (x.take k)) .any :: prefixValues x ctx)
          (.lit (x.take (k + 1)) :: prefixValues x ctx) :=
        .cons _ _ _ _ _ _ _ hGrow (prefix_eq x (k + 1)) (prefixValues_args g x ctx)
      have hi := ih (k + 1) (by omega)
      have hc := par_call hr (by simp) hv hi
      exact test_alt (hP k (by omega)) (seq_ok (not_fail hend) hc)
  exact aux (x.length - k) k (by omega)

theorem exists_obs {g : MGrammar} {self test : Nat} (ctx : List Nat)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 1, existsBody self test ctx.length⟩)
    (x : List Char) (P : Nat → Bool)
    (hP : ∀ j, j ≤ x.length → Test g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x ctx)) x (P j))
    (k : Nat) (hk : k ≤ x.length) :
    Test g .callByValuePar (.call self (.lit (x.take k) :: prefixValues x ctx)) x
      (anyFrom P k (x.length - k)) := by
  apply par_call hr (by simp) _ (exists_body_obs ctx hr x P hP k hk)
  exact prefixValues_args g x (k :: ctx)

theorem exists_predicate {g : MGrammar} {self test : Nat} (ctx : List Nat)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 1, existsBody self test ctx.length⟩)
    (x : List Char) (P : Nat → Prop) [DecidablePred P]
    (hP : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x ctx)) x (P j))
    (k : Nat) (hk : k ≤ x.length) :
    Predicate g .callByValuePar (.call self (.lit (x.take k) :: prefixValues x ctx)) x
      (∃ j, k ≤ j ∧ j ≤ x.length ∧ P j) := by
  let B : Nat → Bool := fun j => decide (P j)
  have hEach : ∀ j, j ≤ x.length → Test g .callByValuePar
      (.call test (.lit (x.take j) :: prefixValues x ctx)) x (B j) := by
    intro j hj
    simpa only [Test, B, decide_eq_true_eq] using (hP j hj).obs
  have h := exists_obs ctx hr x B hEach k hk
  have ht : Predicate g .callByValuePar
      (.call self (.lit (x.take k) :: prefixValues x ctx)) x
      (anyFrom B k (x.length - k) = true) := Predicate.of_obs h
  apply ht.congr
  rw [anyFrom_true_iff]
  have hN : k + (x.length - k) = x.length := by omega
  simp only [hN, B, decide_eq_true_eq]

end Shallot.MacroPeg.CBV.PrefixCounters
