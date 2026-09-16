import PalPeg.GalilMoveLemma

/-!
# Periods and centre shifts of a palindromic span

Word combinatorics for the centre bookkeeping of Galil's real-time matcher.

* The suffix mirror images of `hasPeriod_of_isPal_take` / `isPal_take_of_hasPeriod`
  (`hasPeriod_of_isPal_drop`, `isPal_drop_of_hasPeriod`).
* The span `x[C-k .. C+k]` of a centred palindrome `PalAt x C k`, as a list
  (`isPal_span_of_palAt`, `palAt_of_isPal_span`).
* Two palindromes with the same right end give a period of the span
  (`span_hasPeriod_of_two_palAt`); a period of the span shifts the centre
  (`palAt_shift_of_period`).
* Hence no live centre sits strictly between `C` and `C+h` when `2h` is below the
  minimal period of the span (`no_centre_below_period`).
-/

set_option autoImplicit false
namespace PalPeg
open Manacher

variable {α : Type}

/-! ## Suffix versions of the move lemma -/

/-- A palindromic suffix of a palindrome yields the drop amount as a period.
Mirror image of `hasPeriod_of_isPal_take`. -/
theorem hasPeriod_of_isPal_drop {x : List α} (hx : IsPal x) {k : ℕ} (hk : k ≤ x.length)
    (hy : IsPal (x.drop k)) : HasPeriod x k := by
  have e : x.length - (x.length - k) = k := by omega
  have h := isPal_drop_iff (x := x) (k := x.length - k) hx (Nat.sub_le _ _)
  rw [e] at h
  rw [hasPeriod_iff_drop_eq_take hk]
  exact (h.mp hy).symm

/-- Conversely, a period `p` of a palindrome makes its suffix after `p` a palindrome.
Mirror image of `isPal_take_of_hasPeriod`. -/
theorem isPal_drop_of_hasPeriod {x : List α} (hx : IsPal x) {p : ℕ} (hp : p ≤ x.length)
    (hper : HasPeriod x p) : IsPal (x.drop p) := by
  have e : x.length - (x.length - p) = p := by omega
  have h := isPal_drop_iff (x := x) (k := x.length - p) hx (Nat.sub_le _ _)
  rw [e] at h
  exact h.mpr ((hasPeriod_iff_drop_eq_take hp).mp hper).symm

/-! ## Spans -/

/-- Dropping inside a window: `((x.drop a).take m).drop n = (x.drop (a+n)).take (m-n)`. -/
theorem drop_take_drop {x : List α} {a m n : ℕ} (hn : n ≤ m) :
    ((x.drop a).take m).drop n = (x.drop (a + n)).take (m - n) := by
  have e : a + n + (m - n) = a + m := by omega
  rw [List.take_drop, List.drop_drop, List.take_drop, e]

/-- The span `x[C-k .. C+k]` of `PalAt x C k` has length exactly `2k+1`. -/
theorem length_span_of_palAt {x : List α} {C k : ℕ} (h : PalAt x C k) :
    ((x.drop (C - k)).take (2 * k + 1)).length = 2 * k + 1 := by
  have hkC : k ≤ C := h.1
  have hlt : C + k < x.length := h.2.1
  simp only [List.length_take, List.length_drop]
  omega

/-- The span `x[C-k .. C+k]` of `PalAt x C k` is a palindrome (as a list). -/
theorem isPal_span_of_palAt {x : List α} {C k : ℕ} (h : PalAt x C k) :
    IsPal ((x.drop (C - k)).take (2 * k + 1)) := by
  obtain ⟨hkC, hlt, hsym⟩ := h
  have hlen : ((x.drop (C - k)).take (2 * k + 1)).length = 2 * k + 1 := by
    simp only [List.length_take, List.length_drop]; omega
  rw [isPal_iff_getElem?, hlen]
  intro i hi
  rw [getElem?_take_drop hi, getElem?_take_drop (show 2 * k + 1 - 1 - i < 2 * k + 1 by omega)]
  rcases Nat.le_total i k with hik | hik
  · have hs := hsym (k - i) (by omega)
    rw [show C - (k - i) = C - k + i from by omega,
      show C + (k - i) = C - k + (2 * k + 1 - 1 - i) from by omega] at hs
    exact hs
  · have hs := hsym (i - k) (by omega)
    rw [show C - (i - k) = C - k + (2 * k + 1 - 1 - i) from by omega,
      show C + (i - k) = C - k + i from by omega] at hs
    exact hs.symm

/-- Conversely a palindromic span of odd length `2k+1` starting at `C-k`
(with `k ≤ C`, `C+k < |x|`) is `PalAt x C k`. -/
theorem palAt_of_isPal_span {x : List α} {C k : ℕ} (hk : k ≤ C) (hlen : C + k < x.length)
    (h : IsPal ((x.drop (C - k)).take (2 * k + 1))) : PalAt x C k := by
  have hslen : ((x.drop (C - k)).take (2 * k + 1)).length = 2 * k + 1 := by
    simp only [List.length_take, List.length_drop]; omega
  rw [isPal_iff_getElem?, hslen] at h
  refine ⟨hk, hlen, ?_⟩
  intro i hi
  have hs := h (k - i) (by omega)
  rw [getElem?_take_drop (show k - i < 2 * k + 1 by omega),
    getElem?_take_drop (show 2 * k + 1 - 1 - (k - i) < 2 * k + 1 by omega)] at hs
  rw [show C - k + (k - i) = C - i from by omega,
    show C - k + (2 * k + 1 - 1 - (k - i)) = C + i from by omega] at hs
  exact hs

/-! ## Two palindromes with the same right end -/

/-- `PalAt x C k` and `PalAt x c (C+k-c)` with `C ≤ c ≤ C+k` (same right end `C+k`):
the span has period `2(c-C)`. -/
theorem span_hasPeriod_of_two_palAt {x : List α} {C k c : ℕ} (h1 : PalAt x C k)
    (h2 : PalAt x c (C + k - c)) (hc : C ≤ c) (hck : c ≤ C + k) :
    HasPeriod ((x.drop (C - k)).take (2 * k + 1)) (2 * (c - C)) := by
  have hkC : k ≤ C := h1.1
  have hlt : C + k < x.length := h1.2.1
  have hS : IsPal ((x.drop (C - k)).take (2 * k + 1)) := isPal_span_of_palAt h1
  have hSlen := length_span_of_palAt h1
  have h2span : IsPal ((x.drop (c - (C + k - c))).take (2 * (C + k - c) + 1)) :=
    isPal_span_of_palAt h2
  have e1 : C - k + 2 * (c - C) = c - (C + k - c) := by omega
  have e2 : 2 * k + 1 - 2 * (c - C) = 2 * (C + k - c) + 1 := by omega
  have e : ((x.drop (C - k)).take (2 * k + 1)).drop (2 * (c - C))
      = (x.drop (c - (C + k - c))).take (2 * (C + k - c) + 1) := by
    rw [drop_take_drop (show 2 * (c - C) ≤ 2 * k + 1 by omega), e1, e2]
  refine hasPeriod_of_isPal_drop hS (by rw [hSlen]; omega) ?_
  rw [e]
  exact h2span

/-- If the span of `PalAt x C k` has period `2h` with `h ≤ k`, then `C+h` is the centre of a
palindrome of radius `k-h` with the same right end. -/
theorem palAt_shift_of_period {x : List α} {C k h : ℕ} (hpal : PalAt x C k) (hh : h ≤ k)
    (hper : HasPeriod ((x.drop (C - k)).take (2 * k + 1)) (2 * h)) : PalAt x (C + h) (k - h) := by
  have hkC : k ≤ C := hpal.1
  have hlt : C + k < x.length := hpal.2.1
  have hS : IsPal ((x.drop (C - k)).take (2 * k + 1)) := isPal_span_of_palAt hpal
  have hSlen := length_span_of_palAt hpal
  have hdrop : IsPal (((x.drop (C - k)).take (2 * k + 1)).drop (2 * h)) :=
    isPal_drop_of_hasPeriod hS (by rw [hSlen]; omega) hper
  have e1 : C - k + 2 * h = C + h - (k - h) := by omega
  have e2 : 2 * k + 1 - 2 * h = 2 * (k - h) + 1 := by omega
  rw [drop_take_drop (show 2 * h ≤ 2 * k + 1 by omega), e1, e2] at hdrop
  exact palAt_of_isPal_span (by omega) (by omega) hdrop

/-- No live centre strictly between `C` and `C+h` when every period below `2h` is excluded:
a palindrome with the same right end and centre `c > C` forces `C + h ≤ c`. -/
theorem no_centre_below_period {x : List α} {C k c h : ℕ} (h1 : PalAt x C k)
    (h2 : PalAt x c (C + k - c)) (hc : C < c) (hck : c ≤ C + k)
    (hmin : ∀ p, 0 < p → p < 2 * h → ¬ HasPeriod ((x.drop (C - k)).take (2 * k + 1)) p) :
    C + h ≤ c := by
  by_contra hcon
  have hlt : c < C + h := by omega
  exact hmin (2 * (c - C)) (by omega) (by omega)
    (span_hasPeriod_of_two_palAt h1 h2 (Nat.le_of_lt hc) hck)

#print axioms hasPeriod_of_isPal_drop
#print axioms isPal_drop_of_hasPeriod
#print axioms drop_take_drop
#print axioms length_span_of_palAt
#print axioms isPal_span_of_palAt
#print axioms palAt_of_isPal_span
#print axioms span_hasPeriod_of_two_palAt
#print axioms palAt_shift_of_period
#print axioms no_centre_below_period

end PalPeg
