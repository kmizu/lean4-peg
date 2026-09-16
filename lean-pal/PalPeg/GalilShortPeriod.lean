import PalPeg.GalilPeriodCentre
import PalPeg.GalilPeriodUnion

/-!
# Minimal periods survive the centre shift

Word combinatorics for the restart step of Galil's real-time matcher.

* `no_short_period_drop`: a palindrome of length `≥ 3p` with minimal period `p`
  keeps that minimality on its suffix `x.drop p`.
* `hasPeriod_take_drop` / `hasPeriod_drop_drop`: a period of a span restricts to
  sub-spans (prefixes and suffixes of the window).
* `no_short_period_shift`: the centred form used by the machine — shifting the
  centre of `PalAt x C k` by `h` (with span period `2h`, no shorter span period,
  and `3h ≤ k`) preserves the absence of periods below `2h`.
-/

set_option autoImplicit false
namespace PalPeg
open Manacher

variable {α : Type}

/-! ## Minimality transfers to the shifted span -/

/-- If a palindrome `x` has period `p`, no period below `p`, and length at least `3p`,
then its suffix `x.drop p` (a palindrome) has no period below `p` either. -/
theorem no_short_period_drop {x : List α} {p : ℕ} (hx : IsPal x) (hxp : HasPeriod x p) (hp : 0 < p)
    (hlen : 3 * p ≤ x.length) (hmin : ∀ q, 0 < q → q < p → ¬ HasPeriod x q) :
    ∀ q, 0 < q → q < p → ¬ HasPeriod (x.drop p) q := by
  have hpn : p ≤ x.length := by omega
  have hyPal : IsPal (x.drop p) := isPal_drop_of_hasPeriod hx hpn hxp
  have hy : x.drop p = x.drop (x.length - (x.length - p)) := by
    exact congrArg (fun m => x.drop m) (by omega)
  exact hasPeriod_minimal_of_suffix hx hxp hp hpn hmin hy (by omega) (by omega) hyPal

/-! ## Periods restrict to sub-spans -/

/-- A period of the window `x[a .. a+n)` is a period of the shorter window `x[a .. a+m)`. -/
theorem hasPeriod_take_drop {x : List α} {p a n m : ℕ} (h : HasPeriod ((x.drop a).take n) p)
    (hm : m ≤ n) : HasPeriod ((x.drop a).take m) p := by
  have h' : HasPeriod (((x.drop a).take n).take m) p := hasPeriod_take h
  rwa [List.take_take, show min m n = m from Nat.min_eq_left hm] at h'

/-- A period of the window `x[a .. a+n)` is a period of the window `x[a+d .. a+n)`. -/
theorem hasPeriod_drop_drop {x : List α} {p a n d : ℕ} (h : HasPeriod ((x.drop a).take n) p)
    (hd : d ≤ n) : HasPeriod ((x.drop (a + d)).take (n - d)) p := by
  have h' : HasPeriod (((x.drop a).take n).drop d) p := hasPeriod_drop h
  rwa [drop_take_drop hd] at h'

/-! ## The centred form -/

/-- Centred version of `no_short_period_drop`: if the span of `PalAt x C k` has period `2h`,
no period below `2h`, and `3h ≤ k`, then the shifted span (centre `C+h`, radius `k-h`)
has no period below `2h` either. -/
theorem no_short_period_shift {x : List α} {C k h : ℕ} (hpal : PalAt x C k) (hh : 0 < h)
    (hk : 3 * h ≤ k)
    (hper : HasPeriod ((x.drop (C - k)).take (2 * k + 1)) (2 * h))
    (hmin : ∀ q, 0 < q → q < 2 * h → ¬ HasPeriod ((x.drop (C - k)).take (2 * k + 1)) q) :
    ∀ q, 0 < q → q < 2 * h → ¬ HasPeriod ((x.drop (C + h - (k - h))).take (2 * (k - h) + 1)) q := by
  have hkC : k ≤ C := hpal.1
  have hS : IsPal ((x.drop (C - k)).take (2 * k + 1)) := isPal_span_of_palAt hpal
  have hSlen := length_span_of_palAt hpal
  have hlen : 3 * (2 * h) ≤ ((x.drop (C - k)).take (2 * k + 1)).length := by rw [hSlen]; omega
  have hshift := no_short_period_drop hS hper (by omega) hlen hmin
  have e : (x.drop (C + h - (k - h))).take (2 * (k - h) + 1)
      = ((x.drop (C - k)).take (2 * k + 1)).drop (2 * h) := by
    rw [drop_take_drop (show 2 * h ≤ 2 * k + 1 by omega),
      show C - k + 2 * h = C + h - (k - h) from by omega,
      show 2 * k + 1 - 2 * h = 2 * (k - h) + 1 from by omega]
  rw [e]
  exact hshift

#print axioms no_short_period_drop
#print axioms hasPeriod_take_drop
#print axioms hasPeriod_drop_drop
#print axioms no_short_period_shift

end PalPeg
