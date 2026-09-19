import PalPeg.PeriodAcrossBreak
import PalPeg.CanonicalSearchProgram

/-!
# `LowerExcluded` for the lower bound a broken restart installs

At a lag-zero break the old chain has verified period `2h` on the scan span of radius `d`, that
period is minimal there, and the place `C + d + 1` breaks it.  The restart installs
`lower := last` with `last + h ≤ d`.  A span that can hold a candidate above `last` has radius
`k ≥ 4 (last + 1) ≥ d + 1`, so it contains the break, and `no_period_across_break` excludes every
period `2δ` with `δ ≤ last`.
-/

set_option autoImplicit false

namespace PalPeg.LowerExcludedAtBreak

open PalPeg PalPeg.CanonicalSearchProgram GalilScaffoldChainInputSupply

theorem lowerExcluded_of_break {raw : List (Fin 2)} {C d h last : ℕ}
    (hpalOld : Manacher.PalAt (encoded raw) C d)
    (hperiodOld : PeriodOn (encoded raw) (2*h) (C - d) (C + d))
    (hminimalOld : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span raw C d) p)
    (hbreak : (encoded raw)[C + d + 1 - 2*h]? ≠ (encoded raw)[C + d + 1]?)
    (hh0 : 0 < h) (hhd : 2*h ≤ d) (hlast : last + h ≤ d) (hcover : d + 1 ≤ 4*(last+1)) :
    LowerExcluded raw C last := by
  intro k hkC hpal hk δ hδ0 hδ hper
  have hdC : d ≤ C := hpalOld.1
  have hkC' : k ≤ C := hpal.1
  have hlen : C + k < (encoded raw).length := hpal.2.1
  -- the candidate period on the index interval of the large span
  have hperOn : PeriodOn (encoded raw) (2*δ) (C - k) (C + k) := by
    unfold Span at hper
    rw [show 2*k+1 = (C+k)+1-(C-k) from by omega] at hper
    exact (hasPeriod_slice_iff (x := encoded raw) (p := 2*δ) hlen (by omega)).mp hper
  have hminimalOn : ∀ r, 0 < r → r < 2*h → ¬ PeriodOn (encoded raw) r (C - d) (C + d) := by
    intro r hr0 hr2 hon
    apply hminimalOld r hr0 hr2
    unfold Span
    rw [show 2*d+1 = (C+d)+1-(C-d) from by omega]
    exact (hasPeriod_slice_iff (x := encoded raw) (p := r) hpalOld.2.1 (by omega)).mpr hon
  exact no_period_across_break (j := C + d + 1 - 2*h) hperiodOld hminimalOn
    (hperOn.mono (by omega) (le_refl _)) (by omega) (by omega) (by omega) hlen (by omega)
    (by omega) (by omega) (by omega)
    (by rw [show C + d + 1 - 2*h + 2*h = C + d + 1 from by omega]; exact hbreak)

end PalPeg.LowerExcludedAtBreak
