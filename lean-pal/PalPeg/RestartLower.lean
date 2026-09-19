import PalPeg.RestartCertificate
import PalPeg.LowerExcludedAtBreak

/-!
# The lower bound installed by a broken restart

The inputs of `LowerExcludedAtBreak.lowerExcluded_of_break`, read off the verified window of the
watch that breaks: the period of the whole scan span and the one-place mismatch.
-/

set_option autoImplicit false

namespace PalPeg.RestartLower

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.ShiftPalAlongTrace PalPeg.GalilReplaySpan PalPeg.GalilReplayGeneral2
open PalPeg.RestartBoundary PalPeg.LowerExcludedAtBreak

/-- The verifier of a lag-zero watch stands on the right scan head. -/
theorem verifier_at_right {raw : List (Fin 2)} {cen₀ P : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ P cc b xs (.watch w)) (hzero : zero w.lag = true) :
    position w.machine.verifier = P := by
  obtain ⟨⟨-, hposition⟩, -, -⟩ := hwindow
  have hlagEmpty : w.lag.pos = [] := by
    rcases hw : w.lag with ⟨pos, neg⟩
    rw [hw] at hzero
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hzero
    exact hzero.1
  rw [hlagEmpty] at hposition
  simpa using hposition

/-- The whole scan span of a caught-up watch has period `2h`. -/
theorem spanPeriod_of_window {raw : List (Fin 2)} {cen₀ C d m : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ (C + d) cc b xs (.watch w)) (hzero : zero w.lag = true)
    (hcentre : (encoded raw)[cen₀]? = some cc) (hk : C = cen₀ + m * (xs.length + 1))
    (hpal : Manacher.PalAt (encoded raw) C d) (hhd : 2 * (xs.length + 1) ≤ d) :
    PeriodOn (encoded raw) (2 * (xs.length + 1)) (C - d) (C + d) := by
  have hverifier := verifier_at_right hwindow hzero
  obtain ⟨-, hblock, -⟩ := hwindow
  rw [hverifier] at hblock
  have hlen : C + d < (encoded raw).length := hpal.2.1
  have hfromCentre : PeriodOn (encoded raw) (2 * (xs.length + 1)) cen₀ (C + d) :=
    periodOn_extend_left (periodOn_of_blockOn hblock)
      (by rw [hcentre, block_last_of_blockOn hblock (by omega)])
  have hblockPal := palAt_block_periodic hblock hcentre hlen m (by omega)
  rw [← hk] at hblockPal
  exact periodOn_span_of_halves hpal hhd (hfromCentre.mono (by omega) (le_refl _)) hblockPal

/-- The place a lag-zero break reads differs from the place two semiperiods back. -/
theorem break_mismatch_of_window {raw : List (Fin 2)} {cen₀ P : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w w' : GalilScaffoldChainWatch.State}
    (hwindow : WatchWindow raw cen₀ P cc b xs (.watch w))
    (hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ P + 1) (hbreak : BreakStep w w') :
    (encoded raw)[P + 1 - 2 * (xs.length + 1)]? ≠ (encoded raw)[P + 1]? := by
  intro heq
  have hback : P + 1 - 2 * (xs.length + 1) + 2 * (xs.length + 1) = P + 1 := by omega
  exact not_breakStep_of_text (leftPlace := P + 1 - 2 * (xs.length + 1)) hwindow hsize
    (by rw [hback]; exact heq) (by rw [hback]; exact heq) heq hbreak

end PalPeg.RestartLower
