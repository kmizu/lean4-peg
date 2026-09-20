import PalPeg.HeadBehindRight
import PalPeg.CloseoutVerRep
import PalPeg.CloseoutPackRun48
import PalPeg.GalilLookRefined

/-!
# The lookahead of a watching chain verifier has arrived when that of the right head has

The chain position ledger says `position verifier + lag = position right` with a non-negative
lag, so the verifier stands no further right than the right head, and one place further left
when the lag is positive.  `HeadBehindRight.usedPH_right_le_of_position_le` then bounds the
lookahead of the verifier (one move, or two when the lag is positive) by the letters that bound
the lookahead of the right head.
-/

set_option autoImplicit false

namespace PalPeg.ChainLookBehindRight

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (usedPH)
open PalPeg.GalilLookRefined (lookChain' lagPos_of_value)
open PalPeg.CloseoutVerRep (VerRep verRep_next)
open PalPeg.CloseoutPackRun41 (ChainPositionLedger)
open PalPeg.CloseoutPackRun48 (LagCan)
open PalPeg.HeadBehindRight (usedPH_right_le_of_position_le)

/-- **The lookahead of a watching verifier.** -/
theorem lookChain'_watch_le (raw : List (Fin 2)) (j : ℕ) (wch : GalilScaffoldChainWatch.State)
    (R : GalilScaffoldInputHead.PlaceHead)
    (hverRep : VerRep raw (.watch wch))
    (hledger : ChainPositionLedger (.watch wch) (position R)) (hlag : LagCan (.watch wch))
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (husedVerifier : usedPH raw.length wch.machine.verifier ≤ j)
    (hlookRight : usedPH raw.length (GalilScaffoldChainVerifier.right R) ≤ j) :
    lookChain' raw.length (.watch wch) ≤ j := by
  obtain ⟨hrep, hfocus⟩ := hverRep wch rfl
  obtain ⟨hcanRight, hsane, hsum⟩ := hledger.watch wch rfl
  obtain ⟨hcanonical, hnonneg⟩ := hlag wch rfl
  have hfirst := usedPH_right_le_of_position_le raw j wch.machine.verifier R hrep hsane hR hRs
    (by omega) husedVerifier hlookRight
  show (if GalilScaffoldCounter.positive wch.lag = true then
      usedPH raw.length (GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right wch.machine.verifier))
    else usedPH raw.length (GalilScaffoldChainVerifier.right wch.machine.verifier)) ≤ j
  split
  · rename_i hpositive
    have hbehind := lagPos_of_value wch (position R) hcanonical hsum hpositive
    obtain ⟨hrepNext, _⟩ := verRep_next hrep hfocus hcanRight
    obtain ⟨hposNext, hsaneNext⟩ := GalilFrontMono.right_sane hcanRight hsane
    exact usedPH_right_le_of_position_le raw j _ R hrepNext hsaneNext hR hRs (by omega) hfirst
      hlookRight
  · exact hfirst

#print axioms lookChain'_watch_le

end PalPeg.ChainLookBehindRight
