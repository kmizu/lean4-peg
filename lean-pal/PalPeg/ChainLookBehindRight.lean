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

/-- **The lookahead of the chain verifier has arrived when that of the right head has**, for
every form of the chain.  An idle chain looks at nothing; a copying or broken chain looks at the
place its verifier stands on, whose letters have been used; a watching chain is
`lookChain'_watch_le`.  For a chain walking back, `VerRep` and `LagCan` say nothing (they speak of
watching chains only), so the representation of its verifier and the sign of its lag are asked
for here. -/
theorem lookChain'_le (raw : List (Fin 2)) (j : ℕ) (z : ChainVM)
    (R : GalilScaffoldInputHead.PlaceHead)
    (hverRep : VerRep raw z) (hledger : ChainPositionLedger z (position R)) (hlag : LagCan z)
    (hbackRep : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : GalilScaffoldCounter.Counter)
      (ver : GalilScaffoldInputHead.PlaceHead), z = .back v h lag margin ver →
      GalilScaffoldInputTrace.Represents ver.head raw ∧ 0 ≤ GalilScaffoldCounter.value lag)
    (hR : GalilScaffoldInputTrace.Represents R.head raw) (hRs : GalilFrontMono.Sane R)
    (husedChain : PalPeg.GalilThrottledRun.usedChain raw.length z ≤ j)
    (hlookRight : usedPH raw.length (GalilScaffoldChainVerifier.right R) ≤ j) :
    lookChain' raw.length z ≤ j := by
  cases z with
  | idle => exact Nat.zero_le _
  | copy t h p v lag margin ver => exact husedChain
  | back v h lag margin ver =>
    obtain ⟨hrep, hnonneg⟩ := hbackRep v h lag margin ver rfl
    obtain ⟨_, hsane, hsum⟩ := hledger.back v h lag margin ver rfl
    exact usedPH_right_le_of_position_le raw j ver R hrep hsane hR hRs (by omega) husedChain
      hlookRight
  | watch wch =>
    exact lookChain'_watch_le raw j wch R hverRep hledger hlag hR hRs husedChain hlookRight
  | broken wch => exact husedChain

#print axioms lookChain'_le

end PalPeg.ChainLookBehindRight
