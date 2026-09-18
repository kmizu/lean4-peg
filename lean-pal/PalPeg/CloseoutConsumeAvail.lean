import PalPeg.CloseoutShiftS2
import PalPeg.CloseoutFrontExtra

/-!
# `ConsumeAvail` from the run, not as a hypothesis

`CloseoutPackRun41` §2 identifies `ConsumeAvail` as the one genuinely non-local
residue of the chain payload: a `take`/`immediate` consume moves the verifier,
and `canRight` of the *moved* verifier is an input-supply fact.

`CloseoutPackRun47.consumeAvail_of_next_supply` turns it into four local facts
about the **next right-head cell**: `Represents`, `focus ≠ none`, `canRight` and
`position R' = position R + 1`, plus `LagNonneg` and `ChainPositionLedger`.  The last two
are inside `ChainPositionInvariantWithShiftPhase`; the first four are exactly what
`CloseoutCanRightBound.canRight_next_of_bound` (wave 5) produces from a position
bound.

So `ConsumeAvail` is supplied by the run's own position budget.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutConsumeAvail

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44
open PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutCanRightBound PalPeg.CloseoutFrontExtra

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ConsumeAvail` at a scan state, from the position budget.**  The four
head facts about the next cell come from `Represents` on the current one plus
the bound; `LagNonneg` and `ChainPositionLedger` come from `ChainPositionInvariantWithShiftPhase`. -/
theorem consumeAvail_of_bound {w : List (Fin 2)} {c : Control} {s : GalilVM} {m : ℕ}
    (hx : ChainPositionInvariantWithShiftPhase w c s) (hs : ScanNR ⟨c, s⟩) (hni : s.chain ≠ ChainVM.idle)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hrepN : GalilScaffoldInputTrace.Represents (right s.right).head w)
    (hfocN : (right s.right).head.focus ≠ none)
    (hstep : position (right s.right) = position s.right + 1)
    (hlag : LagNonneg s.chain)
    (hlv : 0 < s.right.head.left.length)
    (hm1 : 1 ≤ m) (hmlt : m < w.length) (hpos : position s.right ≤ 2 * m - 1) :
    ConsumeAvail s.chain := by
  have P := hx.payload hs hni
  exact consumeAvail_of_next_supply hrepN hfocN
    (canRight_next_of_bound hrepN hfocN P.canR hlv hm1 hmlt hpos) hstep
    hrepV hlag P.chainPos

#print axioms consumeAvail_of_bound

end

end PalPeg.CloseoutConsumeAvail
