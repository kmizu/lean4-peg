import PalPeg.CloseoutPackRun38
import PalPeg.CloseoutShiftS
import PalPeg.CloseoutShiftDoneP

/-!
# The three branch hypotheses, re-cut through `CloseoutPackRun38`

`CloseoutShiftS.chainPosInv_steps` runs `ChainPositionInvariant` along a run modulo
`CloseoutPackRun34`'s three named branch hypotheses.  `CloseoutPackRun38` already
decomposes all three:

| Run34 hypothesis | Run38 producer | residue |
|---|---|---|
| `H_BackgroundLandingPayload` | `posPayload_background` (:157) | `H_bgRes` |
| `H_MatchLandingPayload` | `posPayload_match` (:220) | `H_matchRes` |
| `H_ShiftExitPayload` | `posPayload_shiftDone` (:314) | `H_shiftDoneRes` (identity) |

`H_bgRes` and `H_matchRes` are genuine progress: they split the payload into
`SrcPos` (the chain-side ledger, which `step_pos` (:76) transports across one
`ChainStep`), a `start` clause for the idle case, and `verNext`.
`H_shiftDoneRes` is `H_ShiftExitPayload` itself — Run38 records that nothing in
`ChainPositionInvariant` reaches across `shift` mode — and `CloseoutShiftDoneP` gives its
real split (`canR`/`radLe` free from `ShiftGeom`, `ChainSideAt` named).

This file wires the three producers to the run, so `shiftLocalS_of_run` and
everything above it depend on the **residues**, not on Run34's hypotheses.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutBranchRes

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun38
open PalPeg.CloseoutShiftS PalPeg.CloseoutShiftDoneP

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ChainPositionInvariant` along a run from the three residues.** -/
theorem chainPosInv_steps_res {w : List (Fin 2)}
    (hbg : H_bgRes centre place entry q first w)
    (hmatch : H_matchRes centre place entry q first w)
    (hsd : H_shiftDoneRes centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPositionInvariant w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ChainPositionInvariant w y.ctl y.vm :=
  chainPosInv_steps centre place entry q first
    (posPayload_background centre place entry q first hbg)
    (posPayload_match centre place entry q first hmatch)
    (posPayload_shiftDone centre place entry q first hsd) hx h

/-- **`ShiftLocalS` at every state of a run, from the residues.** -/
theorem shiftLocalS_of_run_res {w : List (Fin 2)}
    (hfour : H_FourSemiperiodsLeDistance centre place entry q first w)
    (hbg : H_bgRes centre place entry q first w)
    (hmatch : H_matchRes centre place entry q first w)
    (hsd : H_shiftDoneRes centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPositionInvariant w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ShiftLocalS centre place entry q first w y :=
  shiftLocalS_of_chainPosInv centre place entry q first hfour
    (chainPosInv_steps_res centre place entry q first hbg hmatch hsd hx h)

#print axioms chainPosInv_steps_res
#print axioms shiftLocalS_of_run_res

end

end PalPeg.CloseoutBranchRes
