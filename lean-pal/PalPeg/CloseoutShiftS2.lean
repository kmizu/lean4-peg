import PalPeg.CloseoutPackRun48
import PalPeg.CloseoutShiftS

/-!
# `ShiftLocalS` along a run through `ChainPosInv2`

`CloseoutShiftS` wired `CloseoutPackRun34`'s `ChainPosInv` to a run, leaving
four named branch hypotheses (`H_fourOther`, `H_bgP`, `H_matchP`,
`H_shiftDoneP`).  But `CloseoutPackRun41` and `CloseoutPackRun48` are **further
along** and were never wired:

* `CloseoutPackRun41.ChainPosInv2` closes the chain half under `ChainStep` and
  `ChainMatched` on its own (`chainPos_step` / `chainPos_matched`), so Run38's
  one-tick lookahead is gone; `shift_one` closes outright in
  `chainPosInv2_tick` (:§4).
* `CloseoutPackRun41.watchShiftS_of_chainPosInv2` produces `WatchShiftS` with
  **no `H_fourOther`** — the target's verifier pair comes from `chainPos_step`,
  since an unmatched comparison's chain effect is a plain `ChainStep`.
* `CloseoutPackRun48` discharges all four of `chainPosInv2_tick`'s branch
  hypotheses: `h_bgP2_of_supply` (:163), `h_matchP2_of_target` (:243),
  `h_shiftEntry2_of_target` (:374), `h_shiftDoneRad2_of_supply` (:446).

This file runs `ChainPosInv2` along a run and reads `ShiftLocalS` off it, so the
`hfour` hypothesis of `CloseoutShiftS.shiftLocalS_of_run` disappears.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftS2

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun41
open PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47 PalPeg.CloseoutPackRun48
open PalPeg.CloseoutShiftS

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ChainPosInv2` along a run.** -/
theorem chainPosInv2_steps {w : List (Fin 2)}
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv2 w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ChainPosInv2 w y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    exact ih (chainPosInv2_tick centre place entry q first hbg hmatch hentry hsd hx ht)

/-- **`ShiftLocalS` from `ChainPosInv2`, with no `H_fourOther`.** -/
theorem shiftLocalS_of_chainPosInv2 {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainPosInv2 w x.ctl x.vm) (hav : ConsumeAvail x.vm.chain) :
    ShiftLocalS centre place entry q first w x := by
  by_cases hi : x.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hi
  · exact shiftLocalS_of_watchShiftS centre place entry q first hi
      (watchShiftS_of_chainPosInv2 centre place entry q first h hav)

/-- **`ShiftLocalS` at every state of a run, through `ChainPosInv2`.** -/
theorem shiftLocalS_of_run2 {w : List (Fin 2)}
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv2 w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hav : ConsumeAvail y.vm.chain) :
    ShiftLocalS centre place entry q first w y :=
  shiftLocalS_of_chainPosInv2 centre place entry q first
    (chainPosInv2_steps centre place entry q first hbg hmatch hentry hsd hx h) hav

#print axioms chainPosInv2_steps
#print axioms shiftLocalS_of_chainPosInv2
#print axioms shiftLocalS_of_run2

end

end PalPeg.CloseoutShiftS2
