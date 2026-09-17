import PalPeg.CloseoutPackRun34
import PalPeg.CloseoutFrontExtra

/-!
# `ShiftLocalS` along a run, from `ChainPosInv`

`CloseoutPackRun32` found `WatchShiftG` false at unguarded comparison targets
(a watch born at `ChainStep.backDone` has `distance = reset`), and
`CloseoutPackRun34` built the guarded replacements — `WatchShiftS`,
`ShiftLocalS`, `ChainPosInv`, `watchShiftS_of_chainPosInv`, `chainPosInv_tick`
(20 of 23 tick shapes closed) — but never wired them to a run.

This file does the wiring: `ChainPosInv` travels along a run by
`chainPosInv_tick`, and at each state it yields `ShiftLocalS` through
`watchShiftS_of_chainPosInv` and `shiftLocalS_of_watchShiftS`, with the idle
branch free (`shiftLocalS_of_chainIdle`).

The residue is exactly `CloseoutPackRun34`'s four named branch hypotheses
(`H_fourOther`, `H_bgP`, `H_matchP`, `H_shiftDoneP`) plus the entry
`ChainPosInv`, in place of the **false** `∀ y, WatchShiftG … y`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftS

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ShiftLocalS` from `ChainPosInv`.**  The idle branch is free; the watching
branch goes through the guarded `WatchShiftS`. -/
theorem shiftLocalS_of_chainPosInv {w : List (Fin 2)}
    (hfour : H_fourOther centre place entry q first w) {x : State GalilVM}
    (h : ChainPosInv w x.ctl x.vm) : ShiftLocalS centre place entry q first w x := by
  by_cases hi : x.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hi
  · exact shiftLocalS_of_watchShiftS centre place entry q first hi
      (watchShiftS_of_chainPosInv centre place entry q first hfour h)

/-- **`ChainPosInv` along a run.** -/
theorem chainPosInv_steps {w : List (Fin 2)}
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ChainPosInv w y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    exact ih (chainPosInv_tick centre place entry q first hbg hmatch hsd hx ht)

/-- **`ShiftLocalS` at every state of a run.**  This is what replaces the false
`∀ y, WatchShiftG … y` on the main path. -/
theorem shiftLocalS_of_run {w : List (Fin 2)}
    (hfour : H_fourOther centre place entry q first w)
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ShiftLocalS centre place entry q first w y :=
  shiftLocalS_of_chainPosInv centre place entry q first hfour
    (chainPosInv_steps centre place entry q first hbg hmatch hsd hx h)

#print axioms shiftLocalS_of_chainPosInv
#print axioms chainPosInv_steps
#print axioms shiftLocalS_of_run

end

end PalPeg.CloseoutShiftS
