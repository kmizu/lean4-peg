import PalPeg.CloseoutAdvanceT

/-!
# `RoundBundle`: the five carried fields that produce `hSP`

`CloseoutPackRun29.ShiftPal` — the `hSP` of `given_chainPackAtAnyState_FALSE_HYP` — now follows
from `CloseoutPackRun31.shiftPal_of_readOrigin`, whose inputs are
`ChainRound`, `canRight s.right` and `H_fresh`.  Keeping `ChainRound` along a
run needs four more single-state fields, each of which is itself a tick
invariant modulo at most one named leaf:

| field | tick theorem | named leaf |
|---|---|---|
| `ChainRound` | `CloseoutNoReplayWatch.chainRound_tick_S` | — (`H_shiftDone` comes from `ShiftRound`) |
| `ReadsRound` | `CloseoutNoReplayWatch.readsRound_tick_S` | `H_readsShift` |
| `ShiftRound` | `CloseoutAdvanceT.shiftRound_tick_A` | `H_freshShift` |
| `PeriodShape` | `CloseoutPeriodShape.periodShape_tick` | — |
| `NoReplayWatch` | `CloseoutNoReplayWatch.noReplayWatch_tick` | — |

`RoundBundle` is the conjunction and `roundBundle_tick` the assembled step, so
the compiler checks the residue claim: **`H_readsShift` and `H_freshShift`**,
plus the two side inputs the main path already carries (`ChainPositionInvariantWithShiftPhase`, and
`CopyIdle`, which the `LPackM` tick family already threads as
`c.mode = Mode.shift → CopyIdle s`).

`shiftPal_of_roundBundle` then produces `hSP` from the bundle, and
`H_freshShift` / `H_fresh` are the same obligation twice: the first shift of a
fresh chain, whose content is `GalilScaffoldTopFirstRound.first_round`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRoundBundle

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutRoundReads PalPeg.CloseoutRoundUnique
open PalPeg.CloseoutPeriodShape PalPeg.CloseoutNoReplayWatch PalPeg.CloseoutAdvanceT

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the five carried fields.** -/
structure RoundBundle (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  chainRound : ChainRound w c s
  readsRound : ReadsRound w c s
  shiftRound : ShiftRound w c s
  periodShape : PeriodShape s
  noReplay : NoReplayWatch c s

/-- **The bundle travels one tick.**  `H_shiftDone` is not an input: it comes
from the bundle's own `ShiftRound` through `h_shiftDone_of_shiftRound`. -/
theorem roundBundle_tick {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hB : RoundBundle w c s)
    (hinv : ChainPositionInvariantWithShiftPhase w c s)
    (hci : c.mode = Mode.shift → CopyIdle s)
    (hSh : H_readsShift w c s)
    (hF : H_freshShift w s t)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    RoundBundle w c' t where
  chainRound :=
    chainRound_tick_S centre place entry q first hB.chainRound hB.readsRound hB.periodShape
      hB.noReplay hinv (h_shiftDone_of_shiftRound centre place entry q first hB.shiftRound) h
  readsRound :=
    readsRound_tick_S centre place entry q first hB.chainRound hB.readsRound hB.periodShape
      hB.noReplay hinv hSh h
  shiftRound :=
    shiftRound_tick_A centre place entry q first (x := ⟨c, s⟩) (y := ⟨c', t⟩)
      hB.chainRound hB.shiftRound hB.readsRound hF
      (blockInv_of_chainPosInv2 hinv) hci h
  periodShape := periodShape_tick centre place entry q first hB.periodShape h
  noReplay := noReplayWatch_tick centre place entry q first hB.noReplay hB.periodShape h

/-- **`ShiftPal` from the bundle.**  This is `hSP`'s producer: the bundle plus
`canRight` of the right head plus the fresh-chain branch. -/
theorem shiftPal_of_roundBundle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hm : c.mode = Mode.scan) (hr : c.replaying = false)
    (hB : RoundBundle w c s)
    (hcan : canRight s.right)
    (hfresh : s.periodOnly = false → ShiftPal centre place entry q first w s) :
    ShiftPal centre place entry q first w s :=
  shiftPal_of_readOrigin centre place entry q first hm hr hB.chainRound hcan hfresh

/-- **The bundle along a run**, on the run-level forms of its two leaves. -/
theorem roundBundle_steps {w : List (Fin 2)} {delay n : ℕ} {x y : State GalilVM}
    (hx : RoundBundle w x.ctl x.vm)
    (hinv : ∀ z : State GalilVM, ChainPositionInvariantWithShiftPhase w z.ctl z.vm)
    (hci : ∀ z : State GalilVM, z.ctl.mode = Mode.shift → CopyIdle z.vm)
    (hSh : ∀ z : State GalilVM, H_readsShift w z.ctl z.vm)
    (hF : ∀ z z' : State GalilVM, H_freshShift w z.vm z'.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) delay n x y) :
    RoundBundle w y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := z
    exact ih (roundBundle_tick centre place entry q first hx (hinv _) (hci _) (hSh _)
      (hF ⟨c, s⟩ ⟨c', t⟩) ht)

end

#print axioms roundBundle_tick
#print axioms shiftPal_of_roundBundle
#print axioms roundBundle_steps

end PalPeg.CloseoutRoundBundle
