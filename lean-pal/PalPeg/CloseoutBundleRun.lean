import PalPeg.CloseoutReadsOrigin

/-!
# The round bundle along a run, with the hypotheses quantified over the run

`CloseoutRoundBundle.roundBundle_steps` threads `RoundBundle` along a run, but
its side inputs are quantified over **every** state:

```
(hinv : ∀ z : State GalilVM, ChainPositionInvariantWithShiftPhase w z.ctl z.vm)
(hci  : ∀ z : State GalilVM, CopyIdle z.vm)
```

Those are the same defect `CloseoutPackRefute` found in `hpack`: `CopyIdle` and
`ChainPositionInvariantWithShiftPhase` are properties of the states a run reaches, not of all states, so
as written the hypotheses are unusable (and, for `CopyIdle`, false — a state
mid-copy has `remainingPos`).

`roundBundle_steps_run` below is the same induction with every side input
quantified over the run's own states, which is the shape
`CloseoutMarksFree.MarksRun` and `CloseoutVerSide.VerRun` already use.  The
re-indexing is `Steps.succ ht`.

`roundBundle_of_idle` is the base case: at an idle chain all five fields are
vacuous or `_of_idle`, so the bundle holds at the `InvLPC` origin of every
cycle — which is exactly where `packRunR_MW` starts.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutBundleRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37 PalPeg.CloseoutPackRun41
open PalPeg.CloseoutRoundReads PalPeg.CloseoutRoundUnique
open PalPeg.CloseoutPeriodShape PalPeg.CloseoutNoReplayWatch
open PalPeg.CloseoutRoundBundle
open PalPeg.CloseoutPackRun29
open PalPeg.CloseoutBirthFree
open PalPeg.CloseoutAdvanceT
open PalPeg.CloseoutPackRun2
open PalPeg.GalilBranchInvariants

/-- **The bundle at an idle chain.**  `ChainRound` / `ReadsRound` / `ShiftRound`
all quantify over a *watching* chain, so they are vacuous; `PeriodShape` and
`NoReplayWatch` have their own `_of_idle`. -/
theorem roundBundle_of_idle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hi : s.chain = ChainVM.idle) : RoundBundle w c s where
  chainRound := fun _ _ _ wch hw => by rw [hi] at hw; cases hw
  readsRound := fun _ _ _ wch hw => by rw [hi] at hw; cases hw
  shiftRound := fun _ wch hw => by rw [hi] at hw; cases hw
  periodShape := periodShape_of_idle hi
  noReplay := noReplayWatch_of_idle hi

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`roundBundle_steps` with the side inputs quantified over the run.** -/
theorem roundBundle_steps_run {w : List (Fin 2)} {delay : ℕ} :
    ∀ {n : ℕ} {x y : State GalilVM},
      Steps (galilFrameS (PofC centre place entry w) q first) delay n x y →
      RoundBundle w x.ctl x.vm →
      (∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
        ChainPositionInvariantWithShiftPhase w z.ctl z.vm ∧ (z.ctl.mode = Mode.shift → CopyIdle z.vm) ∧
          H_readsShift w z.ctl z.vm) →
      (∀ (m : ℕ) (z z' : State GalilVM),
        Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
        Tick (galilFrameS (PofC centre place entry w) q first) delay z z' →
        H_freshShift w z.vm z'.vm) →
      RoundBundle w y.ctl y.vm := by
  intro n x y h
  induction h with
  | zero x => intro hx _ _; exact hx
  | @succ n x z y ht hr ih =>
    intro hx hsup hF
    obtain ⟨hinv0, hci0, hSh0⟩ := hsup 0 x (.zero x)
    refine ih (roundBundle_tick centre place entry q first hx hinv0 hci0 hSh0
      (hF 0 x z (.zero x) ht) ht) ?_ ?_
    · intro m z' hz'
      exact hsup (m + 1) z' (.succ ht hz')
    · intro m z' z'' hz' htk
      exact hF (m + 1) z' z'' (.succ ht hz') htk

/-- **`ShiftPal` at every state of a run out of an idle chain.**  This is
`hSP`'s content, with the bundle supplied by the run instead of assumed: the
origin is idle (`roundBundle_of_idle`), the bundle travels
(`roundBundle_steps_run`), and `shiftPal_of_roundBundle` reads it off. -/
theorem shiftPal_of_run {w : List (Fin 2)} {delay n : ℕ} {x y : State GalilVM}
    (hidle : x.vm.chain = ChainVM.idle)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) delay n x y)
    (hsup : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      ChainPositionInvariantWithShiftPhase w z.ctl z.vm ∧ (z.ctl.mode = Mode.shift → CopyIdle z.vm) ∧
          H_readsShift w z.ctl z.vm)
    (hF : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      Tick (galilFrameS (PofC centre place entry w) q first) delay z z' →
      H_freshShift w z.vm z'.vm)
    (hm : y.ctl.mode = Mode.scan) (hr : y.ctl.replaying = false)
    (hcan : canRight y.vm.right)
    (hfresh : y.vm.periodOnly = false →
      ShiftPal centre place entry q first w y.vm) :
    ShiftPal centre place entry q first w y.vm :=
  shiftPal_of_roundBundle centre place entry q first hm hr
    (roundBundle_steps_run centre place entry q first h (roundBundle_of_idle hidle) hsup hF)
    hcan hfresh

end

/-- **The `CopyIdle` residue is free.**  `AuxPack.copyP` is
`CopyPack c s := c.mode ≠ Mode.copy → CopyIdle s` (`GalilChainCoupling:695`),
and `shift ≠ copy`.  `AuxPack` travels the run by
`CloseoutPackRun2.auxPack_steps`, which `packRunR_MW` already runs. -/
theorem copyIdle_shift_of_auxPack {c : Control} {s : GalilVM}
    (h : PalPeg.CloseoutPackRun2.AuxPack c s) (hm : c.mode = Mode.shift) : CopyIdle s :=
  h.copyP (by rw [hm]; decide)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ShiftPal` from the run, with the `CopyIdle` residue discharged.**  Three
run-form inputs are left: `ChainPositionInvariantWithShiftPhase` (which the four branch supplies carry),
`H_readsShift` (`CloseoutReadsOrigin.h_readsShift_of_originShift`) and
`H_freshShift` (`GalilScaffoldTopFirstRound.first_round`). -/
theorem shiftPal_of_run_aux {w : List (Fin 2)} {delay n : ℕ} {x y : State GalilVM}
    (hidle : x.vm.chain = ChainVM.idle)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) delay n x y)
    (haux : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      PalPeg.CloseoutPackRun2.AuxPack z.ctl z.vm)
    (hpos : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      ChainPositionInvariantWithShiftPhase w z.ctl z.vm)
    (hSh : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      H_readsShift w z.ctl z.vm)
    (hF : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      Tick (galilFrameS (PofC centre place entry w) q first) delay z z' →
      H_freshShift w z.vm z'.vm)
    (hm : y.ctl.mode = Mode.scan) (hr : y.ctl.replaying = false)
    (hcan : canRight y.vm.right)
    (hfresh : y.vm.periodOnly = false →
      ShiftPal centre place entry q first w y.vm) :
    ShiftPal centre place entry q first w y.vm :=
  shiftPal_of_run centre place entry q first hidle h
    (fun m z hz => ⟨hpos m z hz, fun hs => copyIdle_shift_of_auxPack (haux m z hz) hs,
      hSh m z hz⟩)
    hF hm hr hcan hfresh

end

/-! ## `ChainPositionInvariantWithShiftPhase` is not needed either — only `BlockInv`

`roundBundle_tick` passes its `hinv : ChainPositionInvariantWithShiftPhase w c s` to three places, and
every one of them uses it **only** through
`CloseoutRoundReads.blockInv_of_chainPosInv2` — i.e. only `BlockInv s.chain`:

* `chainRound_tick_S` → `chainRound_tick_BF` → `chainRound_tick_B`'s `hblk`;
* `readsRound_tick_S` → `readsRound_tick`'s `hblk`;
* `shiftRound_tick_A`'s `hblk` (already taken as `blockInv_of_chainPosInv2 hinv`).

And `BlockInv s.chain` is `Coupled.block` (`GalilChainCoupling:361`), a field of
`AuxPack.coupled` — the same run-carried pack that gave `CopyIdle`.  So the
bundle's tick needs **no** `ChainPositionInvariantWithShiftPhase` at all. -/

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`roundBundle_tick` with `ChainPositionInvariantWithShiftPhase` replaced by `BlockInv`.** -/
theorem roundBundle_tick_B {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hB : RoundBundle w c s)
    (hblk : BlockInv s.chain)
    (hci : c.mode = Mode.shift → CopyIdle s)
    (hSh : H_readsShift w c s)
    (hF : H_freshShift w s t)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    RoundBundle w c' t where
  chainRound :=
    chainRound_tick_B centre place entry q first (x := ⟨c, s⟩) (y := ⟨c', t⟩)
      hB.chainRound hB.readsRound hB.periodShape
      (h_shiftDone_of_shiftRound centre place entry q first hB.shiftRound)
      (h_birthR_vacuous centre place entry q first hB.noReplay hB.periodShape h) hblk h
  readsRound :=
    PalPeg.CloseoutRoundUnique.readsRound_tick centre place entry q first
      (x := ⟨c, s⟩) (y := ⟨c', t⟩)
      hB.chainRound hB.readsRound hB.periodShape hSh
      (h_readsBirth_vacuous centre place entry q first hB.noReplay hB.periodShape h) hblk h
  shiftRound :=
    shiftRound_tick_A centre place entry q first (x := ⟨c, s⟩) (y := ⟨c', t⟩)
      hB.chainRound hB.shiftRound hB.readsRound hF hblk hci h
  periodShape := periodShape_tick centre place entry q first hB.periodShape h
  noReplay := noReplayWatch_tick centre place entry q first hB.noReplay hB.periodShape h

/-- **The bundle along a run, with `AuxPack` doing the work of `ChainPositionInvariantWithShiftPhase`.** -/
theorem roundBundle_steps_B {w : List (Fin 2)} {delay : ℕ} :
    ∀ {n : ℕ} {x y : State GalilVM},
      Steps (galilFrameS (PofC centre place entry w) q first) delay n x y →
      RoundBundle w x.ctl x.vm →
      (∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
        AuxPack z.ctl z.vm ∧ H_readsShift w z.ctl z.vm) →
      (∀ (m : ℕ) (z z' : State GalilVM),
        Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
        Tick (galilFrameS (PofC centre place entry w) q first) delay z z' →
        H_freshShift w z.vm z'.vm) →
      RoundBundle w y.ctl y.vm := by
  intro n x y h
  induction h with
  | zero x => intro hx _ _; exact hx
  | @succ n x z y ht hr ih =>
    intro hx hsup hF
    obtain ⟨haux0, hSh0⟩ := hsup 0 x (.zero x)
    refine ih (roundBundle_tick_B centre place entry q first hx haux0.coupled.block
      (fun hs => copyIdle_shift_of_auxPack haux0 hs) hSh0 (hF 0 x z (.zero x) ht) ht) ?_ ?_
    · intro m z' hz'
      exact hsup (m + 1) z' (.succ ht hz')
    · intro m z' z'' hz' htk
      exact hF (m + 1) z' z'' (.succ ht hz') htk

/-- **`ShiftPal` from the run: `hSP`'s content with two residues left.**
`AuxPack` (a field of the premise bundle, carried by `auxPack_steps`) supplies
both `BlockInv` and `CopyIdle`; what remains is `H_readsShift`
(`CloseoutReadsOrigin.h_readsShift_of_originShift`) and `H_freshShift`
(`GalilScaffoldTopFirstRound.first_round`). -/
theorem shiftPal_of_run_B {w : List (Fin 2)} {delay n : ℕ} {x y : State GalilVM}
    (hidle : x.vm.chain = ChainVM.idle)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) delay n x y)
    (haux : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      AuxPack z.ctl z.vm)
    (hSh : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      H_readsShift w z.ctl z.vm)
    (hF : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) delay m x z →
      Tick (galilFrameS (PofC centre place entry w) q first) delay z z' →
      H_freshShift w z.vm z'.vm)
    (hm : y.ctl.mode = Mode.scan) (hr : y.ctl.replaying = false)
    (hcan : canRight y.vm.right)
    (hfresh : y.vm.periodOnly = false →
      ShiftPal centre place entry q first w y.vm) :
    ShiftPal centre place entry q first w y.vm :=
  shiftPal_of_roundBundle centre place entry q first hm hr
    (roundBundle_steps_B centre place entry q first h (roundBundle_of_idle hidle)
      (fun m z hz => ⟨haux m z hz, hSh m z hz⟩) hF)
    hcan hfresh

end

#print axioms roundBundle_of_idle
#print axioms roundBundle_steps_run
#print axioms shiftPal_of_run
#print axioms copyIdle_shift_of_auxPack
#print axioms shiftPal_of_run_aux
#print axioms roundBundle_tick_B
#print axioms roundBundle_steps_B
#print axioms shiftPal_of_run_B

end PalPeg.CloseoutBundleRun
