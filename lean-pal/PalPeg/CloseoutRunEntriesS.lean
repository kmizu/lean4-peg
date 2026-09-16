import PalPeg.CloseoutReadyStage
import PalPeg.CloseoutRunEntriesPaced

/-!
# `RunEntriesS` for the concrete search: the `.run` entry is `startRun`

`CloseoutReadyStage.runEntryS_of_entryPaced` reduced the `.run`-entry datum to a
hand-over statement about the preparation phase.  This file discharges the
*machine* half of that hand-over for the concrete search
(`GalilScaffoldTopSearch.searchStep` over `GalilScaffoldPrepareControl.Tick`):

* `run_entry_startRun` — **entering `.run` is `startRun` and nothing else.**
  From every non-`.run` mode, a `searchStep` that ends in `.run` must be the
  `Tick` branch (`lower`/`lowerHome`/`copy`/`home`), and the only `Tick`
  producing `.run` is `startRun`.  Hence at the entry the source head is home
  (`focus = 4`), the handed-over DP machine is `GalilScaffoldControl.start 320`
  of the preparation's program (`run_entry_dp`), and the entry debt is the debt
  the preparation held, minus the advance of this very event (`run_entry_debt`):
  the preparation ticks never touch the debt (`Tick.tick_debt`), so the entry
  debt is exactly `initialDebt radius` plus `2` per grow tick.

* `runEntriesS_of_inv` — **the closure over every event list.**  Any invariant
  `Q` that is preserved by `searchStep` and that discharges `DpSafeStage` at
  each `.run` entry gives `RunEntriesS as v` for *every* `as`: no condition on
  `as.length` and none on `as.count true`.  The per-entry budget is paid by
  `dpSafeStage_entry_paced`, which is itself budget-free.

* §3 checks the arithmetic at the calibrated first stage on the explicit
  restarted trace of `CloseoutRunEntriesPaced` (`v0`, `p1 … p8`): the entry debt
  is `2`, which is exactly `GalilReplaySpan.stageDebt 0 0`, i.e. the `stageDebt Rad k`
  of `StageEntry 0 reset` (`3*0 ≤ 5*0`), and the stage window is
  `stageWindow 0 = 8`.  So the debt half of the hand-over holds on the nose at
  the restart, with no slack assumption.

## What is still named

`PreloadHandover` — the identification of `GalilScaffoldControl.start 320 x.program`
at the `startRun` tick with `⟨GalilScaffoldPreload.initial w lower, false⟩` for the
calibrated window `w` (`w.length = stageWindow k`).  This is a whole-phase
statement about the copy phase that precedes the entry
(`GalilScaffoldPrepareControl.prepared_run` proves exactly this shape for a full
run from `.lower`, but relates the *program config*, not the pair, and only
along a complete `Run`); it is not a per-tick fact, so it stays named here.
Its precise type is

  `PreloadHandover : ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool)
      (w : List (Fin 3)) (lower : ℕ),
      searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      v'.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩`

and `runEntryS_of_handover` below shows that this, together with the debt facts
proved here, is all that `RunEntryS` needs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRunEntriesS

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl
open PalPeg.GalilScaffoldCounter (Counter Canonical value)
open PalPeg.GalilSearchReadyInv
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow)

/-! ## 1. The `.run` entry is `startRun` -/

/-- The only preparation tick that produces `.run` is `startRun`. -/
theorem tick_run_startRun {x y : State} (ht : Tick true x y) (hm : y.mode = .run) :
    x.mode = .home ∧ (x.program.config.tapes 7).focus = 4 ∧
      y = {x with program := GalilScaffoldControl.start 320 x.program, mode := .run} := by
  cases ht with
  | lowerBit x hmx hp => rw [show ({x with program := _, work := _} : State).mode = x.mode from rfl, hmx] at hm; exact absurd hm (by decide)
  | lowerEnd x hmx hp => simp at hm
  | lowerLeft x hmx hf hl => rw [show ({x with program := _} : State).mode = x.mode from rfl, hmx] at hm; exact absurd hm (by decide)
  | beginCopy x hmx hf => simp at hm
  | copyBit x a hmx ha hw => rw [show ({x with program := _, work := _, walker := _} : State).mode = x.mode from rfl, hmx] at hm; exact absurd hm (by decide)
  | copyEnd x hmx he => simp at hm
  | sourceLeft x hmx hf hl => rw [show ({x with program := _} : State).mode = x.mode from rfl, hmx] at hm; exact absurd hm (by decide)
  | startRun x hmx hf => exact ⟨hmx, hf, rfl⟩

/-- **Entering `.run` is `startRun`.**  Every non-`.run` mode either cannot reach
`.run` in one `searchStep` at all, or does so through the `Tick` branch, whose
only `.run`-producing constructor is `startRun`. -/
theorem run_entry_startRun {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) :
    v.search.mode = .home ∧ (v.toPrep.program.config.tapes 7).focus = 4 ∧
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
        ({v.toPrep with program := GalilScaffoldControl.start 320 v.toPrep.program, mode := .run} : State)) v.search.quarter v.lower := by
  classical
  unfold searchStep at hs
  cases hm : v.search.mode with
  | idle => rw [hm] at hs; subst hs; rw [hm] at hr; exact absurd hr (by decide)
  | found => rw [hm] at hs; subst hs; rw [hm] at hr; exact absurd hr (by decide)
  | missed => rw [hm] at hs; subst hs; rw [hm] at hr; exact absurd hr (by decide)
  | grow =>
    rw [hm] at hs
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hs
      have : v'.search.mode = .grow := by
        rw [hs, ofPrep_mode, afterAdvance_mode, growStep_mode]; exact hm
      rw [this] at hr; exact absurd hr (by decide)
    · simp only [hp, Bool.false_eq_true, if_false] at hs
      have : v'.search.mode = .lower := by
        rw [hs, ofPrep_mode, afterAdvance_mode, prepare_mode]
      rw [this] at hr; exact absurd hr (by decide)
  | run => exact absurd hm hne
  | wait =>
    rw [hm] at hs
    have hmode : v'.search.mode = .double ∨ v'.search.mode = .wait := by
      rw [hs]
      show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _ ∨
        (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _
      rw [advance_mode]
      rcases waitStep_mode v.search with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hm)
    rcases hmode with h1 | h1 <;> rw [h1] at hr <;> exact absurd hr (by decide)
  | double =>
    rw [hm] at hs
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hs
      have : v'.search.mode = .double := by
        rw [hs]
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        rw [advance_mode, doubleStep_mode]; exact hm
      rw [this] at hr; exact absurd hr (by decide)
    · simp only [hp, Bool.false_eq_true, if_false] at hs
      have : v'.search.mode = .lower := by
        rw [hs, ofPrep_mode, afterAdvance_mode, prepare_mode]
      rw [this] at hr; exact absurd hr (by decide)
  | lower =>
    rw [hm] at hs
    obtain ⟨y, hy, hv'⟩ := hs
    have hym : y.mode = .run := by
      have : v'.search.mode = (GalilScaffoldPreparePaced.afterAdvance a y).mode := by
        rw [hv', ofPrep_mode]
      rw [afterAdvance_mode] at this
      rw [← this]; exact hr
    obtain ⟨h1, h2, h3⟩ := tick_run_startRun hy hym
    rw [show v.toPrep.mode = v.search.mode from rfl, hm] at h1
    exact absurd h1 (by decide)
  | lowerHome =>
    rw [hm] at hs
    obtain ⟨y, hy, hv'⟩ := hs
    have hym : y.mode = .run := by
      have : v'.search.mode = (GalilScaffoldPreparePaced.afterAdvance a y).mode := by
        rw [hv', ofPrep_mode]
      rw [afterAdvance_mode] at this
      rw [← this]; exact hr
    obtain ⟨h1, h2, h3⟩ := tick_run_startRun hy hym
    rw [show v.toPrep.mode = v.search.mode from rfl, hm] at h1
    exact absurd h1 (by decide)
  | copy =>
    rw [hm] at hs
    obtain ⟨y, hy, hv'⟩ := hs
    have hym : y.mode = .run := by
      have : v'.search.mode = (GalilScaffoldPreparePaced.afterAdvance a y).mode := by
        rw [hv', ofPrep_mode]
      rw [afterAdvance_mode] at this
      rw [← this]; exact hr
    obtain ⟨h1, h2, h3⟩ := tick_run_startRun hy hym
    rw [show v.toPrep.mode = v.search.mode from rfl, hm] at h1
    exact absurd h1 (by decide)
  | home =>
    rw [hm] at hs
    obtain ⟨y, hy, hv'⟩ := hs
    have hym : y.mode = .run := by
      have : v'.search.mode = (GalilScaffoldPreparePaced.afterAdvance a y).mode := by
        rw [hv', ofPrep_mode]
      rw [afterAdvance_mode] at this
      rw [← this]; exact hr
    obtain ⟨h1, h2, h3⟩ := tick_run_startRun hy hym
    refine ⟨rfl, h2, ?_⟩
    rw [hv', h3]

#print axioms tick_run_startRun
#print axioms run_entry_startRun

/-- **The handed-over DP machine.**  At the `.run` entry the program is the
preparation's program restarted at `320`, and it is not done. -/
theorem run_entry_dp {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) :
    v'.dp = GalilScaffoldControl.start 320 v.dp := by
  obtain ⟨-, -, h3⟩ := run_entry_startRun hs hne hr
  rw [h3]
  cases a <;> rfl

/-- **The entry debt.**  The preparation ticks never touch the debt, so the debt
at the `.run` entry is the debt held before the entry tick, minus the advance of
this very event. -/
theorem run_entry_debt {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) :
    v'.search.debt =
      (if a then GalilScaffoldCounter.dec v.search.debt else v.search.debt) := by
  obtain ⟨-, -, h3⟩ := run_entry_startRun hs hne hr
  rw [h3]
  cases a <;> rfl

#print axioms run_entry_dp
#print axioms run_entry_debt

/-! ## 2. The closure over every event list -/

/-- An invariant is a *run-entry invariant* when it is preserved by `searchStep`
and discharges the cut budget at every `.run` entry. -/
def EntryInv (Q : SearchVM → List Bool → Prop) : Prop :=
  ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
    Q v (a :: as) → searchStep center a v v' →
      (v.search.mode ≠ .run → v'.search.mode = .run → DpSafeStage v' as) ∧ Q v' as

/-- **`RunEntriesS` for every event list.**  A run-entry invariant gives the
`.run`-entry datum along *every* stream: no bound on the length of `as` and no
bound on its comparison count appear anywhere. -/
theorem runEntriesS_of_inv {Q : SearchVM → List Bool → Prop} (hQ : EntryInv Q) :
    ∀ (as : List Bool) (v : SearchVM), Q v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq center v' hstep
    obtain ⟨hentry, hnext⟩ := hQ v v' center a as hq hstep
    exact ⟨fun _ hne hr => hentry hne hr, ih v' hnext⟩

#print axioms runEntriesS_of_inv

/-- **`RunEntryS` from the named preload hand-over plus the debt facts.**  This
is `runEntryS_of_entryPaced` with its hand-over premise cut down to the single
residual: the identification of the started program with the calibrated preload.
The `Canonical`/`stageDebt` halves are supplied as data of the stage. -/
theorem runEntryS_of_handover (center : GalilScaffoldPlace.Place) (a : Bool)
    (v v' : SearchVM) (as : List Bool) (w : List (Fin 3)) (lower Rad k slack : ℕ)
    (hw : w.length = stageWindow k)
    (hpre : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      v'.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hcan : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      Canonical v'.search.debt)
    (hdebt : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (hlen : dpEvents (stageWindow k) ≤ as.length) (hpaced : PacedL 2048 slack as) :
    RunEntryS center a v v' as :=
  runEntryS_of_entryPaced center a v v' as w lower Rad k slack hw
    (fun hs hne hr => ⟨hpre hs hne hr, hcan hs hne hr, hdebt hs hne hr⟩)
    hstage hslack hlen hpaced

#print axioms runEntryS_of_handover

/-! ## 3. The arithmetic at the calibrated first stage -/

open PalPeg.CloseoutRunEntriesPaced (v0 p1 p2 p3 p4 p5 p6 p7 p8 ctr)

/-- The stage debt of the restart stage: `StageEntry 0 reset` has `k = 0`, and
`stageDebt 0 0 = 2 * max 0 1 - 0 = 2`. -/
theorem stageDebt_restart : PalPeg.GalilReplaySpan.stageDebt 0 ((0 : ℕ) : ℤ) = 2 := by
  norm_num [PalPeg.GalilReplaySpan.stageDebt]

/-- The explicit restarted trace enters `.run` at `p8` with debt exactly the
stage debt of its stage: `initialDebt reset` plus the `2` of the single grow
tick is `2 = stageDebt 0 0`. -/
theorem trace_entry_debt :
    PalPeg.GalilReplaySpan.stageDebt 0 ((0 : ℕ) : ℤ)
      ≤ value (PalPeg.CloseoutRunEntriesPaced.w p8).search.debt := by
  rw [stageDebt_restart, PalPeg.CloseoutRunEntriesPaced.p8_debt]

/-- Its stage window is the calibrated minimum. -/
theorem stageWindow_restart : stageWindow 0 = 8 := by
  norm_num [PalPeg.CloseoutDebtAudit.stageWindow]

/-- `StageEntry 0 reset` gives the arithmetic premise of
`dpSafeStage_entry_paced` for `k = 0`. -/
theorem stage_of_restart : 3 * 0 ≤ 5 * 0 := by omega

#print axioms stageDebt_restart
#print axioms trace_entry_debt
#print axioms stageWindow_restart

end PalPeg.CloseoutRunEntriesS
