import PalPeg.CloseoutPreload13

/-!
# Pacing the run leg, and the real shape of the `.wait` leg

`CloseoutPreload13.run_exit_frame` closes the *frame* half of the fact
`CloseoutPreload12` names and leaves two arithmetic clauses.  This file supplies
what each of them needs.

* §1 `RunTraceP` — `CloseoutPreload13.RunTrace` with the pacing premise
  `CloseoutReadyStage.PacedL 2048 k` attached, and the count bound it buys:
  a run phase of `L` events spends at most `pacedComparisons 2048 L` units of
  debt (`runTraceP_count`, `runP_exit_debt`).
* §2 `credit_double_covers` — the bookkeeping half of clause 1: when the run
  phase's own consumption fits in the quarter-cell credit `m / 4`, the
  undoubled budget plus that consumption is dominated by the doubled budget
  (`CloseoutPreload11.credit_double`).  So `runP_exit_ge` turns an entry budget
  stated at window `m` into the exit budget stated at window `2 * m`.
* §3 **a correction to clause 2.**  `CloseoutPreload13` conjectured a
  `.wait`/`.run` *alternation* needing a fuel measure.  There is none:
  `GalilScaffoldTopSearch.searchStep` in `.wait` mode is
  `advance a (GalilScaffoldDouble.waitStep true ·)`, and `waitStep` either
  leaves the state in `.wait` (debt not yet zero) or enters `.double`.  **A
  `.wait` state never returns to `.run`.**  So the leg is a straight
  `.wait`-only trace whose own measure is the debt itself, and it hands the
  window on as `work = span` — the `.double` shape `CloseoutPreload13` §4
  already corrected.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

namespace PalPeg.CloseoutPreload14

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat reset zero dec
  dec_value dec_canonical zero_iff ofNat_value)
open PalPeg.CloseoutReadyStage (PacedL pacedL_count_take)
open PalPeg.CloseoutDebtAudit (pacedComparisons)
open PalPeg.CloseoutPreload11 (stageCredit credit_double)
open PalPeg.CloseoutPreload13 (RunTrace runTrace_debt runTrace_snoc run_exit_frame)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The paced run trace -/

/-- **NAMED — a run phase with its clock pacing.**  `CloseoutPreload13.RunTrace`
carries no premise limiting how many of its events are comparisons; this is the
same trace with the stage's pacing hypothesis attached. -/
def RunTraceP (k : ℕ) (as : List Bool) (v t : SearchVM) : Prop :=
  RunTrace as v t ∧ PacedL 2048 k as

/-- **The count bound.**  A paced event list of length `L` holds at most
`pacedComparisons 2048 L` comparisons — the whole list, not just a prefix. -/
theorem pacedL_count {k : ℕ} {as : List Bool} (hk : k ≤ 2047)
    (h : PacedL 2048 k as) :
    as.count true ≤ pacedComparisons 2048 as.length := by
  have := pacedL_count_take (k := k) (N := as.length) hk h
  rwa [List.take_length] at this

/-- The same, for a paced run trace. -/
theorem runTraceP_count {k : ℕ} {as : List Bool} {v t : SearchVM}
    (hk : k ≤ 2047) (h : RunTraceP k as v t) :
    as.count true ≤ pacedComparisons 2048 as.length :=
  pacedL_count hk h.2

#print axioms runTraceP_count

/-- **NAMED — the debt a paced run phase leaves.**  Combining
`CloseoutPreload13.runTrace_debt` with the pacing: the exit debt is at least the
entry debt less `pacedComparisons 2048 L`. -/
theorem runTraceP_debt_ge {k : ℕ} {as : List Bool} {v t : SearchVM}
    (hk : k ≤ 2047) (h : RunTraceP k as v t) :
    value v.search.debt - (pacedComparisons 2048 as.length : ℤ) ≤ value t.search.debt := by
  have hc := runTraceP_count hk h
  have hd := runTrace_debt h.1
  have : ((as.count true : ℕ) : ℤ) ≤ ((pacedComparisons 2048 as.length : ℕ) : ℤ) := by
    exact_mod_cast hc
  omega

#print axioms runTraceP_debt_ge

/-! ## 2. The doubling leg -/

/-- **NAMED — the quarter-cell credit pays for the run phase.**  This is the
bookkeeping identity clause 1 of `CloseoutPreload13` §4 asks for: if the run
phase's own consumption fits in `m / 4`, then the budget stated at window `m`
plus that consumption is covered by the budget stated at the doubled window.
Immediate from `CloseoutPreload11.credit_double`. -/
theorem credit_double_covers {k m C : ℕ} (hm : 8 * max k 1 ≤ m) (hC : C ≤ m / 4) :
    stageCredit k m + C ≤ stageCredit k (2 * m) := by
  have := credit_double (k := k) (m := m) hm
  omega

#print axioms credit_double_covers

/-- The same over `ℤ`, in the shape the stage budgets are stated in. -/
theorem credit_double_covers_int {Rad k m C : ℕ} (hm : 8 * max k 1 ≤ m) (hC : C ≤ m / 4) :
    stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) + 1 + (C : ℤ)
      ≤ stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 := by
  have h := credit_double_covers (k := k) (m := m) (C := C) hm hC
  have : ((stageCredit k m + C : ℕ) : ℤ) ≤ ((stageCredit k (2 * m) : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at this ⊢
  omega

/-- **NAMED — clause 1 of `CloseoutPreload13` §4, closed modulo the entry
budget.**  A paced run phase entered with the *doubled*-window budget plus its
own paced consumption exits with the doubled-window budget — which is exactly
the hypothesis `CloseoutPreload12.runEntriesS_of_double_exit` asks of the
`.double` state.  Note the entry budget is stated at `2 * m`: by
`credit_double_covers` the window-`m` budget plus the phase's consumption is
*weaker*, so this is the conservative form. -/
theorem runP_exit_debt {Rad k m slack : ℕ} {as : List Bool} {v t : SearchVM}
    (hk : slack ≤ 2047) (h : RunTraceP slack as v t)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      + (pacedComparisons 2048 as.length : ℤ) ≤ value v.search.debt) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t.search.debt := by
  have := runTraceP_debt_ge hk h
  omega

#print axioms runP_exit_debt

/-- The same at an exit tick, through `CloseoutPreload13.run_exit_frame`: the
full frame *and* the doubled-window budget, with the `.double` exit carrying
`work = ofNat m` (the `CloseoutPreload13` correction). -/
theorem runP_exit_frame_debt {Rad k m mw slack : ℕ} {as : List Bool}
    {v t t' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hk : slack ≤ 2047)
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat mw)
    (hlow : v.lower = ofNat k)
    (hr : RunTrace as v t) (hp : PacedL 2048 slack (as ++ [a]))
    (hmt : t.search.mode = Mode.run) (hs : searchStep c a t t')
    (hne : t'.search.mode ≠ Mode.run)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      + (pacedComparisons 2048 (as.length + 1) : ℤ) ≤ value v.search.debt) :
    t'.lower = ofNat k ∧ t'.walker = v.walker ∧
      t'.search.finalStage = v.search.finalStage ∧
      stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t'.search.debt ∧
      (t'.search.mode = Mode.wait → t'.search.span = ofNat mw) ∧
      (t'.search.mode = Mode.double →
        t'.search.work = ofNat mw ∧ t'.search.span = reset ∧ t'.search.quarter = 0) := by
  obtain ⟨hl, hw, hf, hd, -, hwait, hdbl⟩ :=
    run_exit_frame hm hsp hlow hr hmt hs hne
  have hfull : RunTraceP slack (as ++ [a]) v t' := ⟨runTrace_snoc hr hmt hs, hp⟩
  have hlen : (as ++ [a]).length = as.length + 1 := by simp
  have hge := runP_exit_debt (Rad := Rad) (k := k) (m := m) hk hfull (by rw [hlen]; exact hE)
  exact ⟨hl, hw, hf, hge, hwait, hdbl⟩

#print axioms runP_exit_frame_debt

/-! ## 3. The `.wait` leg — there is no alternation -/

/-- **NAMED — the two cases of a `.wait` tick.**  Either the debt is not yet
zero and the state stays in `.wait` with its window untouched, or the debt is
zero and the tick enters `.double`, moving the window into `work`.  In neither
case does the state return to `.run`. -/
theorem wait_step_cases {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.wait) (hs : searchStep c a v v') :
    v'.lower = v.lower ∧ v'.walker = v.walker ∧
      value v'.search.debt = value v.search.debt - (if a then 1 else 0) ∧
      ((zero v.search.debt = false ∧ v'.search.mode = Mode.wait ∧
          v'.search.span = v.search.span ∧ v'.search.work = v.search.work) ∨
       (zero v.search.debt = true ∧ v'.search.mode = Mode.double ∧
          v'.search.work = v.search.span ∧ v'.search.span = reset ∧
          v'.search.quarter = 0)) := by
  unfold searchStep at hs
  rw [hm] at hs
  subst hs
  by_cases hz : zero v.search.debt = true
  · have hw : GalilScaffoldDouble.waitStep true v.search = GalilScaffoldDouble.enter v.search :=
      GalilScaffoldDouble.wait_enter _ hm hz
    refine ⟨rfl, rfl, ?_, Or.inr ⟨hz, ?_, ?_, ?_, ?_⟩⟩ <;>
      cases a <;>
      simp [GalilScaffoldSearchRun.advance, hw, GalilScaffoldDouble.enter, dec_value]
  · have hz' : zero v.search.debt = false := by
      cases h : zero v.search.debt
      · rfl
      · exact absurd h hz
    have hw : GalilScaffoldDouble.waitStep true v.search = v.search := by
      simp [GalilScaffoldDouble.waitStep, hz']
    refine ⟨rfl, rfl, ?_, Or.inl ⟨hz', ?_, ?_, ?_⟩⟩ <;>
      cases a <;>
      simp [GalilScaffoldSearchRun.advance, hw, dec_value, hm]

#print axioms wait_step_cases

/-- **NAMED — a `.wait` state never re-enters `.run`.**  This is the correction
to clause 2 of `CloseoutPreload13` §4: the conjectured `.wait`/`.run`
alternation does not exist, so no fuel measure for it is needed. -/
theorem wait_not_to_run {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.wait) (hs : searchStep c a v v') :
    v'.search.mode ≠ Mode.run := by
  obtain ⟨-, -, -, hc | hc⟩ := wait_step_cases hm hs
  · rw [hc.2.1]; decide
  · rw [hc.2.1]; decide

#print axioms wait_not_to_run

/-- Consecutive ticks all taken in `.wait` mode. -/
inductive WaitTrace : List Bool → SearchVM → SearchVM → Prop
  | nil (v : SearchVM) : WaitTrace [] v v
  | cons (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool) (v v' t : SearchVM)
      (hm : v.search.mode = Mode.wait) (hs : searchStep c a v v')
      (hr : WaitTrace as v' t) : WaitTrace (a :: as) v t

/-- **The `.wait` leg's own frame and measure.**  While the phase stays in
`.wait` the window, the lower bound and the walker are untouched, and the debt
falls by one per comparison — so the debt itself is the measure of the leg: it
can hold at most `value v.search.debt` comparisons before `waitStep` fires. -/
theorem waitTrace_frame {as : List Bool} {v t : SearchVM}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait) :
    t.lower = v.lower ∧ t.walker = v.walker ∧ t.search.span = v.search.span ∧
      t.search.work = v.search.work ∧
      value t.search.debt = value v.search.debt - as.count true := by
  induction hr with
  | nil => simp
  | cons c a as v v' t hm hs hrest ih =>
      obtain ⟨hl, hw, hd, hc | hc⟩ := wait_step_cases hm hs
      · obtain ⟨il, iw, isp, iwk, idb⟩ := ih hmt
        refine ⟨il.trans hl, iw.trans hw, isp.trans hc.2.2.1, iwk.trans hc.2.2.2, ?_⟩
        rw [idb, hd]
        cases a <;> simp <;> omega
      · -- the trace continues, so `t` is reachable from a `.double` state; but a
        -- `.double` state is not `.wait`, and `waitTrace` only takes `.wait` ticks
        exfalso
        cases hrest with
        | nil w => rw [hc.2.1] at hmt; exact absurd hmt (by decide)
        | cons c2 a2 as2 w w' t2 hm2 hs2 hr2 =>
            rw [hc.2.1] at hm2; exact absurd hm2 (by decide)

#print axioms waitTrace_frame

/-- **NAMED — the `.wait` exit.**  A `.wait` leg that leaves `.wait` leaves it
into `.double`, carrying the window it was given into `work` — the shape
`CloseoutPreload12.runEntriesS_of_double_exit` consumes once the `.double`
phase has spent `work` back into `span`. -/
theorem wait_exit_double {mw : ℕ} {c : GalilScaffoldPlace.Place} {a : Bool}
    {as : List Bool} {v t t' : SearchVM}
    (hsp : v.search.span = ofNat mw)
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hs : searchStep c a t t') (hne : t'.search.mode ≠ Mode.wait) :
    t'.search.mode = Mode.double ∧ t'.search.work = ofNat mw ∧
      t'.search.span = reset ∧ t'.search.quarter = 0 ∧
      t'.lower = v.lower ∧ t'.walker = v.walker := by
  obtain ⟨il, iw, isp, -, -⟩ := waitTrace_frame hr hmt
  obtain ⟨hl, hw, -, hc | hc⟩ := wait_step_cases hmt hs
  · exact absurd hc.2.1 hne
  · exact ⟨hc.2.1, by rw [hc.2.2.1, isp, hsp], hc.2.2.2.1, hc.2.2.2.2,
      hl.trans il, hw.trans iw⟩

#print axioms wait_exit_double

/-!
## 4. What is left

Closed here:

* clause 1 of `CloseoutPreload13` §4 **modulo the entry budget**:
  `runP_exit_debt` / `runP_exit_frame_debt` derive
  `stageDebt Rad k + stageCredit k (2*m) + 1 ≤ value t'.search.debt` from the
  pacing alone, and `credit_double_covers` shows the quarter-cell credit of one
  doubling absorbs a consumption of `m / 4`.
* clause 2 is **not a fuel problem**: `wait_not_to_run` shows a `.wait` state
  never returns to `.run`, so the `.run` → `.wait` → `.double` → `prepare`
  round trip has no alternation inside it, and the `.wait` leg's own measure is
  its debt (`waitTrace_frame`) with the exit shape `work = ofNat m`
  (`wait_exit_double`).

The single residue is now the **entry budget calibration**: `runP_exit_debt`
asks the `.run` entry to hold
`stageDebt Rad k + stageCredit k (2*m) + 1 + pacedComparisons 2048 L`, where `L`
is the run phase's event count.  Nothing yet bounds `L` by the stage window, so
nothing yet converts `CloseoutReadyStage`'s stage-entry debt into that premise —
i.e. the missing fact is `L ≤ dpEvents (m+1)`-style: *a `.run` phase entered at
window `m` exits within the stage's own event budget.*

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload14
