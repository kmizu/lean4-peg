import PalPeg.CloseoutPreload12

/-!
# The run leg of `PostRun`: the frame carried by a `.run` phase

`CloseoutPreload12` ends by naming the one machine fact still missing from
`CloseoutPreload8.PostRun`:

> a `.run` phase entered DP-safe at window `m` exits into `.wait`/`.double` with
> `span = ofNat m`, the same `lower = ofNat k`, and debt still at least
> `stageDebt Rad k + stageCredit k (2 * m) + 1`.

This file discharges the **frame** half of that fact — everything except the
arithmetic of the doubled-window credit — directly from the machine, with no
hypothesis beyond the trace itself.

* §1 `safe_calls_debt`, `safe_quanta_debt`: a `SafeQuanta` spends exactly one
  unit of debt per `true` event and nothing else touches the counter.  (The
  existing `GalilScaffoldSearchRun.quanta_safe` proves this only for a
  `RunQuanta`; the `.run` branch of `searchStep` hands us a bare `SafeQuanta`.)
* §2 `RunTrace`: a maximal run of `searchStep` ticks all taken in `.run` mode,
  and its four frame lemmas — `lower`, `walker`, `finalStage`, and the *stage*
  span `GalilScaffoldSearchRun.stageSpan` — together with the debt ledger.
* §3 `run_exit_frame`: the exit itself.  A `.run` phase entered at
  `span = ofNat m`, `lower = ofNat k` exits with `lower = ofNat k`, with
  `span = ofNat m` when the exit is `.wait`, and with `work = ofNat m`,
  `span = reset`, `quarter = 0` when the exit is `.double`; and the debt has
  fallen by exactly the number of comparisons consumed.
* §4 the residue, stated exactly.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

namespace PalPeg.CloseoutPreload13

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat reset dec_value ofNat_value)
open PalPeg.GalilScaffoldSearchRun (SafeCalls SafeQuanta advance stageSpan
  safe_quanta_frame double_work_of_quanta double_reset_of_quanta quanta_exit_mode ExitMode)

/-! ## 1. The debt ledger of a bare `SafeQuanta` -/

/-- The DP calls never touch the debt counter. -/
theorem safe_calls_debt {s t : State} {x y : GalilScaffoldControl.Machine 12}
    {bs : List Bool} (hr : SafeCalls s x bs t y) : t.debt = s.debt := by
  induction hr with
  | nil => rfl
  | cons s x y z b bs t ht hsafe hr ih =>
      exact ih.trans (GalilScaffoldSearchRun.finish_debt _ _ _ _)

/-- **The run-phase ledger.**  A `SafeQuanta` spends exactly one unit of debt per
comparison; the 64 DP calls between comparisons are free. -/
theorem safe_quanta_debt {s t : State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} (hr : SafeQuanta s x as t y) :
    value t.debt = value s.debt - as.count true := by
  induction hr with
  | nil => simp
  | cons s u t x y z a as hm hq hr ih =>
      have hd : u.debt = s.debt := safe_calls_debt hq
      have hav : value (advance a u).debt = value s.debt - (if a then 1 else 0) := by
        cases a
        · simp [advance, hd]
        · simp [advance, hd, dec_value]
      rw [ih, hav]
      cases a <;> simp <;> omega

#print axioms safe_quanta_debt

/-! ## 2. A maximal `.run` trace on the search VM -/

/-- Consecutive `searchStep` ticks, each *taken* in `.run` mode.  The centre
place is allowed to differ from tick to tick, as it does on the real scan. -/
inductive RunTrace : List Bool → SearchVM → SearchVM → Prop
  | nil (v : SearchVM) : RunTrace [] v v
  | cons (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool) (v v' t : SearchVM)
      (hm : v.search.mode = Mode.run) (hs : searchStep c a v v')
      (hr : RunTrace as v' t) : RunTrace (a :: as) v t

/-- A single `.run` tick, unfolded. -/
theorem run_step_quanta {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.run) (hs : searchStep c a v v') :
    SafeQuanta v.search v.dp [a] v'.search v'.dp ∧ v'.lower = v.lower ∧
      v'.walker = v.walker := by
  unfold searchStep at hs; rw [hm] at hs; exact hs

/-- The lower bound and the walker are untouched by the run phase. -/
theorem runTrace_lower {as : List Bool} {v t : SearchVM} (hr : RunTrace as v t) :
    t.lower = v.lower ∧ t.walker = v.walker := by
  induction hr with
  | nil => exact ⟨rfl, rfl⟩
  | cons c a as v v' t hm hs hrest ih =>
      obtain ⟨-, hl, hw⟩ := run_step_quanta hm hs
      exact ⟨ih.1.trans hl, ih.2.trans hw⟩

/-- The stage span and the final-stage flag are untouched by the run phase. -/
theorem runTrace_frame {as : List Bool} {v t : SearchVM} (hr : RunTrace as v t) :
    t.search.finalStage = v.search.finalStage ∧
      stageSpan t.search = stageSpan v.search := by
  induction hr with
  | nil => exact ⟨rfl, rfl⟩
  | cons c a as v v' t hm hs hrest ih =>
      obtain ⟨hq, -, -⟩ := run_step_quanta hm hs
      have h := safe_quanta_frame hq
      exact ⟨ih.1.trans h.1, ih.2.trans h.2⟩

/-- **The run-phase debt ledger, on the search VM.** -/
theorem runTrace_debt {as : List Bool} {v t : SearchVM} (hr : RunTrace as v t) :
    value t.search.debt = value v.search.debt - as.count true := by
  induction hr with
  | nil => simp
  | cons c a as v v' t hm hs hrest ih =>
      obtain ⟨hq, -, -⟩ := run_step_quanta hm hs
      have h := safe_quanta_debt hq
      rw [ih, h]
      cases a <;> simp <;> omega

#print axioms runTrace_debt

/-! ## 3. The exit -/

/-- One more `.run` tick extends the trace. -/
theorem runTrace_snoc {as : List Bool} {v t t' : SearchVM}
    {c : GalilScaffoldPlace.Place} {a : Bool} (hr : RunTrace as v t)
    (hmt : t.search.mode = Mode.run) (hs : searchStep c a t t') :
    RunTrace (as ++ [a]) v t' := by
  induction hr with
  | nil w => exact RunTrace.cons c a [] w t' t' hmt hs (RunTrace.nil t')
  | cons c0 a0 as0 v0 v1 t0 hm0 hs0 hrest ih =>
      exact RunTrace.cons c0 a0 _ v0 v1 t' hm0 hs0 (ih hmt hs)


/-- **NAMED — the frame a `.run` phase carries to its exit.**  A run phase
entered at window `m` and lower bound `k` leaves the lower bound alone, spends
exactly one debt unit per comparison, and hands the window on in the shape the
exit mode dictates: `.wait` keeps it in `span`, `.double` moves it into `work`
and resets `span` and `quarter` (`GalilScaffoldSearchFinish.finish`).

This is the frame half of the fact `CloseoutPreload12` names; §4 says what is
left. -/
theorem run_exit_frame {k m : ℕ} {as : List Bool} {v t t' : SearchVM}
    {c : GalilScaffoldPlace.Place} {a : Bool}
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat m)
    (hlow : v.lower = ofNat k)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hs : searchStep c a t t') (hne : t'.search.mode ≠ Mode.run) :
    t'.lower = ofNat k ∧ t'.walker = v.walker ∧
      t'.search.finalStage = v.search.finalStage ∧
      value t'.search.debt = value v.search.debt - (as ++ [a]).count true ∧
      ExitMode t'.search ∧
      (t'.search.mode = Mode.wait → t'.search.span = ofNat m) ∧
      (t'.search.mode = Mode.double →
        t'.search.work = ofNat m ∧ t'.search.span = reset ∧ t'.search.quarter = 0) := by
  have hfull : RunTrace (as ++ [a]) v t' := runTrace_snoc hr hmt hs
  obtain ⟨hl, hw⟩ := runTrace_lower hfull
  obtain ⟨hf, hspan⟩ := runTrace_frame hfull
  obtain ⟨hq, -, -⟩ := run_step_quanta hmt hs
  have hex : ExitMode t'.search := quanta_exit_mode hq hmt hne
  -- the entry state is in `.run`, so its stage span is its span
  have hentry : stageSpan v.search = ofNat m := by
    simp [stageSpan, hm, hsp]
  refine ⟨hl.trans hlow, hw, hf, by rw [runTrace_debt hfull], hex, ?_, ?_⟩
  · intro hwait
    have : stageSpan t'.search = t'.search.span := by
      simp [stageSpan, hwait]
    rw [← this, hspan, hentry]
  · intro hdbl
    have hwork : stageSpan t'.search = t'.search.work := by
      simp [stageSpan, hdbl]
    have hrst := double_reset_of_quanta hq hmt hdbl
    exact ⟨by rw [← hwork, hspan, hentry], hrst.1, hrst.2⟩

#print axioms run_exit_frame

/-!
## 4. What is left

`run_exit_frame` closes the *frame* clauses of the fact `CloseoutPreload12`
names, and closes them unconditionally: no `Canonical`, no calibration, no
pacing hypothesis.  In particular the phrasing in `CloseoutPreload12` needs one
correction — the `.double` exit does **not** keep `span = ofNat m`.
`GalilScaffoldSearchFinish.finish` moves the window into `work` and sets
`span := reset`, `quarter := 0`, so the window reaches `CloseoutPreload12.runEntriesS_of_double_exit`'s
`hsp : t.search.span = ofNat m` only after the `.double` phase's own
`GalilScaffoldDouble.step` loop has spent `work` back into `span` — which is why
the hypothesis there is at the *spent* double (`positive t.search.work = false`)
and why the budget it asks for is the doubled-window one.

So the residue of `CloseoutPreload8.PostRun` is now exactly two arithmetic
clauses, both about the debt and neither about the frame:

1. **The doubling leg.**  From `value t'.search.debt = value v.search.debt - (as ++ [a]).count true`
   (§3) and a pacing bound on `(as ++ [a]).count true` over a run phase of
   `dpEvents (m+1)` events, derive
   `stageDebt Rad k + stageCredit k (2*m) + 1 ≤ value t'.search.debt` at the
   `.double` exit — i.e. that the run phase's own comparisons cost at most
   `stageCredit k (2*m) - stageCredit k m` plus what `CloseoutPreload11.credit_double`
   already pays.  The missing input is the count bound: `RunTrace` carries no
   `PacedL` premise, so nothing yet limits `(as ++ [a]).count true`.
2. **The `.wait` leg.**  The same at a `.wait` exit, where the window is
   unchanged and the required budget is therefore `stageCredit k m`, but where
   the phase re-enters `.run` rather than dispatching `prepare`, so the
   induction is on the number of `.wait`/`.run` alternations inside one stage —
   which has no measure yet.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload13
