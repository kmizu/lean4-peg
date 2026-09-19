import PalPeg.CloseoutPreload35

/-!
# One stage cycle, on the search state alone

`CloseoutPreload35.postRunF_round_trip_S` carries the scan frame — a
`ScanSupplyInv`, a `ScanTrace` from a state satisfying `I` with `ClockInv 2048`,
and the pacing of the *whole* stream from that state — and spends all of it on a
single consequence:

```
have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
have hpa : PacedL 2048 2047 (bs ++ [a3]) := pacedL_suffix_2047 hpaced hph
```

the slack at the `.double` leg is at most `2047`.  Every other step of that
proof is about the search state alone.

This file states the same cycle with that consequence as its hypothesis, so
nothing here mentions a frame, a control or a `GalilVM`:

  from a `.run` entry with `span = ofNat mw`, `lower = ofNat k` and
  `8 * max k 1 ≤ mw`, the run / wait / double legs reach a `.double` state with
  `span = ofNat (2 * mw)` whose exit is a `PrepAt k (2 * mw)` satisfying
  `StageInvS k (2 * mw)`.

**Why the search-only form is the one that is needed.**
`CloseoutRunEntriesS.EntryInv Q` quantifies over *every* event list and every
`searchStep` successor, so its invariant `Q` cannot carry a `ScanTrace` of the
run the machine actually takes.  `runEntriesS_of_inv` then gives `RunEntriesS as v`
for every `as`, which is the half of `SearchReadyS` that
`CloseoutPreload37.readyField2_entry_of_datum` currently obtains from
`CloseoutPreload6.runEntriesS_of_namedG`, whose hypothesis `NoReturn` is the
`ReachL → ReachP` converter that fails once the machine has visited `.run`.

**Not done here.**  The legs are still hypotheses (`RunTrace rs`, `WaitTrace ws`,
`bs.length = mw`).  Splitting an arbitrary paced event list into those legs —
the totality statement — is what `EntryInv` still needs, and this file does not
prove it.  So nothing is removed from any axiom or hypothesis list yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageCycleSearch

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)
open PalPeg.CloseoutPreload13 (RunTrace run_exit_frame)
open PalPeg.CloseoutPreload14 (WaitTrace wait_step_cases wait_exit_double)
open PalPeg.CloseoutPreload17 (DoubleTrace double_spends double_exit_canonical)
open PalPeg.CloseoutPreload24 (wait_exit_debt_zero)
open PalPeg.CloseoutPreload35 (StageInvS stageInvS_of_double_exit bal_of_paced_slack_S)

/-- **One stage cycle, with no frame.**  `postRunF_round_trip_S` with its five
frame hypotheses (`hsup`, `hsc`, `hp`, `hclk`, and the pacing of the whole
stream) replaced by the one fact they were used to derive: the `.double` leg and
its dispatch are paced with slack at most `2047`. -/
theorem stageCycle_of_runEntry {k mw : ℕ} {rs ws bs : List Bool} {a1 a3 : Bool}
    {cr cw : GalilScaffoldPlace.Place} {v t0 w0 w1 u0 : SearchVM}
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat mw)
    (hlow : v.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hrun : RunTrace rs v t0) (ht0 : t0.search.mode = Mode.run)
    (hs1 : searchStep cr a1 t0 w0) (hw0 : w0.search.mode = Mode.wait)
    (hwait : WaitTrace ws w0 w1) (hw1 : w1.search.mode = Mode.wait)
    (hcan1 : Canonical w1.search.debt)
    (hs2 : searchStep cw false w1 u0) (hne : u0.search.mode ≠ Mode.wait)
    (hcan0 : Canonical u0.search.debt)
    (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hpacedDouble : PacedL 2048 2047 (bs ++ [a3])) :
    ∃ t1 : SearchVM, DoubleTrace bs u0 t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvS k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  have hne0 : w0.search.mode ≠ Mode.run := by rw [hw0]; decide
  obtain ⟨hl0, -, -, -, -, hwsp, -⟩ := run_exit_frame hm hsp hlow hrun ht0 hs1 hne0
  have hsp0 : w0.search.span = ofNat mw := hwsp hw0
  obtain ⟨hdm, hdw, hdsp, hq0, hdl, -⟩ := wait_exit_double hsp0 hwait hw1 hs2 hne
  have hz : zero w1.search.debt = true := by
    obtain ⟨-, -, -, hc | hc⟩ := wait_step_cases hw1 hs2
    · exact absurd hc.2.1 hne
    · exact hc.1
  have hd0 : value u0.search.debt = 0 := wait_exit_debt_zero hw1 hz hcan1 hs2
  obtain ⟨t1, hr, h1m, h1w, h1s, h1l, -, -⟩ := double_spends cw hdm hdw hdsp hblen
  have h1l' : t1.lower = ofNat k := by rw [h1l, hdl, hl0]
  refine ⟨t1, hr, h1m, h1w, h1s, h1l', ?_⟩
  intro c' t' hs3
  have hcal' : 8 * max k 1 ≤ 2 * mw := by omega
  have hbal := bal_of_paced_slack_S hcal' hblen hmw le_rfl hpacedDouble
  obtain ⟨hprep, hinv⟩ :=
    stageInvS_of_double_exit hr hd0 hq0 hcan0 h1m h1w h1s h1l' hblen hbal hs3
  have hc1 := double_exit_canonical hr h1m h1w hcan0
  obtain ⟨-, hwk, -⟩ := prepAt_of_double_exit h1m h1w h1s h1l' hc1 hs3
  exact ⟨hprep, hinv, hwk, hcal'⟩

#print axioms stageCycle_of_runEntry

end PalPeg.StageCycleSearch
