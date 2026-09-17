import PalPeg.CloseoutPreload15

/-!
# The run leg's entry, cut to the stage's own budget

`CloseoutPreload15` §5 names the residue that blocks `CloseoutPreload8.PostRun`:
its `run_length_le_dpEvents` / `runP_exit_debt_at_exit` ask for a charged prefix
handed over in the split shape `as ++ rest = pre ++ post` with
`pre.length = dpEvents w.length`, whereas a stage entry carries only
`CloseoutPreload8.StagePrep`'s *length* inequality
`D + dpEvents (stageWindow1 k) ≤ bs.length + as.length`.

This file does that plumbing, and removes one further mismatch on the way:
`CloseoutPreload15` asks for `w.length = stageWindow1 k`, but a stage entry only
ever supplies `w.length ≤ stageWindow1 k` (the preparation copies a `List.take`,
`CloseoutPreload8.dpSafeStage_entry_min`), so every statement here is relaxed to
the inequality.

* §1 `dpEvents_mono` — the budget is monotone in the window length.
* §2 `stagePrep_event_supply` — **the length inequality, unpacked.**  At the
  `.run` entry reached out of a `StagePrep` stage there are at least
  `dpEvents (stageWindow1 k)` events still ahead, so the charged prefix can be
  cut as a genuine `List.take` of the events, with no appeal to anything past
  the stage.
* §3 `run_length_le_dpEvents_take` — `CloseoutPreload15.run_length_le_dpEvents`
  with the prefix taken to be `as0.take (dpEvents w.length)` and its count bound
  read off the pacing, so the only premises left are the entry's debt and window.
* §4 `runP_exit_debt_at_exit_take` — the exit budget in the same shape.
* §5 the residue that remains (`CloseoutPreload8.PostRun` is *not* closed, and
  §5 records why it is not provable in the form it is stated).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

namespace PalPeg.CloseoutPreload16

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutDebtAudit (dpEvents pacedComparisons stageWindow1)
open PalPeg.CloseoutPreload6 (pacedL_count_take_gen)
open PalPeg.CloseoutPreload11 (stageCredit)
open PalPeg.CloseoutPreload13 (RunTrace runTrace_snoc)
open PalPeg.CloseoutPreload15 (run_length_le_dpEvents runP_exit_debt_of_stage)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. Monotonicity of the DP event budget -/

/-- The DP event budget is monotone in the window length. -/
theorem dpEvents_mono {W W' : ℕ} (h : W ≤ W') : dpEvents W ≤ dpEvents W' := by
  unfold dpEvents
  exact Nat.div_le_div_right (by omega)

#print axioms dpEvents_mono

/-! ## 2. The event supply at a stage entry -/

/-- **NAMED — `CloseoutPreload8.StagePrep`'s length clause, at the entry.**
A stage whose preparation trace `bs` has been walked to a `.run` entry over the
event `a` has at least `dpEvents (stageWindow1 k)` events still ahead of that
entry: the clause `D + dpEvents (stageWindow1 k) ≤ bs.length + (a :: as).length`
together with the depth bound `(bs ++ [a]).length ≤ D` leaves the whole DP
budget inside `as`.  This is the fact that lets the charged prefix be cut as a
`List.take` of `as` itself. -/
theorem stagePrep_event_supply {k D : ℕ} {bs as : List Bool} {a : Bool}
    (hlen : D + dpEvents (stageWindow1 k) ≤ bs.length + (a :: as).length)
    (hdep : (bs ++ [a]).length ≤ D) :
    dpEvents (stageWindow1 k) ≤ as.length := by
  simp only [List.length_append, List.length_singleton] at hdep
  simp only [List.length_cons] at hlen
  omega

#print axioms stagePrep_event_supply

/-- The charged prefix cut as a `take` really has the budget length. -/
theorem take_length_of_supply {k W : ℕ} {as0 : List Bool}
    (hw : W ≤ stageWindow1 k) (hsup : dpEvents (stageWindow1 k) ≤ as0.length) :
    (as0.take (dpEvents W)).length = dpEvents W := by
  have := dpEvents_mono hw
  rw [List.length_take]
  omega

/-! ## 3. The run-phase length bound, from the entry data alone -/

/-- **NAMED — `CloseoutPreload15.run_length_le_dpEvents` with the split
supplied.**  The charged prefix is `as0.take (dpEvents w.length)`, its length is
right by §2, and its comparison count is bounded by the pacing of the event
stream (`CloseoutPreload6.pacedL_count_take_gen`), so the only inputs left are
the DP preload, the entry debt and the window bound. -/
theorem run_length_le_dpEvents_take {as as0 rest : List Bool} {v t : SearchVM}
    {w : List (Fin 3)} {lower k slack : ℕ}
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hw : w.length ≤ stageWindow1 k)
    (hsup : dpEvents (stageWindow1 k) ≤ as0.length)
    (hc : Canonical v.search.debt)
    (hpaced : PacedL 2048 slack as0)
    (hdebt : (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
      ≤ value v.search.debt)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hpref : as ++ rest = as0) :
    as.length + 1 ≤ dpEvents (stageWindow1 k) := by
  set N : ℕ := dpEvents w.length with hN
  have hmono : N ≤ dpEvents (stageWindow1 k) := by rw [hN]; exact dpEvents_mono hw
  have hprelen : (as0.take N).length = N := take_length_of_supply (k := k) hw hsup
  have hcount : (as0.take N).count true ≤ (slack + N) / 2048 + 1 :=
    pacedL_count_take_gen hpaced
  have hdiv : (slack + N) / 2048 ≤ (slack + dpEvents (stageWindow1 k)) / 2048 :=
    Nat.div_le_div_right (by omega)
  have hb : (((as0.take N).count true : ℤ)) ≤ value v.search.debt := by
    have : (((as0.take N).count true : ℕ) : ℤ)
        ≤ (((slack + N) / 2048 + 1 : ℕ) : ℤ) := Int.ofNat_le.mpr hcount
    have h2 : (((slack + N) / 2048 + 1 : ℕ) : ℤ)
        ≤ (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ) :=
      Int.ofNat_le.mpr (by omega)
    omega
  have hsplit : as ++ rest = as0.take N ++ as0.drop N := by
    rw [hpref, List.take_append_drop]
  have hlt := run_length_le_dpEvents (w := w) (lower := lower) (pre := as0.take N)
    (post := as0.drop N) hdp hm hprelen hc hb hr hmt hsplit
  omega

#print axioms run_length_le_dpEvents_take

/-! ## 4. The exit budget in the same shape -/

/-- **NAMED — `CloseoutPreload15.runP_exit_debt_at_exit` with the charged prefix
cut from the event stream and the window relaxed to `≤ stageWindow1 k`.**  This
is the shape a stage entry can actually produce. -/
theorem runP_exit_debt_at_exit_take {Rad k m slack : ℕ} {as as0 rest : List Bool}
    {v t t' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hk : slack ≤ 2047)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hw : w.length ≤ stageWindow1 k)
    (hsup : dpEvents (stageWindow1 k) ≤ as0.length)
    (hc : Canonical v.search.debt)
    (hpaced : PacedL 2048 slack as0)
    (hdebt : (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
      ≤ value v.search.debt)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hpref : as ++ rest = as0)
    (hs : searchStep c a t t')
    (hp : PacedL 2048 slack (as ++ [a]))
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : 2 * stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      ≤ value v.search.debt) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t'.search.debt := by
  have hlt := run_length_le_dpEvents_take (k := k) hdp hm hw hsup hc hpaced hdebt hr hmt hpref
  refine runP_exit_debt_of_stage (Rad := Rad) (k := k) (m := m)
    (L := (as ++ [a]).length) hk ⟨runTrace_snoc hr hmt hs, hp⟩ hstage rfl ?_ hE
  have hlen : (as ++ [a]).length = as.length + 1 := by simp
  rw [hlen]
  exact hlt

#print axioms runP_exit_debt_at_exit_take

/-!
## 5. What is left

Closed here: the *plumbing* residue `CloseoutPreload15` §5 names.  A stage entry
never has to look past its own stage to produce the charged prefix: §2 turns
`CloseoutPreload8.StagePrep`'s length clause into `dpEvents (stageWindow1 k) ≤
as.length`, so the prefix is a `List.take` of the events already ahead, its
length is exactly the budget, and its comparison count comes off the pacing.
§3 / §4 then carry `CloseoutPreload15`'s length bound and exit budget with the
window relaxed to `w.length ≤ stageWindow1 k`, which is all a preparation — whose
window is a `List.take` — ever supplies.

**NOT closed — `CloseoutPreload8.PostRun` is still open, and not only for want
of work.**  `PostRun` is

> `∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v`

with *no* hypothesis on `as`.  But `DpSafeStage v as` splits `as = pre ++ post`
and constrains only the charged prefix `pre`; the suffix `post` is entirely
free — in particular it need not be `PacedL`, and no debt is held against it.
`RunEntriesS as v`, on the other hand, demands a `DpSafeStage` witness at *every*
later `.run` entry inside `as`, including the entries of the next stage, reached
after the `.run` → `.wait` → `.double` → `prepare` round trip.  Every route to
such a witness (`dpSafeStage_entry_min`, `CloseoutPreload11.dpSafe_entry_km`,
`CloseoutPreload12.dpSafe_of_stagePrepP`) consumes a pacing hypothesis on the
events it charges, and `runEntriesS_of_double_exit` likewise asks for
`PacedL 2048 0 as`.  So `PostRun` as stated is not merely unproved: the ledger
it asserts cannot be maintained against an unpaced suffix, and the statement
needs a pacing (and stage-budget) premise on `as` before the round trip of
`CloseoutPreload14` §3 / `CloseoutPreload15` / this file can be chained into it.

The one machine fact still missing for the *paced* form is the `.double` leg
between `wait_exit_double` (which lands at `work = ofNat mw`, `span = reset`) and
`CloseoutPreload12.runEntriesS_of_double_exit` (which consumes a *spent*
`.double` state, `positive work = false`): nothing yet says the doubling phase
runs `work` down to zero within its own credit.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload16
