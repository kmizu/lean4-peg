import PalPeg.CloseoutPreload17

/-!
# The three residues of `postRunP_of_machine`

`CloseoutPreload17` §3 lists what is still missing before the composition of
`CloseoutPreload16.runP_exit_debt_at_exit_take` with the `.double` leg is a
proof of `CloseoutPreload17.PostRunP`.  This file settles as much of each of the
three as is true, and names precisely what is left.

* §1 (residue 1, the slack normalisation).  `CloseoutPreload5.pacedL_suffix`
  charges the suffix the *whole* prefix length as slack.  The sharp slack is
  the prefix's own clock phase, `bs.length - 2048 * bs.count true`
  (`pacedL_suffix_slack`), and it is `≤ 2047` exactly when the prefix is
  *phase-bounded* (`PrefixPhase`), which is the list-level shadow of "the
  controller clock is a phase mod 2048".  So the `% 2048` rounding is available
  — as a consequence of `PrefixPhase`, not of `PacedL` alone.
* §2 (residue 2, the `.wait` leg).  `CloseoutPreload14.waitTrace_frame` measures
  the leg by *comparisons*, not by ticks: `wait_leg_count` shows the leg spends
  exactly the entry debt in comparisons, and `wait_leg_length_ge` shows that,
  under pacing, this forces the leg to be **long** (`2048 * debt ≤ length +
  slack`).  Hence the hoped-for "wait tick count ≤ entry debt" is false in the
  wrong direction: the tick count is bounded *below*, and is not bounded above
  at all without a liveness clause (background events may stall `.wait`
  indefinitely).
* §3 (residue 3, the `hE` of `CloseoutPreload17.double_leg_entries`).  The
  quarter-cell balance gives the exit debt from the window alone
  (`double_exit_debt_ge`), so `hE` is *supplied* by a window-length inequality
  (`double_exit_debt_bound`), and `double_leg_entries_window` is
  `double_leg_entries` with `hE` discharged.

§4 records what `postRunP_of_machine` still needs.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload18

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive reset zero zero_iff)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload11 (stageCredit)
open PalPeg.CloseoutPreload14 (WaitTrace waitTrace_frame)
open PalPeg.CloseoutPreload17 (PostRunP DoubleTrace double_exit_debt double_exit_canonical
  double_leg_entries)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The sharp suffix slack, and the `% 2048` rounding -/

/-- **NAMED — the sharp suffix slack.**  `CloseoutPreload5.pacedL_suffix` gives
the suffix the slack `bs.length`; the truth is that the prefix's own
comparisons have already been paid for, so any `slack` with
`bs.length ≤ d * bs.count true + slack` works.  The minimal such `slack` is the
prefix's clock phase. -/
theorem pacedL_suffix_slack {d slack : ℕ} {bs as : List Bool}
    (h : PacedL d 0 (bs ++ as)) (hs : bs.length ≤ d * bs.count true + slack) :
    PacedL d slack as := by
  intro n
  have h2 := h (bs.length + n)
  rw [List.take_length_add_append, List.count_append] at h2
  have hmul : d * (bs.count true + (as.take n).count true)
      = d * (bs.count true) + d * ((as.take n).count true) := by ring
  omega

#print axioms pacedL_suffix_slack

/-- **NAMED — the list-level shadow of the controller clock phase.**  A prefix
is phase-bounded when its length exceeds the ticks already charged to its own
comparisons by less than a full quantum.  This is what
`CloseoutPreload17` §3 (1) calls "the machine's clock phase": the premise
`PostRunP` must carry if its slack is to be normalised. -/
def PrefixPhase (bs : List Bool) : Prop := bs.length ≤ 2048 * bs.count true + 2047

/-- **The `% 2048` rounding of `pacedL_suffix`.**  Under `PrefixPhase` the
suffix's slack is `≤ 2047`, which is exactly the side condition
`CloseoutReadyStage.pacedL_count_take` and
`CloseoutPreload16.runP_exit_debt_at_exit_take` ask for. -/
theorem pacedL_suffix_2047 {bs as : List Bool} (h : PacedL 2048 0 (bs ++ as))
    (hph : PrefixPhase bs) : PacedL 2048 2047 as :=
  pacedL_suffix_slack h hph

#print axioms pacedL_suffix_2047

/-- A prefix shorter than one quantum is phase-bounded outright: the rounding is
free at any stage entry whose preparation fits inside a single clock period. -/
theorem prefixPhase_of_short {bs : List Bool} (h : bs.length ≤ 2047) : PrefixPhase bs := by
  unfold PrefixPhase; omega

#print axioms prefixPhase_of_short

/-- Phase-boundedness is preserved by a background tick, and by a comparison
that is itself paced.  (`false` costs one tick of phase; `true` buys a whole
quantum.) -/
theorem prefixPhase_cons_false {bs : List Bool} (h : bs.length ≤ 2048 * bs.count true + 2046) :
    PrefixPhase (bs ++ [false]) := by
  unfold PrefixPhase
  simp [List.count_append]
  omega

theorem prefixPhase_cons_true {bs : List Bool} (h : PrefixPhase bs) :
    PrefixPhase (bs ++ [true]) := by
  unfold PrefixPhase at h ⊢
  simp [List.count_append, Nat.mul_add]
  omega

#print axioms prefixPhase_cons_false
#print axioms prefixPhase_cons_true

/-! ## 2. The `.wait` leg is measured in comparisons, and is long -/

/-- **NAMED — the `.wait` leg spends exactly the entry debt.**  A leg that runs
to the `waitStep` firing point (`zero debt = true`) has held exactly
`value v.search.debt` comparisons.  This is `waitTrace_frame` read as a measure:
the measure is the *comparison count*, not the tick count. -/
theorem wait_leg_count {as : List Bool} {v t : SearchVM} (hr : WaitTrace as v t)
    (hmt : t.search.mode = Mode.wait) (hz : zero t.search.debt = true)
    (hc : Canonical t.search.debt) :
    ((as.count true : ℕ) : ℤ) = value v.search.debt := by
  obtain ⟨-, -, -, -, hd⟩ := waitTrace_frame hr hmt
  have h0 : value t.search.debt = 0 := (zero_iff _ hc).mp hz
  omega

#print axioms wait_leg_count

/-- **NAMED — a paced `.wait` leg is long.**  Since the leg holds one comparison
per unit of entry debt and the stream is clock-paced, the leg lasts at least
`2048 * debt - slack` ticks.  So the tick count of the `.wait` leg is bounded
*below* by the entry debt, not above: `CloseoutPreload17` §3 (2)'s hoped-for
upper bound is false in that direction. -/
theorem wait_leg_length_ge {as : List Bool} {slack : ℕ} (hp : PacedL 2048 slack as) :
    2048 * as.count true ≤ as.length + slack := by
  have h := hp as.length
  rw [List.take_length] at h
  exact h

#print axioms wait_leg_length_ge

/-- The two together: a paced `.wait` leg that fires has length at least
`2048 * debt - slack`. -/
theorem wait_leg_length_of_debt {as : List Bool} {v t : SearchVM} {slack d : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hp : PacedL 2048 slack as) (hd : value v.search.debt = (d : ℤ)) :
    2048 * d ≤ as.length + slack := by
  have h1 := wait_leg_count hr hmt hz hc
  have h2 := wait_leg_length_ge (as := as) (slack := slack) hp
  have h3 : ((as.count true : ℕ) : ℤ) = (d : ℤ) := by rw [h1, hd]
  have h4 : as.count true = d := by exact_mod_cast h3
  omega

#print axioms wait_leg_length_of_debt

/-! ## 3. The `.double` exit debt, and the `hE` of `double_leg_entries` -/

/-- **NAMED — the `.double` exit debt from the window alone.**  At the shape
`CloseoutPreload14.wait_exit_double` leaves (`quarter = 0`, and — by
`wait_leg_count` — `debt = 0`), the quarter cell credits one unit per four
ticks, so the exit debt is the window length quartered, less the comparisons
met. -/
theorem double_exit_debt_ge {as : List Bool} {v t : SearchVM} (hr : DoubleTrace as v t)
    (hmt : t.search.mode = Mode.double) (hwt : positive t.search.work = false)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0) :
    ((as.length : ℕ) : ℤ) ≤ 4 * value t.search.debt + 4 * ((as.count true : ℕ) : ℤ) + 3 := by
  have hb := double_exit_debt hr hmt hwt
  have hql : t.search.quarter.val < 4 := t.search.quarter.isLt
  have hq0 : v.search.quarter.val = 0 := by rw [hq]; simp
  have hqc : ((t.search.quarter.val : ℕ) : ℤ) < 4 := by exact_mod_cast hql
  rw [hv0, hq0] at hb
  push_cast at hb ⊢
  omega

#print axioms double_exit_debt_ge

/-- **NAMED — `hE` is supplied by the window length.**  `double_leg_entries`
asks for `E + 1 ≤ value t.search.debt` at the `.double` exit; by
`double_exit_debt_ge` this follows from a purely numeric inequality on the
number of ticks the doubling phase ran. -/
theorem double_exit_debt_bound {as : List Bool} {v t : SearchVM} {E : ℤ}
    (hr : DoubleTrace as v t) (hmt : t.search.mode = Mode.double)
    (hwt : positive t.search.work = false)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hlen : 4 * (E + 1) + 4 * ((as.count true : ℕ) : ℤ) + 3 ≤ ((as.length : ℕ) : ℤ)) :
    E + 1 ≤ value t.search.debt := by
  have h := double_exit_debt_ge hr hmt hwt hv0 hq
  omega

#print axioms double_exit_debt_bound

/-- **NAMED — the `.double` leg dispatches into the next stage, with `hE`
discharged.**  This is `CloseoutPreload17.double_leg_entries` with its exit-debt
hypothesis replaced by the window-length inequality of `double_exit_debt_bound`
— residue 3 of `CloseoutPreload17` §3, closed. -/
theorem double_leg_entries_window {c' : GalilScaffoldPlace.Place} {k Rad D mw : ℕ}
    {a : Bool} {bs : List Bool} {v t t' : SearchVM}
    (hr : DoubleTrace bs v t)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hvc : Canonical v.search.debt)
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ 2 * mw) (hstage : 3 * Rad ≤ 5 * k)
    (hlen : 4 * (stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ) + 1)
        + 4 * ((bs.count true : ℕ) : ℤ) + 3 ≤ ((bs.length : ℕ) : ℤ))
    (hs : searchStep c' a t t') (hdep : DepthAt t' D) (hD : D ≤ prepLen k)
    (hpost : PostRunP) :
    ∀ (as : List Bool),
      D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' :=
  double_leg_entries htm htw hts htl hcal hstage
    (double_exit_canonical hr htm htw hvc)
    (double_exit_debt_bound (E := stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ))
      hr htm htw hv0 hq hlen)
    hs hdep hD hpost

#print axioms double_leg_entries_window

/-!
## 4. What is left

Closed here, against `CloseoutPreload17` §3:

* **residue 1, partly.**  `pacedL_suffix_slack` is the sharp form of
  `CloseoutPreload5.pacedL_suffix`, and `pacedL_suffix_2047` rounds the slack to
  `≤ 2047` — the side condition `runP_exit_debt_at_exit_take` needs — from
  `PrefixPhase bs`, with `prefixPhase_of_short` / `prefixPhase_cons_*` as its
  closure rules.  **Still missing:** the machine fact that the preparation
  prefix of a stage really is phase-bounded, i.e. that the controller clock
  `c.clock` of `CloseoutPreload.RdPaced` equals `2048 - (phase of bs)`; that is
  a statement about `GalilScaffoldMatchClock`, not about `PacedL`.
* **residue 2, corrected.**  The `.wait` leg's measure is its *comparison
  count*, and it equals the entry debt exactly (`wait_leg_count`); under pacing
  this bounds the leg's tick count from **below** (`wait_leg_length_of_debt`).
  The bound conjectured in `CloseoutPreload17` §3 (2) — tick count ≤ entry debt
  — is therefore false.  **Still missing:** an *upper* bound on the leg, which
  needs a liveness clause (no unbounded stall on background events), and then
  the conversion of that bound into the next stage's `DepthAt` budget.
* **residue 3, closed.**  `double_exit_debt_bound` derives `hE` from the window
  length, and `double_leg_entries_window` is `double_leg_entries` with `hE`
  discharged.

**NOT closed — `postRunP_of_machine` is not proved here.**  With residue 3
closed and residue 1 reduced to a clock-phase fact, the one genuinely open
input is residue 2's upper bound on the `.wait` leg (equivalently: that a stage
completes within its own event budget), together with the
`GalilScaffoldMatchClock` phase identity feeding `PrefixPhase`.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload18
