import PalPeg.CloseoutPreload14

/-!
# The run phase's own length bound

`CloseoutPreload14` §4 leaves a single residue: `runP_exit_debt` charges the
`.run` entry `pacedComparisons 2048 L` where `L` is the run phase's event
count, and *nothing yet bounds `L`*.

This file supplies that bound, and it needs no new hypothesis: the measure of a
`.run` phase is already present in `CloseoutReadyStage.DpSafeStage` — the
*charged prefix* `pre`, the events the stage's debt has paid for in advance.
`CloseoutReadyStage.dpSafeStage_pre_ne_nil` says a running DP always has a
non-empty charged prefix left, and `dpSafeStage_step` says every quantum eats
one of its cells.  So the charged prefix is a strictly decreasing measure of
the `.run` phase, and a run trace that is *still running* is strictly shorter
than its charged prefix.

* §1 `DpCharged` — `DpSafeStage` with the charged prefix exposed, and its two
  machine lemmas (non-emptiness at a running DP, and the step).
* §2 `runTrace_charged` / `runTrace_length_lt` — **the measure.**  A
  `CloseoutPreload13.RunTrace` consumes its events off the charged prefix, and
  while the phase has not left `.run` the prefix is not exhausted.
* §3 `run_length_le_dpEvents` — the bound in the shape `CloseoutPreload14` asks
  for: with the charged prefix taken to be the stage's own DP budget, a `.run`
  phase of window `w` runs for at most `dpEvents w.length` events, so the exit
  tick lands at `L ≤ dpEvents w.length`.
* §4 `runP_exit_debt_of_stage` — the residue discharged: the entry budget
  `stageDebt Rad k + stageCredit k (2*m) + 1 + pacedComparisons 2048 L` is
  implied by `2 * stageDebt Rad k + stageCredit k (2*m) + 1`, because
  `CloseoutDebtAudit.stage_budget_closes1` pays the paced count of a whole
  stage window out of one `stageDebt`.
* §5 the residue that remains (`CloseoutPreload8.PostRun` is *not* closed).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

namespace PalPeg.CloseoutPreload15

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat reset)
open PalPeg.GalilScaffoldSearchRun (SafeQuanta)
open PalPeg.GalilBranchInvariants2 (DpReached dpReached_step)
open PalPeg.CloseoutReadyStage (DpSafeStage dpSafeStage_pre_ne_nil dpEvents_budget PacedL)
open PalPeg.CloseoutDebtAudit (dpEvents pacedComparisons stageWindow1 stage_budget_closes1)
open PalPeg.CloseoutPreload11 (stageCredit)
open PalPeg.CloseoutPreload13 (RunTrace run_step_quanta)
open PalPeg.CloseoutPreload14 (RunTraceP runP_exit_debt)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The charged prefix, exposed -/

/-- **NAMED — `CloseoutReadyStage.DpSafeStage` with its charged prefix named.**
`DpSafeStage v as` hides the split `as = pre ++ post`; the measure of the run
phase is `pre`, so we carry it. -/
def DpCharged (v : SearchVM) (pre : List Bool) : Prop :=
  ∃ (w : List (Fin 3)) (lower : ℕ) (s0 : State) (bs : List Bool),
    3186 * w.length + 1683 ≤ 64 * (bs ++ pre).length ∧ s0.mode = Mode.run ∧
    Canonical s0.debt ∧ (((bs ++ pre).count true : ℤ)) ≤ value s0.debt ∧
    DpReached w lower s0 bs v.search v.dp

/-- A `DpCharged` witness is a `DpSafeStage` witness for any continuation. -/
theorem dpSafeStage_of_charged {v : SearchVM} {pre post : List Bool}
    (h : DpCharged v pre) : DpSafeStage v (pre ++ post) := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  exact ⟨w, lower, s0, bs, pre, post, rfl, hbud, hs0, hc, hb, hreach⟩

/-- **The charged prefix is non-empty while the DP runs.**  Directly
`CloseoutReadyStage.dpSafeStage_pre_ne_nil`. -/
theorem dpCharged_ne_nil {v : SearchVM} {pre : List Bool}
    (hm : v.search.mode = Mode.run) (h : DpCharged v pre) : pre ≠ [] := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  exact dpSafeStage_pre_ne_nil (as := pre ++ ([] : List Bool)) (post := []) hm rfl
    hbud hs0 hc hb hreach

/-- **One quantum eats one cell of the charged prefix.**  The debt ledger moves
the consumed event from the prefix into the already-run part `bs`, so the
budget and the count clause are unchanged. -/
theorem dpCharged_step {v v' : SearchVM} {a : Bool} {pre : List Bool}
    (h : DpCharged v (a :: pre))
    (hq : SafeQuanta v.search v.dp [a] v'.search v'.dp) :
    DpCharged v' pre := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  refine ⟨w, lower, s0, bs ++ [a], ?_, hs0, hc, ?_, dpReached_step hreach hq⟩
  · have hlen : ((bs ++ [a]) ++ pre).length = (bs ++ a :: pre).length := by simp
    rw [hlen]; exact hbud
  · have hcnt : ((bs ++ [a]) ++ pre).count true = (bs ++ a :: pre).count true := by
      simp [List.count_append]
    rw [hcnt]; exact hb

#print axioms dpCharged_ne_nil
#print axioms dpCharged_step

/-! ## 2. The measure -/

/-- **NAMED — a run trace consumes its events off the charged prefix.**  A
`CloseoutPreload13.RunTrace` of events `as`, started at a DP whose charged
prefix is `pre` and whose events continue as `as ++ rest = pre ++ post`, leaves
the charged prefix `pre` with exactly `as` removed from its front. -/
theorem runTrace_charged {as rest pre post : List Bool} {v t : SearchVM}
    (hr : RunTrace as v t) (hsplit : as ++ rest = pre ++ post)
    (h : DpCharged v pre) :
    ∃ pre' : List Bool, pre = as ++ pre' ∧ DpCharged t pre' := by
  induction hr generalizing pre with
  | nil w => exact ⟨pre, by simp, h⟩
  | cons c a as v v' t hm hs hrest ih =>
      have hne : pre ≠ [] := dpCharged_ne_nil hm h
      cases pre with
      | nil => exact absurd rfl hne
      | cons p pre =>
          have hp : p = a := by
            have := (List.cons.inj hsplit).1
            simpa using this.symm
          subst hp
          have hrest' : as ++ rest = pre ++ post := by
            simpa using (List.cons.inj hsplit).2
          obtain ⟨hq, -, -⟩ := run_step_quanta hm hs
          obtain ⟨pre', hpre', hch⟩ := ih hrest' (dpCharged_step h hq)
          exact ⟨pre', by rw [hpre']; simp, hch⟩

#print axioms runTrace_charged

/-- **NAMED — the length bound.**  A run trace that has *not* left `.run` is
strictly shorter than the charged prefix it started with: the prefix is a
decreasing measure and is still non-empty at the end of the trace. -/
theorem runTrace_length_lt {as rest pre post : List Bool} {v t : SearchVM}
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hsplit : as ++ rest = pre ++ post) (h : DpCharged v pre) :
    as.length < pre.length := by
  obtain ⟨pre', hpre', hch⟩ := runTrace_charged hr hsplit h
  have hne : pre' ≠ [] := dpCharged_ne_nil hmt hch
  have hlen : pre.length = as.length + pre'.length := by rw [hpre']; simp
  have : 0 < pre'.length := List.length_pos_iff.mpr hne
  omega

#print axioms runTrace_length_lt

/-! ## 3. The bound in stage shape -/

/-- The charged prefix at a stage entry: the DP machine is the preload of the
window `w`, and the prefix charged is any list long enough for the DP's own
instruction budget whose comparisons the entry debt already covers. -/
theorem dpCharged_entry {v : SearchVM} {w : List (Fin 3)} {lower : ℕ} {pre : List Bool}
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hbud : 3186 * w.length + 1683 ≤ 64 * pre.length)
    (hc : Canonical v.search.debt)
    (hb : ((pre.count true : ℤ)) ≤ value v.search.debt) :
    DpCharged v pre := by
  refine ⟨w, lower, v.search, [], by simpa using hbud, hm, hc, by simpa using hb, ?_⟩
  show SafeQuanta v.search ⟨GalilScaffoldPreload.initial w lower, false⟩ [] v.search v.dp
  rw [hdp]
  exact .nil _ _

/-- **NAMED — the fact `CloseoutPreload14` §4 names: a `.run` phase exits
inside the stage's own DP event budget.**  Taking the charged prefix to be a
list of exactly `dpEvents w.length` events — the budget
`CloseoutReadyStage.dpEvents_budget` certifies is long enough — the run trace
up to the last still-running state is shorter than it, so the whole phase,
exit tick included, has at most `dpEvents w.length` events. -/
theorem run_length_le_dpEvents {as rest pre post : List Bool} {v t : SearchVM}
    {w : List (Fin 3)} {lower : ℕ}
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hlen : pre.length = dpEvents w.length)
    (hc : Canonical v.search.debt)
    (hb : ((pre.count true : ℤ)) ≤ value v.search.debt)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hsplit : as ++ rest = pre ++ post) :
    as.length + 1 ≤ dpEvents w.length := by
  have hbud : 3186 * w.length + 1683 ≤ 64 * pre.length := by
    rw [hlen]; exact dpEvents_budget w.length
  have := runTrace_length_lt hr hmt hsplit (dpCharged_entry hdp hm hbud hc hb)
  omega

#print axioms run_length_le_dpEvents

/-! ## 4. The residue of `CloseoutPreload14` discharged -/

/-- `pacedComparisons` is monotone in the event count. -/
theorem pacedComparisons_mono {d n n' : ℕ} (h : n ≤ n') :
    pacedComparisons d n ≤ pacedComparisons d n' := by
  unfold pacedComparisons
  exact Nat.succ_le_succ (Nat.div_le_div_right h)

/-- **NAMED — the entry budget `CloseoutPreload14.runP_exit_debt` asks for is
implied by one extra `stageDebt`.**  The paced comparison count of a whole
stage window is at most `stageDebt Rad k` (`stage_budget_closes1`), so an entry
debt of `2 * stageDebt Rad k + stageCredit k (2*m) + 1` dominates
`stageDebt Rad k + stageCredit k (2*m) + 1 + pacedComparisons 2048 L` for every
run phase whose length `L` fits the stage window. -/
theorem entry_budget_of_stage {Rad k m L : ℕ}
    (hstage : 3 * Rad ≤ 5 * k) (hL : L ≤ dpEvents (stageWindow1 k)) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
        + (pacedComparisons 2048 L : ℤ)
      ≤ 2 * stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 := by
  have hmono : pacedComparisons 2048 L ≤ pacedComparisons 2048 (dpEvents (stageWindow1 k)) :=
    pacedComparisons_mono hL
  have hcast : ((pacedComparisons 2048 L : ℕ) : ℤ)
      ≤ ((pacedComparisons 2048 (dpEvents (stageWindow1 k)) : ℕ) : ℤ) := by
    exact_mod_cast hmono
  have hpay := stage_budget_closes1 (k := k) (Rad := Rad) hstage
  omega

#print axioms entry_budget_of_stage

/-- **NAMED — `CloseoutPreload14.runP_exit_debt` with its entry premise
discharged.**  This is the residue of `CloseoutPreload14` §4 closed: no
`pacedComparisons 2048 as.length` premise survives, only the stage's own
length bound and the calibrated stage debt. -/
theorem runP_exit_debt_of_stage {Rad k m slack L : ℕ} {as : List Bool} {v t : SearchVM}
    (hk : slack ≤ 2047) (h : RunTraceP slack as v t)
    (hstage : 3 * Rad ≤ 5 * k)
    (hlen : as.length = L) (hL : L ≤ dpEvents (stageWindow1 k))
    (hE : 2 * stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      ≤ value v.search.debt) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t.search.debt := by
  refine runP_exit_debt (Rad := Rad) (k := k) (m := m) hk h ?_
  have hb := entry_budget_of_stage (Rad := Rad) (k := k) (m := m) (L := L) hstage hL
  rw [hlen]
  omega

#print axioms runP_exit_debt_of_stage

/-- The same at an exit tick: the run trace up to the last running state is
strictly shorter than the stage's DP budget (§3), so the full event list
`as ++ [a]` still fits it, and §4's budget applies to the exit state. -/
theorem runP_exit_debt_at_exit {Rad k m slack : ℕ} {as rest pre post : List Bool}
    {v t t' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hk : slack ≤ 2047)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hwin : w.length = stageWindow1 k)
    (hprelen : pre.length = dpEvents w.length)
    (hc : Canonical v.search.debt)
    (hb : ((pre.count true : ℤ)) ≤ value v.search.debt)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hsplit : as ++ rest = pre ++ post)
    (hs : searchStep c a t t')
    (hp : PacedL 2048 slack (as ++ [a]))
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : 2 * stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      ≤ value v.search.debt) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t'.search.debt := by
  have hlt := run_length_le_dpEvents hdp hm hprelen hc hb hr hmt hsplit
  have hfull : RunTraceP slack (as ++ [a]) v t' :=
    ⟨PalPeg.CloseoutPreload13.runTrace_snoc hr hmt hs, hp⟩
  refine runP_exit_debt_of_stage (Rad := Rad) (k := k) (m := m)
    (L := (as ++ [a]).length) hk hfull hstage rfl ?_ hE
  have hlen : (as ++ [a]).length = as.length + 1 := by simp
  rw [hlen, ← hwin]
  exact hlt

#print axioms runP_exit_debt_at_exit

/-!
## 5. What is left

Closed here: the residue `CloseoutPreload14` §4 names.  The measure of the
`.run` phase is the *charged prefix* of `CloseoutReadyStage.DpSafeStage`, not
anything inside the search state: `runTrace_charged` shows each quantum eats
one cell of it, `runTrace_length_lt` that a still-running phase has not
exhausted it, and `run_length_le_dpEvents` that with the prefix taken to be the
stage's own DP budget the phase — exit tick included — fits
`dpEvents w.length`.  `runP_exit_debt_of_stage` / `runP_exit_debt_at_exit` then
carry `CloseoutPreload14.runP_exit_debt` with no `pacedComparisons` premise
left, at the cost of one extra `stageDebt Rad k` in the entry budget, which
`CloseoutDebtAudit.stage_budget_closes1` pays.

**NOT closed — `CloseoutPreload8.PostRun` is still open.**  What is missing is
no longer the run leg's arithmetic but the *plumbing* of the entry: to apply
`runP_exit_debt_at_exit` at a real stage one must produce, at the `.run` entry
reached by `CloseoutReadyStage`/`CloseoutPreload11.dpSafe_entry_km`, the
charged prefix `pre` in the split shape `as ++ rest = pre ++ post` with
`pre.length = dpEvents w.length` — i.e. the entry's `DpSafeStage` witness has
to be *re-cut* to exactly the budget length instead of the arbitrary prefix it
carries, which needs the event stream ahead of the entry to be at least that
long.  That length premise is `CloseoutPreload8.StagePrep`'s
`D + dpEvents (stageWindow1 k) ≤ bs.length + as.length`, so the remaining work
is threading that inequality into a `pre`/`post` split rather than proving
anything new about the machine.  The `.wait`/`.double` continuation
(`CloseoutPreload14` §3) and `CloseoutPreload12.runEntriesS_of_double_exit`
then have to be chained into `RunEntriesS` itself.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload15
