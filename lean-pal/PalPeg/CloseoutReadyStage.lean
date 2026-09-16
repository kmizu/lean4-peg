import PalPeg.CloseoutDebtAudit
import PalPeg.CloseoutReportCase

/-!
# The stage-cut DP budget: `DpSafeStage`, `SearchReadyS`, `ReadyPacedS`

`CloseoutDebtAudit` showed that `GalilSearchReadyInv.DpSafeRem v as` charges the
*whole* remaining event list `as` against the debt held at the `.run` entry, and
that this over-charge is what refuted `RunEntriesAtBegin`,
`GalilReplaySpan.ReplayFitsStage`, and the `ReadyFuel … (headRank r.right)`
premise of `GalilSegmentConstructB`.  The machine's real obligation is local:
only the comparisons between the `.run` entry and the halt of that stage's DP
are charged, and the arithmetic of that local obligation closes unconditionally
(`CloseoutDebtAudit.stage_budget_closes`).

This file installs the cut invariant.

* `DpSafeStage v as` charges only a **prefix** `pre` of `as` that is already long
  enough to run the DP to its halt (`3186*|w|+1683 ≤ 64*|bs ++ pre|`); the
  suffix `post` is free.  It implies `DpSafeHere` verbatim (`dpSafeHere_of_stage`)
  and is preserved by one quantum (`dpSafeStage_step`) — the charged prefix is
  never empty at a `.run` state (`dpSafeStage_pre_ne_nil`, by
  `safeQuanta_exists_of_reached`: a DP whose budget is already spent is not in
  `.run`), so the consumed event always comes out of `pre`, never out of `post`.

* `PacedL d k as` is the clock-synchronisation of the event stream: at most one
  comparison per `d` ticks, with `k` the slack the current clock phase allows
  (`k = d - clock`).  It is exactly what the scan loop emits: a background tick
  adds a unit of slack (`pacedL_false`), and a comparison may fire only when the
  slack is full and resets it (`pacedL_true`).

* `dpSafeStage_entry_paced` is the point of the exercise: **at a calibrated
  stage entry, a clock-paced event stream of any length whatsoever fits the stage
  debt.**  No upper bound on `|as|` and no bound on `as.count true` is needed —
  only the pacing.  This is the form `RunEntriesAtBegin` should have had; its
  budget-free version is true.

* `ReadyRemS`/`SearchReadyS`/`RunEntriesS` re-run `GalilSearchReadyInv` and
  `GalilLeafPres` on the cut invariant, and `ReadyPacedS v n k` is the closure
  over paced lists that replaces `GalilSegmentConstructB.ReadyFuel v n K`.  The
  match budget `K` is gone: the entry premise of `segment_of_invLPCS` quantifies
  over *every* event list that is long enough and clock-paced, which is every
  list the scan loop can emit.

* §5–§6 re-prove `GalilSegmentConstructB.watchSegE_constructB` /
  `segment_of_invLPCB` and `CloseoutReportCase.reachAtC3_of_target_matchF` /
  `reachAtC3_of_crossF` on `ReadyPacedS`.

## What is still named

`RunEntriesS` — the `.run`-entry datum.  `dpSafeStage_entry_paced` proves the
*budget* half of it outright for every paced stream; what stays is the
identification of the handed-over DP machine with `GalilScaffoldPreload.initial
w lower` for the calibrated window `w` of the stage, together with the entry
debt `stageDebt Rad k ≤ value debt` — a whole-phase statement
(`GalilScaffoldPreparePaced.PacedPrepared` / `prepare_complete`), not a per-tick
invariant.  `runEntryS_of_entryPaced` packages exactly that hand-over into
`DpSafeStage`, so the residual is now a statement about the preparation phase
alone, with no event-budget side condition attached.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutReadyStage

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilBranchInvariants2
open PalPeg.GalilSearchReadyInv
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open PalPeg.GalilScaffoldCounter (Counter Canonical value zero reset inc_canonical)
open PalPeg.GalilTickFun2
open PalPeg.GalilSegmentConstruct PalPeg.GalilLeafPres PalPeg.GalilLeafEnds
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleLeaves2
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleMC3
open PalPeg.GalilSegmentConstructB PalPeg.GalilInvPlus3 PalPeg.CloseoutReportCase
open PalPeg.GalilLeafReport PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilLexMeasure PalPeg.GalilGlueBLeaves PalPeg.GalilOracleM
open PalPeg.GalilFinalAssembly2 PalPeg.GalilLeafPos PalPeg.GalilReadyFuelUses
open PalPeg.GalilOneFallback PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilScaffoldSearchRun (SafeQuanta)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow pacedComparisons stage_budget_closes)

/-! ## 1. The cut budget -/

/-- **The stage-cut DP budget.**  Only a prefix `pre` of the events still ahead
is charged against the debt held at the `.run` entry, and that prefix is already
long enough to carry the DP to its halt.  The suffix `post` — the events after
the DP stops, which belong to the *next* stage's ledger — is free. -/
def DpSafeStage (v : SearchVM) (as : List Bool) : Prop :=
  ∃ (w : List (Fin 3)) (lower : ℕ) (s0 : GalilScaffoldSearchFinish.State)
    (bs pre post : List Bool),
    as = pre ++ post ∧
    3186*w.length+1683 ≤ 64*(bs ++ pre).length ∧ s0.mode = .run ∧
    Canonical s0.debt ∧ (((bs ++ pre).count true : ℤ)) ≤ value s0.debt ∧
    DpReached w lower s0 bs v.search v.dp

/-- The cut budget is still a `DpSafeHere` witness: take the charged prefix as
the suffix `DpSafeHere` quantifies over. -/
theorem dpSafeHere_of_stage {v : SearchVM} {as : List Bool} (h : DpSafeStage v as) :
    DpSafeHere v.search v.dp := by
  obtain ⟨w, lower, s0, bs, pre, post, -, hbud, hs0, hc, hb, hreach⟩ := h
  exact ⟨w, lower, s0, bs, pre, hbud, hs0, hc, hb, hreach⟩

/-- `DpSafeStage` is weaker than `DpSafeRem`: charge the whole remaining list. -/
theorem dpSafeStage_of_rem {v : SearchVM} {as : List Bool} (h : DpSafeRem v as) :
    DpSafeStage v as := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  exact ⟨w, lower, s0, bs, as, [], by simp, hbud, hs0, hc, hb, hreach⟩

/-- **The charged prefix is never empty at a running DP.**  If it were, the
budget `3186*|w|+1683 ≤ 64*|bs|` would already be spent, and
`safeQuanta_exists_of_reached` would place the halt at the current
configuration, contradicting `.run`. -/
theorem dpSafeStage_pre_ne_nil {v : SearchVM} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ} {s0 : GalilScaffoldSearchFinish.State}
    {bs pre post : List Bool} (hm : v.search.mode = .run)
    (hsplit : as = pre ++ post)
    (hbud : 3186*w.length+1683 ≤ 64*(bs ++ pre).length) (hs0 : s0.mode = .run)
    (hc : Canonical s0.debt) (hb : (((bs ++ pre).count true : ℤ)) ≤ value s0.debt)
    (hreach : DpReached w lower s0 bs v.search v.dp) : pre ≠ [] := by
  rintro rfl
  have hbud' : 3186*w.length+1683 ≤ 64*(bs ++ ([] : List Bool)).length := by simpa using hbud
  have hb' : (((bs ++ ([] : List Bool)).count true : ℤ)) ≤ value s0.debt := by simpa using hb
  obtain ⟨used, rest, t, y, hsp, hq, hmode, -⟩ :=
    safeQuanta_exists_of_reached w lower bs [] s0 v.search v.dp hbud' hs0 hc hb' hreach hm
  have hu : used = [] := by
    cases used with
    | nil => rfl
    | cons b us => simp at hsp
  subst hu
  obtain ⟨rfl, -⟩ := safe_quanta_nil hq
  exact hmode hm

/-- **Preservation.**  One quantum moves the event out of the charged prefix. -/
theorem dpSafeStage_step {v v' : SearchVM} {a : Bool} {as : List Bool}
    (hm : v.search.mode = .run) (h : DpSafeStage v (a :: as))
    (hq : SafeQuanta v.search v.dp [a] v'.search v'.dp) :
    DpSafeStage v' as := by
  obtain ⟨w, lower, s0, bs, pre, post, hsplit, hbud, hs0, hc, hb, hreach⟩ := h
  have hne : pre ≠ [] := dpSafeStage_pre_ne_nil hm hsplit hbud hs0 hc hb hreach
  cases pre with
  | nil => exact absurd rfl hne
  | cons p pre =>
    have hp : p = a := by simpa using (List.cons.inj hsplit).1.symm
    subst hp
    have has : as = pre ++ post := by simpa using (List.cons.inj hsplit).2
    refine ⟨w, lower, s0, bs ++ [p], pre, post, has, ?_, hs0, hc, ?_,
      dpReached_step hreach hq⟩
    · have hlen : ((bs ++ [p]) ++ pre).length = (bs ++ p :: pre).length := by simp
      rw [hlen]; exact hbud
    · have hcnt : ((bs ++ [p]) ++ pre).count true = (bs ++ p :: pre).count true := by
        simp [List.count_append]
      rw [hcnt]; exact hb

/-- The entry form: nothing consumed yet, the DP is at its preload, and the
charged prefix is a prefix of the events ahead. -/
theorem dpSafeStage_entry (v : SearchVM) (w : List (Fin 3)) (lower : ℕ)
    (as pre post : List Bool)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run) (hsplit : as = pre ++ post)
    (hbud : 3186*w.length+1683 ≤ 64*pre.length)
    (hc : Canonical v.search.debt)
    (hb : ((pre.count true : ℤ)) ≤ value v.search.debt) :
    DpSafeStage v as := by
  refine ⟨w, lower, v.search, [], pre, post, hsplit, by simpa using hbud, hmode, hc,
    by simpa using hb, ?_⟩
  show SafeQuanta v.search ⟨GalilScaffoldPreload.initial w lower, false⟩ [] v.search v.dp
  rw [hdp]
  exact .nil _ _

#print axioms dpSafeHere_of_stage
#print axioms dpSafeStage_pre_ne_nil
#print axioms dpSafeStage_step
#print axioms dpSafeStage_entry

/-! ## 2. Clock pacing, and the budget-free entry theorem -/

/-- **The clock synchronisation of the event stream.**  `PacedL d k as` says
that every prefix of `as` holds at most one comparison per `d` ticks, with `k`
units of slack for the current clock phase: `k = d - clock`, so a fresh clock
has no slack and a clock about to fire has `d-1`. -/
def PacedL (d k : ℕ) (as : List Bool) : Prop :=
  ∀ n : ℕ, d * ((as.take n).count true) ≤ n + k

theorem pacedL_mono {d k k' : ℕ} {as : List Bool} (hk : k ≤ k') (h : PacedL d k as) :
    PacedL d k' as := fun n => le_trans (h n) (by omega)

theorem pacedL_nil (d k : ℕ) : PacedL d k ([] : List Bool) := by
  intro n; simp

/-- Background events only add slack. -/
theorem pacedL_false {d k k' : ℕ} {as : List Bool} (hk : k' ≤ k + 1) (h : PacedL d k' as) :
    PacedL d k (false :: as) := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have hcnt : ((false :: as).take (n+1)).count true = (as.take n).count true := by
      simp [List.take_succ_cons]
    rw [hcnt]
    have := h n
    omega

/-- A comparison may fire only when the slack is full, and it resets it. -/
theorem pacedL_true {d k : ℕ} {as : List Bool} (hd : d ≤ k + 1) (h : PacedL d 0 as) :
    PacedL d k (true :: as) := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have hcnt : ((true :: as).take (n+1)).count true = (as.take n).count true + 1 := by
      simp [List.take_succ_cons]
    rw [hcnt]
    have := h n
    have hmul : d * ((as.take n).count true + 1) = d * ((as.take n).count true) + d := by ring
    omega

theorem pacedL_replicate_false (d k n : ℕ) :
    PacedL d k (List.replicate n false) := by
  intro m
  have : ((List.replicate n false).take m).count true = 0 := by
    rw [List.take_replicate, List.count_replicate]
    simp
  rw [this]
  omega

/-- The count a paced stream can put into a window of `N` events, at the clock
pacing `2048`. -/
theorem pacedL_count_take {k N : ℕ} {as : List Bool} (hk : k ≤ 2047)
    (h : PacedL 2048 k as) :
    (as.take N).count true ≤ PalPeg.CloseoutDebtAudit.pacedComparisons 2048 N := by
  have h0 := h N
  have h1 := Nat.div_add_mod N 2048
  have h2 : N % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
  unfold PalPeg.CloseoutDebtAudit.pacedComparisons
  omega

/-- `64 * dpEvents W` really covers the DP's instruction budget. -/
theorem dpEvents_budget (W : ℕ) : 3186*W+1683 ≤ 64 * dpEvents W := by
  unfold PalPeg.CloseoutDebtAudit.dpEvents
  have h1 := Nat.div_add_mod (3186*W+1683+63) 64
  have h2 : (3186*W+1683+63) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The budget-free entry theorem.**  At a calibrated stage entry — the DP
machine handed over is the preload of the stage window `w` of a stage with lower
bound `k`, and the entry debt is the stage debt `stageDebt Rad k` — *every*
clock-paced event stream fits, of **any length**.  No upper bound on `as.length`
and no bound on `as.count true` appears: the charged prefix is the DP's own
window `dpEvents (stageWindow k)`, and `CloseoutDebtAudit.stage_budget_closes`
pays for it unconditionally.

This is the statement `GalilReplaySpan.RunEntriesAtBegin` should have carried;
its budget-free version is true, whereas the `DpSafeRem` version that charges
the whole suffix is refuted (`CloseoutReadinessAudit`). -/
theorem dpSafeStage_entry_paced (v : SearchVM) (w : List (Fin 3)) (lower Rad k slack : ℕ)
    (as : List Bool)
    (hw : w.length = stageWindow k)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run)
    (hc : Canonical v.search.debt)
    (hstage : 3 * Rad ≤ 5 * k)
    (hdebt : PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v.search.debt)
    (hslack : slack ≤ 2047)
    (hlen : dpEvents (stageWindow k) ≤ as.length)
    (hpaced : PacedL 2048 slack as) :
    DpSafeStage v as := by
  set N : ℕ := dpEvents (stageWindow k) with hN
  refine dpSafeStage_entry v w lower as (as.take N) (as.drop N) hdp hmode
    (by rw [List.take_append_drop]) ?_ hc ?_
  · have hlenpre : (as.take N).length = N := by
      rw [List.length_take]; omega
    rw [hlenpre, hw, hN]
    exact dpEvents_budget _
  · have h1 : (as.take N).count true ≤ pacedComparisons 2048 N :=
      pacedL_count_take hslack hpaced
    have h2 : ((pacedComparisons 2048 N : ℕ) : ℤ)
        ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) := stage_budget_closes hstage
    have h3 : (((as.take N).count true : ℕ) : ℤ) ≤ ((pacedComparisons 2048 N : ℕ) : ℤ) :=
      Int.ofNat_le.mpr h1
    omega

#print axioms pacedL_false
#print axioms pacedL_true
#print axioms pacedL_count_take
#print axioms dpEvents_budget
#print axioms dpSafeStage_entry_paced

/-! ## 3. `SearchReady` over the cut budget -/

/-- `GalilSearchReadyInv.ReadyRem` on the cut budget. -/
def ReadyRemS (v : SearchVM) (as : List Bool) : Prop :=
  PrepInv v.toPrep ∧ (v.search.mode = .run → DpSafeStage v as)

theorem searchReady_of_readyRemS {v : SearchVM} {as : List Bool} (h : ReadyRemS v as) :
    SearchReady v :=
  ⟨h.1, fun hm => dpSafeHere_of_stage (h.2 hm)⟩

theorem readyRemS_of_readyRem {v : SearchVM} {as : List Bool} (h : ReadyRem v as) :
    ReadyRemS v as := ⟨h.1, fun hm => dpSafeStage_of_rem (h.2 hm)⟩

/-- **Boot.**  At a stage restart the search sits in `.grow`, so both halves are
vacuous for every remaining-event list. -/
theorem readyRemS_begin (v : SearchVM) (lower radius : Counter)
    (h : v.search = GalilScaffoldSearchFinish.begin lower radius) (as : List Bool) :
    ReadyRemS v as := readyRemS_of_readyRem (searchReady_begin v lower radius h as)

theorem readyRemS_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (as : List Bool) :
    ReadyRemS (searchLens.get r) as :=
  readyRemS_of_readyRem (searchReady_restarted hR as)

/-- `GalilSearchReadyInv.RunEntry` on the cut budget. -/
def RunEntryS (center : GalilScaffoldPlace.Place) (a : Bool) (v v' : SearchVM)
    (as : List Bool) : Prop :=
  searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run → DpSafeStage v' as

/-- **Preservation, one tick.**  `GalilSearchReadyInv.searchReady_step` re-run on
the cut budget: every branch is discharged verbatim, and the `.run` branch now
appeals to `dpSafeStage_step`, which takes the consumed event out of the charged
prefix instead of out of the whole suffix. -/
theorem readyRemS_step (center : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool)
    {v v' : SearchVM} (hstep : searchStep center a v v') (h : ReadyRemS v (a :: as))
    (hentry : RunEntryS center a v v' as) :
    ReadyRemS v' as := by
  classical
  obtain ⟨hprep, hdp⟩ := h
  unfold searchStep at hstep
  cases hm : v.search.mode with
  | idle =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | found =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | missed =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | grow =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      have hmode : v'.search.mode = .grow := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, growStep_mode]
        exact hm
      refine ⟨prepInv_of_notPrep (Or.inr (Or.inl hmode)), fun hr => ?_⟩
      rw [hmode] at hr; simp at hr
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      have hmode : v'.search.mode = .lower := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, prepare_mode]
      refine ⟨?_, fun hr => ?_⟩
      · rw [hstep]
        show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
        exact prepInv_afterAdvance a (prepInv_prepare _ _ _)
      · rw [hmode] at hr; simp at hr
  | lower =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | lowerHome =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | copy =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | home =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | run =>
    rw [hm] at hstep
    obtain ⟨hq, _, _⟩ := hstep
    refine ⟨?_, fun _ => dpSafeStage_step hm (hdp hm) hq⟩
    by_cases hrun : v'.search.mode = .run
    · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inl hrun)))
    · rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm hrun with hf | hmi | hw | hd
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inl hf))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmi)))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw))))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))))
  | wait =>
    rw [hm] at hstep
    have hmode : v'.search.mode = .double ∨ v'.search.mode = .wait := by
      rw [hstep]
      show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _ ∨
        (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _
      rw [advance_mode]
      rcases waitStep_mode v.search with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hm)
    refine ⟨?_, fun hr => ?_⟩
    · rcases hmode with h1 | h1
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
    · rcases hmode with h1 | h1 <;> rw [h1] at hr <;> simp at hr
  | double =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      have hmode : v'.search.mode = .double := by
        rw [hstep]
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        rw [advance_mode, doubleStep_mode]
        exact hm
      refine ⟨prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmode)))))),
        fun hr => ?_⟩
      rw [hmode] at hr; simp at hr
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      have hmode : v'.search.mode = .lower := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, prepare_mode]
      refine ⟨?_, fun hr => ?_⟩
      · rw [hstep]
        show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
        exact prepInv_afterAdvance a (prepInv_prepare _ _ _)
      · rw [hmode] at hr; simp at hr

/-- `GalilLeafPres.RunEntriesAll` on the cut budget. -/
def RunEntriesS : List Bool → SearchVM → Prop
  | [], _ => True
  | a :: as, v =>
      ∀ (center : GalilScaffoldPlace.Place) (v' : SearchVM), searchStep center a v v' →
        RunEntryS center a v v' as ∧ RunEntriesS as v'

/-- `GalilLeafPres.SearchReadyB` on the cut budget. -/
def SearchReadyS (v : SearchVM) (as : List Bool) : Prop :=
  ReadyRemS v as ∧ RunEntriesS as v

theorem searchReadyS_ready {v : SearchVM} {as : List Bool} (h : SearchReadyS v as) :
    SearchReady v := searchReady_of_readyRemS h.1

theorem searchReadyS_step {center : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    {v v' : SearchVM} (hstep : searchStep center a v v') (h : SearchReadyS v (a :: as)) :
    SearchReadyS v' as := by
  obtain ⟨hrem, hE⟩ := h
  obtain ⟨hentry, hrest⟩ := hE center v' hstep
  exact ⟨readyRemS_step center a as hstep hrem hentry, hrest⟩

/-- **Preservation through the scan tick** — the replacement for the refuted
`hpres` leaf, on the cut budget. -/
theorem searchReadyS_effect (P : Shared) {a : Bool} {as : List Bool} {s : GalilVM}
    {v : SearchVM} (hidle : s.chain = ChainVM.idle)
    (h : SearchReadyS (searchLens.get s) (a :: as)) (he : searchEffect P a s v) :
    SearchReadyS v as := by
  rcases he with ⟨_, hs⟩ | ⟨hne, _⟩
  · exact searchReadyS_step hs h
  · exact absurd hidle hne

theorem searchReadyS_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (as : List Bool)
    (hE : RunEntriesS as (searchLens.get r)) : SearchReadyS (searchLens.get r) as :=
  ⟨readyRemS_restarted hR as, hE⟩

#print axioms readyRemS_begin
#print axioms readyRemS_step
#print axioms searchReadyS_step
#print axioms searchReadyS_effect
#print axioms searchReadyS_restarted

/-! ## 4. The paced closure: `ReadyPacedS` replaces `ReadyFuel` -/

/-- **The entry closure.**  `SearchReadyS` for *every* event list that is long
enough and clock-paced at the current phase.  Compared with
`GalilSegmentConstructB.ReadyFuel v n K` the match budget `K` is gone: the
comparisons are limited by the clock alone, which is what the scan loop
actually enforces, and the cut budget `DpSafeStage` no longer needs the whole
suffix to be short. -/
def ReadyPacedS (v : SearchVM) (n k : ℕ) : Prop :=
  ∀ as : List Bool, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as

theorem readyPacedS_ready {v : SearchVM} {n k : ℕ} (h : ReadyPacedS v n k) : SearchReady v :=
  searchReadyS_ready (h (List.replicate n false) (by simp) (pacedL_replicate_false _ _ _))

theorem readyPacedS_mono {v : SearchVM} {n n' k k' : ℕ} (hn : n ≤ n') (hk : k' ≤ k)
    (h : ReadyPacedS v n k) : ReadyPacedS v n' k' :=
  fun as hlen hp => h as (le_trans hn hlen) (pacedL_mono hk hp)

/-- A background tick spends one unit of fuel and buys one unit of slack. -/
theorem readyPacedS_effect_false (P : Shared) {n k k' : ℕ} {s : GalilVM} {v : SearchVM}
    (hk : k' ≤ k + 1) (hidle : s.chain = ChainVM.idle)
    (h : ReadyPacedS (searchLens.get s) (n + 1) k) (he : searchEffect P false s v) :
    ReadyPacedS v n k' := by
  intro as hlen hp
  exact searchReadyS_effect P hidle
    (h (false :: as) (by simpa using hlen) (pacedL_false hk hp)) he

/-- A comparison may fire only on a full clock, and it resets the slack. -/
theorem readyPacedS_effect_true (P : Shared) {n k : ℕ} {s : GalilVM} {v : SearchVM}
    (hk : 2048 ≤ k + 1) (hidle : s.chain = ChainVM.idle)
    (h : ReadyPacedS (searchLens.get s) (n + 1) k) (he : searchEffect P true s v) :
    ReadyPacedS v n 0 := by
  intro as hlen hp
  exact searchReadyS_effect P hidle
    (h (true :: as) (by simpa using hlen) (pacedL_true hk hp)) he

/-- **Boot.**  At a stage restart the `ReadyRemS` half is free, so the closure
reduces to `RunEntriesS`. -/
theorem readyPacedS_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (n k : ℕ)
    (hE : ∀ as : List Bool, n ≤ as.length → PacedL 2048 k as →
      RunEntriesS as (searchLens.get r)) :
    ReadyPacedS (searchLens.get r) n k :=
  fun as hlen hp => searchReadyS_restarted hR as (hE as hlen hp)

#print axioms readyPacedS_ready
#print axioms readyPacedS_effect_false
#print axioms readyPacedS_effect_true
#print axioms readyPacedS_restarted

/-! ## 5. The segment construction on the paced closure -/

/-- **`GalilSegmentConstructB.watchSegE_constructB` on `ReadyPacedS`.**  Same
fuel induction, same seven exits; the match budget `headRank s.right` is
replaced by the clock slack, which the loop itself maintains: a background tick
spends one unit of fuel and gains a unit of slack, a comparison spends one unit
of fuel and resets the slack to zero, and a comparison can only be taken at
`c.clock = 1`, where the slack is full.  The invariant relating the two is
`2048 ≤ c.clock + k`. -/
theorem watchSegE_constructS (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM) (r k : ℕ), c.mode = .scan → 1 ≤ c.clock →
      2048 ≤ c.clock + k → s.chain = ChainVM.idle →
      ReadyPacedS (searchLens.get s) n k →
      MInv raw c s → ScanInvariant raw (position s.center) r s.left s.right →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM) (r' : ℕ),
        WatchSegE P q first 2048 es c s c' t ∧
        c'.mode = .scan ∧ 1 ≤ c'.clock ∧ t.chain = ChainVM.idle ∧
        SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
        ScanInvariant raw (position t.center) r' t.left t.right ∧
        (es.length = n ∨ SegEnd P c' t) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c s r k hm hclk hk hidle hsr hM hi
    exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, readyPacedS_ready hsr, hM, hi, Or.inl rfl⟩
  | succ n ih =>
    intro c s r k hm hclk hk hidle hsr hM hi
    have hrdy : SearchReady (searchLens.get s) := readyPacedS_ready hsr
    by_cases hav : canRight s.right
    · by_cases hrp : c.replaying = true
      · rcases Nat.lt_or_ge 1 c.clock with hlt | hle
        · -- `countR`
          obtain ⟨v, hv⟩ := hsearch s hrdy false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : ReadyPacedS (searchLens.get s') n (k + 1) := by
            rw [hget']; exact readyPacedS_effect_false P (le_refl _) hidle hsr hv
          have hM' : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
          have hi' : ScanInvariant raw (position s'.center) r s'.left s'.right := by
            rw [hl', hr', hC']; exact hi
          obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
            ih {c with clock := c.clock - 1} s' r (k + 1) hm (by simp; omega)
              (by simp; omega) hch' hsr' hM' hi'
          refine ⟨false :: es, c', t, r', .countR c s s' hm hrp hlt hidle hb hseg, hm', hclk',
            hidle', hsrt, hMt, hit, ?_⟩
          rcases hlen with h0 | h0
          · exact Or.inl (by simp [h0])
          · exact Or.inr h0
        · have hc1 : c.clock = 1 := le_antisymm hle hclk
          by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          have hmatch : read (left s.left) = read (right s.right) :=
            replay_match_of_minv hM hrp hav hi
          obtain ⟨vq, hq⟩ := hsearch s hrdy true
          by_cases hf : vq.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.found hc1 hav hmatch ⟨vq, hq, hf⟩)⟩
          · set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
            have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
            set u : GalilVM := replayDec true (afterCompare s vs vq) with hudef
            let o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output
            have ho : refresh (galilFrame P q first) u c.output o := by
              refine ⟨fun hl => ?_, fun hl => ?_⟩
              · have hl' : P.onLetter u := hl
                show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔
                  P.leftFirst u
                rw [if_pos hl']; exact decide_eq_true_iff
              · have hl' : ¬ P.onLetter u := hl
                show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
                rw [if_neg hl']
            have hidleU : u.chain = ChainVM.idle := by
              rw [hudef, replayDec_chain, afterCompare_chain]
            have hgetU : searchLens.get u = vq := by rw [hudef, replayDec_search]; rfl
            have hsrU : ReadyPacedS (searchLens.get u) n 0 := by
              rw [hgetU]
              exact readyPacedS_effect_true P (by omega) hidle hsr hq
            have hMU : MInv raw {c with clock := 2048, output := o, replaying := !(P.replayExhausted u)} u :=
              minv_matchR P hex o 2048 hrp rfl hav hi hM
            have hiU : ScanInvariant raw (position u.center) (r+1) u.left u.right := by
              have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
              rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
              exact h0
            obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
              ih {c with clock := 2048, output := o, replaying := !(P.replayExhausted u)} u (r+1) 0
                hm (by norm_num) (by norm_num) hidleU hsrU hMU hiU
            refine ⟨true :: es, c', t, r',
              .matchIdleR c s vs vq o hm hrp hc1 hav hidle rfl rfl rfl hmt hq hf ho hseg,
              hm', hclk', hidle', hsrt, hMt, hit, ?_⟩
            rcases hlen with h0 | h0
            · exact Or.inl (by simp [h0])
            · exact Or.inr h0
      · have hrp' : c.replaying = false := by
          cases hb : c.replaying with
          | false => rfl
          | true => exact absurd hb hrp
        rcases Nat.lt_or_ge 1 c.clock with hlt | hle
        · -- `count`
          obtain ⟨v, hv⟩ := hsearch s hrdy false
          by_cases hfb : v.search.mode = .found
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.foundBackground hclk ⟨v, hv, hfb⟩)⟩
          obtain ⟨s', hb, hch', hl', hr', hC', hrep', hget'⟩ :=
            idle_background_exists P q first s hidle hv hfb
          have hsr' : ReadyPacedS (searchLens.get s') n (k + 1) := by
            rw [hget']; exact readyPacedS_effect_false P (le_refl _) hidle hsr hv
          have hM' : MInv raw {c with clock := c.clock - 1} s' := minv_same rfl hr' hC' hrep' hM
          have hi' : ScanInvariant raw (position s'.center) r s'.left s'.right := by
            rw [hl', hr', hC']; exact hi
          obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
            ih {c with clock := c.clock - 1} s' r (k + 1) hm (by simp; omega)
              (by simp; omega) hch' hsr' hM' hi'
          refine ⟨false :: es, c', t, r', .count c s s' hm hrp' hav hlt hb hseg, hm', hclk',
            hidle', hsrt, hMt, hit, ?_⟩
          rcases hlen with h0 | h0
          · exact Or.inl (by simp [h0])
          · exact Or.inr h0
        · have hc1 : c.clock = 1 := le_antisymm hle hclk
          by_cases hlast : PopsIncoming s.right ∧ ∃ a, s.right.head.incoming = [a]
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.lastLetter hc1 hav hlast.1 hlast.2)⟩
          by_cases hmatch : read (left s.left) = read (right s.right)
          · obtain ⟨vq, hq⟩ := hsearch s hrdy true
            by_cases hf : vq.search.mode = .found
            · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
                Or.inr (.found hc1 hav hmatch ⟨vq, hq, hf⟩)⟩
            · set vs : ScanVM := ⟨left s.left, right s.right, ChainVM.idle⟩ with hvsdef
              have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
              set u : GalilVM := afterCompare s vs vq with hudef
              let o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output
              have ho : refresh (galilFrame P q first) u c.output o := by
                refine ⟨fun hl => ?_, fun hl => ?_⟩
                · have hl' : P.onLetter u := hl
                  show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔
                    P.leftFirst u
                  rw [if_pos hl']; exact decide_eq_true_iff
                · have hl' : ¬ P.onLetter u := hl
                  show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
                  rw [if_neg hl']
              have hidleU : u.chain = ChainVM.idle := by rw [hudef, afterCompare_chain]
              have hgetU : searchLens.get u = vq := rfl
              have hsrU : ReadyPacedS (searchLens.get u) n 0 := by
                rw [hgetU]
                exact readyPacedS_effect_true P (by omega) hidle hsr hq
              have hMU : MInv raw {c with clock := 2048, output := o, replaying := false} u :=
                minv_match o 2048 hrp' rfl rfl hav hmatch hi hM
              have hiU : ScanInvariant raw (position u.center) (r+1) u.left u.right := by
                have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi
                rw [hudef, afterCompare_center]
                exact h0
              obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
                ih {c with clock := 2048, output := o, replaying := false} u (r+1) 0
                  hm (by norm_num) (by norm_num) hidleU hsrU hMU hiU
              refine ⟨true :: es, c', t, r',
                .matchIdle c s vs vq o hm hrp' hav hc1 hidle rfl rfl rfl hmt hq hf ho hseg,
                hm', hclk', hidle', hsrt, hMt, hit, ?_⟩
              rcases hlen with h0 | h0
              · exact Or.inl (by simp [h0])
              · exact Or.inr h0
          · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi,
              Or.inr (.mismatch hrp' hc1 hav hmatch)⟩
    · exact ⟨[], c, s, r, .stop _ _, hm, hclk, hidle, hrdy, hM, hi, Or.inr (.ended hav)⟩

#print axioms watchSegE_constructS

/-- **`GalilSegmentConstructB.segment_of_invLPCB` on `ReadyPacedS`.**  The entry
premise is now `InvLPC` plus `SearchReadyS` at *every* long-enough, clock-paced
event list — no match budget, no upper bound on the list.  Since every list the
scan loop can emit is clock-paced, this is the closure the machine actually
offers. -/
theorem segment_of_invLPCS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (c : Control) (r : GalilVM) (hIC : InvLPC raw c r)
    (hready : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (2048 - c.clock)) :
    ∃ (c' : Control) (t : GalilVM),
      SegReachedW centre place entry q first raw c r c' t ∧
      SegEnd (PofC centre place entry raw) c' t := by
  have hIP : InvLP raw c r := hIC.1.1
  have hI : InvS raw c r := hIP.1.1
  obtain ⟨hm, hclk, hidle, hM, R, hi, hfr, hrr, hsi⟩ :
      c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.minv, Rad,
        hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
    · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.minv, k,
        h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩
  obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
    watchSegE_constructS raw (PofC centre place entry raw) hex q first
      hsearch (headRank r.right * 2048 + c.clock) c r R (2048 - c.clock) hm hclk
      (by omega) hidle hready hM hi
  have hEnd : SegEnd (PofC centre place entry raw) c' t := by
    rcases hlen with h0 | h0
    · exact .ended (exhausted_of_long (PofC centre place entry raw) q first 2048 (by norm_num)
        hseg hclk (le_of_eq h0.symm))
    · exact h0
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw (PofC centre place entry raw) rfl rfl q first 2048 hseg
      (position r.center) R hi hIP.1.2
  have hrun : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c', t⟩ :=
    ⟨k1, stepsAll_mono (fun _ h0 _ _ => h0) h1⟩
  have hsteps : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es.length
      ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hseg
  have hfrt : Frontier t ∧ ReplayRest c' t :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place
      entry q first 2048 hsteps hm (hlive_of_invLPC centre place entry q first hIC) hfr hrr
  have hsit : ShiftIdle t := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hseg]
    exact (shiftIdle_iff r).1 hsi
  exact ⟨c', t,
    ⟨{ run := hrun
       center := watchSegE_center _ q first 2048 hseg
       mode := hm'
       clock := hclk'
       idle := hidle'
       minv := hMt
       search := hsrt
       input := hit.rightRep
       frontier := hfrt.1
       shiftIdle := hsit
       scan := ⟨r', hit⟩ }, es, hseg⟩, hEnd⟩

/-! ## 6. The report comparison and the crossing case, on `ReadyPacedS` -/

/-- **`CloseoutReportCase.readyFuel_watchSegE` on `ReadyPacedS`.**  The clock
slack at the far end is whatever the segment's last tick left; the invariant
`2048 ≤ clock + slack` is transported with it. -/
theorem readyPacedS_watchSegE (P : Shared) (q : ℕ) (first : Fin 9)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t) (ht : t.chain = ChainVM.idle) :
    ∀ n k : ℕ, 2048 ≤ c.clock + k →
      ReadyPacedS (searchLens.get s) (n + es.length) k →
      ∃ k', 2048 ≤ c'.clock + k' ∧ ReadyPacedS (searchLens.get t) n k' := by
  induction h with
  | stop c s => intro n k hk h0; exact ⟨k, hk, by simpa using h0⟩
  | wait c s s' hm hr hn hb rest ih =>
      intro n k hk h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hs' : s'.chain = ChainVM.idle := watchSegE_idle_start P q first 2048 rest ht
      have hs : s.chain = ChainVM.idle := by
        by_contra hne
        exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
      exact ih ht n (k + 1) (by omega)
        (readyPacedS_effect_false P (le_refl _) hs
          (readyPacedS_mono (by simp; omega) (le_refl _) h0) hse)
  | count c s s' hm hr ha hc hb rest ih =>
      intro n k hk h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      have hs' : s'.chain = ChainVM.idle := watchSegE_idle_start P q first 2048 rest ht
      have hs : s.chain = ChainVM.idle := by
        by_contra hne
        exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
      exact ih ht n (k + 1) (by simp; omega)
        (readyPacedS_effect_false P (le_refl _) hs
          (readyPacedS_mono (by simp; omega) (le_refl _) h0) hse)
  | countR c s s' hm hr hc hidle hb rest ih =>
      intro n k hk h0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hse⟩ := backgroundS_fields P q first hb
      exact ih ht n (k + 1) (by simp; omega)
        (readyPacedS_effect_false P (le_refl _) hidle
          (readyPacedS_mono (by simp; omega) (le_refl _) h0) hse)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      intro n k hk h0
      have hs' : (afterCompare s vs vq).chain = ChainVM.idle :=
        watchSegE_idle_start P q first 2048 rest ht
      have hmatch : read (left s.left) = read (right s.right) := by
        obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
        rw [scanLens.get_set] at hl0 hr0
        have hmp := matched_parts P q first hmt
        rw [hl0, hr0] at hmp; exact hmp
      obtain ⟨-, -, htk⟩ := compare_parts P q first hcmp hmatch
      have hs : s.chain = ChainVM.idle := by
        by_contra hne0
        rw [afterCompare_chain] at hs'
        exact chainTick_ne_idle htk hne0 hs'
      exact absurd hs hne
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro n k hk h0
      exact ih ht n 0 (by simp)
        (readyPacedS_effect_true P (by omega) hidle
          (readyPacedS_mono (by simp; omega) (le_refl _) h0) hq)
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro n k hk h0
      exact ih ht n 0 (by simp)
        (readyPacedS_effect_true P (by omega) hidle
          (readyPacedS_mono (by simp; omega) (le_refl _) h0) hq)

#print axioms segment_of_invLPCS
#print axioms readyPacedS_watchSegE

theorem reachAtC3_of_target_matchS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (n k : ℕ) (hk : 2048 ≤ k + 1) (hready : ReadyPacedS (searchLens.get t) (n + 1) k)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  -- the entering counters, transported along the idle segment
  obtain ⟨RadE, hiE, hRRE, hSE, hLE⟩ := hIC.1.1.2
  have hiT : ScanInvariant raw (position r.center) (RadE + es.count true) t.left t.right :=
    scanInvariant_watchSegE P q first 2048 hw hiE
  have hRRT : RadiusRep t.radius (RadE + es.count true) :=
    radiusRep_watchSegE P q first 2048 hw hRRE
  have hST : SpanRep t := spanRep_watchSegE P q first 2048 hw hSE
  have hLT : Canonical t.length := canonical_length_watchSegE P q first 2048 hw hLE
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterCompare t vs vq) := hmt
  set u : GalilVM := afterCompare t vs vq with hu
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c'.output with ho'
  have ho : refresh (galilFrameS P q first) u c'.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = c'.output
      rw [if_neg hl']
  have hsrc : SoundScanNR raw ⟨c', t⟩ := stepsAll_last hrun0
  obtain ⟨⟨k1, hrun1⟩, hrp, hfr⟩ :=
    PalPeg.GalilReportPrefix.reportAt_of_match raw P rfl rfl q first 2048 hsrc hs.mode hc1 hnr
      hav hs.minv hi hpos hm1 hmle vs vq o rfl rfl hcmp hmt1 ho
  have hsound := stepsAll_last hrun1
  have hpl : (galilFrameS P q first).matchedPlace c'.replaying u u := by
    show u = (if c'.replaying then _ else u)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) 2048 ⟨c', t⟩
      ⟨{c' with clock := 2048, output := o, replaying := false}, u⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := 2048) c' t u u o hs.mode
      (Or.inr hav) hc1 hcmp hmt1 hpl ho
    rw [hnr] at h
    simpa using h
  have hall := stepsAll_trans hrun0 (.succ hsrc htick (.zero _ hsound))
  obtain ⟨L, w, hw', hcr, -, -⟩ :=
    GalilCostedFallback.costedRun_target_match raw P q first hw hi0 hc0 hc1 hav m hm1 hpos vq
  -- the counters and the centre head at the landing of the comparison
  have hcu : u.center = r.center := by rw [hu, afterCompare_center, hs.center]
  have hEu : EntryCounters raw u := by
    refine ⟨RadE + es.count true + 1, ?_, ?_, ?_, ?_⟩
    · rw [hcu]; exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hiT
    · rw [hu, afterCompare_radius]; exact radius_rep_inc hRRT
    · rw [hu]; exact spanRep_afterCompare hST
    · rw [hu, afterCompare_length]; exact inc_canonical _ (inc_canonical _ hLT)
  -- the stage data: the report comparison is a `matchIdle` step of the segment
  have hmid : WatchSegE P q first 2048 [true] c' t
      {c' with clock := 2048, output := o, replaying := false} u :=
    .matchIdle c' t vs vq o hs.mode hnr hav hc1 hs.idle rfl rfl rfl hmt0 hq hnf ho (.stop _ _)
  have hstage : ReplayStage raw P q first
      {c' with clock := 2048, output := o, replaying := false} u :=
    replayStage_trans (replayStage_trans hIN.2 hw) hmid
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact readyPacedS_ready (readyPacedS_effect_true P hk hs.idle hready hq)
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    have hIL : InvLP raw {c' with clock := 2048, output := o, replaying := false} u :=
      ⟨invL_of_run hall (Or.inr ⟨R + 1, hIS⟩), hEu⟩
    exact ⟨⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
      centreRep_congr hcu hIC.2⟩, hstage⟩
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega

#print axioms reachAtC3_of_target_matchS

theorem reachAtC3_of_crossS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hready : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (2048 - c.clock))
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hmC, hclkC, hidleC, hsrC, hMC, R0, hi0, hfrC, hrrC, hsiC⟩ := invS_entry_data hI.1
  have hnrC : c.replaying = false := (invS_mode hI.1).2
  have hposT : position t.right = position r.right + es.count true :=
    (watchSegE_right_position raw (PofC centre place entry raw) q first 2048 hw hi0).2
  obtain ⟨es1, es2, hsplit, hcnt1⟩ :=
    split_nth_true es (2 * m - 2 - position r.right) (by omega)
  obtain ⟨c1, s1, hw1, hw2⟩ :=
    watchSegE_append (PofC centre place entry raw) q first 2048 es1 (by rw [← hsplit]; exact hw)
  have hi1 : ScanInvariant raw (position r.center) (R0 + es1.count true) s1.left s1.right :=
    scanInvariant_watchSegE (PofC centre place entry raw) q first 2048 hw1 hi0
  have hpos1 : position s1.right = position r.right + es1.count true :=
    (watchSegE_right_position raw (PofC centre place entry raw) q first 2048 hw1 hi0).2
  have hpos1' : position s1.right = 2 * m - 2 := by rw [hpos1, hcnt1]; omega
  have hcen1 : s1.center = r.center :=
    watchSegE_center (PofC centre place entry raw) q first 2048 hw1
  have hnr1 : c1.replaying = false :=
    watchSegE_notReplaying (PofC centre place entry raw) q first 2048 hw1 hnrC
  have hidle1 : s1.chain = ChainVM.idle :=
    watchSegE_idle_start (PofC centre place entry raw) q first 2048 hw2 hs.idle
  have hmode1 : c1.mode = Mode.scan := by
    obtain ⟨av, -, -, -, hmo⟩ := watchSegE_clock (PofC centre place entry raw) q first 2048 hw1
    rw [hmo, hmC]
  have hrank1 : headRank s1.right + es1.count true = headRank r.right :=
    rank_count (PofC centre place entry raw) q first 2048 hw1
  have hM1 : MInv raw c1 s1 :=
    minv_watchSegE raw (PofC centre place entry raw) (fun s => hex_C centre place entry raw s)
      q first 2048 hw1 R0 hi0 hMC
  have hsteps1 : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es1.length
      ⟨c, r⟩ ⟨c1, s1⟩ := watchSegE_steps_length _ q first 2048 hw1
  have hfr1 : Frontier s1 ∧ ReplayRest c1 s1 :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place entry q first 2048
      hsteps1 hmC (hlive_of_invLPC centre place entry q first hIC) hfrC hrrC
  have hsi1 : ShiftIdle s1 := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hw1]
    exact (shiftIdle_iff r).1 hsiC
  have hrep1 : s1.replay = reset := hfr1.2 (Or.inl hnr1)
  have hrun1 : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c1, s1⟩ :=
    ⟨es1.length, seg_run centre place entry q first raw hI hw1⟩
  cases hw2 with
  | «match» _ _ vs vq o _ _ _ _ hne2 _ _ _ _ _ => exact absurd hidle1 hne2
  | matchIdleR _ _ vs vq o _ hr2 _ _ _ _ _ _ _ _ _ _ _ => rw [hnr1] at hr2; exact absurd hr2 (by simp)
  | matchIdle _ _ vs vq o hm2 hr2 ha2 hc2 hidle2 hl2 hrr2 hvs2 hmt2 hq2 hnf2 ho2 rest =>
      have hmtread : read (left s1.left) = read (right s1.right) := by
        have h0 := matched_parts (PofC centre place entry raw) q first hmt2
        rw [hl2, hrr2] at h0; exact h0
      -- the crossing state can still move right: both halves of the budget
      have hrk : 1 ≤ headRank s1.right := by
        have := rank_right s1.right ha2; omega
      have hlen1 : es1.length + 1 ≤ headRank r.right * 2048 + c.clock := by
        by_contra hcon
        exact (exhausted_of_long (PofC centre place entry raw) q first 2048 (by norm_num)
          hw1 hclkC (by omega)) ha2
      obtain ⟨k1, hk1, hfuel1⟩ :=
        readyPacedS_watchSegE (PofC centre place entry raw) q first hw1 hidle1
          ((headRank r.right * 2048 + c.clock - es1.length - 1) + 1) (2048 - c.clock)
          (by omega) (readyPacedS_mono (by omega) (le_refl _) hready)
      have hsr1 : SearchReady (searchLens.get s1) := readyPacedS_ready hfuel1
      have hsW1 : SegReachedW centre place entry q first raw c r c1 s1 :=
        ⟨{ run := hrun1
           center := hcen1
           mode := hmode1
           clock := by omega
           idle := hidle1
           minv := hM1
           search := hsr1
           input := hi1.rightRep
           frontier := hfr1.1
           shiftIdle := hsi1
           scan := ⟨R0 + es1.count true, by rw [hcen1]; exact hi1⟩ }, es1, hw1⟩
      exact reachAtC3_of_target_matchS centre place entry q first raw m hm1 hmle
        c r c1 s1 hIN _ k1 (by omega) hfuel1 hsW1 ⟨hnr1, hc2, ha2, hpos1', hrep1⟩ hmtread vq hq2 hnf2

#print axioms reachAtC3_of_crossS

/-! ## 7. The named residual, with the budget half removed -/

/-- **`RunEntryS` from the hand-over alone.**  All that is left of the
`.run`-entry datum is the *preparation-phase* fact: when the preparation hands
control over, the DP machine is the preload of the calibrated window `w` of a
stage with lower bound `k`, and the entry debt is the stage debt.  No
event-budget side condition survives — `dpSafeStage_entry_paced` pays for every
clock-paced stream of every length. -/
theorem runEntryS_of_entryPaced (center : GalilScaffoldPlace.Place) (a : Bool)
    (v v' : SearchVM) (as : List Bool) (w : List (Fin 3)) (lower Rad k slack : ℕ)
    (hw : w.length = stageWindow k)
    (hhand : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      v'.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩ ∧ Canonical v'.search.debt ∧
        PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (hlen : dpEvents (stageWindow k) ≤ as.length) (hpaced : PacedL 2048 slack as) :
    RunEntryS center a v v' as := by
  intro hs hne hr
  obtain ⟨h1, h2, h3⟩ := hhand hs hne hr
  exact dpSafeStage_entry_paced v' w lower Rad k slack as hw h1 hr h2 hstage h3 hslack hlen hpaced

#print axioms runEntryS_of_entryPaced

end PalPeg.CloseoutReadyStage
