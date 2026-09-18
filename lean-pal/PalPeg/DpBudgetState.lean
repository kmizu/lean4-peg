import PalPeg.DpBudgetBalance
import PalPeg.CloseoutReadyStage

/-!
# The readiness budget on the search state

`DpBudgetBalance` shows that `spent + ⌈(need + k)/2048⌉ ≤ debt` is exactly
balanced against the two transport steps of `CloseoutReadyStage.ReadyIface`.
This file puts that accounting on a `SearchVM`:

* `DpBudgetAt v k` — the DP of `v` was started at a `.run` state `s0` with
  preload `w`, has been given the events `bs`, and the budget holds with
  `need = dpEvents w.length - bs.length`, `spent = bs.count true` and
  `debt = value s0.debt`.
* `dpSafeHere_of_dpBudgetAt` — the `ready` direction.  `DpSafeHere` existentially
  quantifies its continuation, so taking it all-background reduces it to
  `spent ≤ debt`, which `dpBudget_spent` gives.
* `dpBudgetAt_need_pos` — while the DP is in `.run` it has not been given its
  whole budget yet.  This is `CloseoutReadyStage.dpSafeStage_pre_ne_nil` read at
  the empty charged prefix.
* `dpBudgetAt_background` / `dpBudgetAt_comparison` — one quantum, the two
  cases, discharged by the arithmetic of `DpBudgetBalance`.

**Not done here.**  `DpBudgetAt` covers the `.run` phase only.  A `Φ` for
`ReadyIface` also has to hold in the preparation, `.wait` and `.double` phases
(`StageDoubleLeg` is the `.double` one) and to re-establish `DpBudgetAt` at each
`.run` entry, which is where the stage debt and `bal_of_paced_slack_S` come in.
So no hypothesis is removed yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.DpBudgetState

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldCounter (Canonical value)
open PalPeg.GalilScaffoldSearchRun (SafeQuanta)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.GalilBranchInvariants2 (DpReached DpSafeHere dpReached_step PrepInv
  prepInv_prepare prepInv_tick)
open PalPeg.GalilSearchReadyInv (prepInv_of_notPrep prepInv_afterAdvance advance_mode
  waitStep_mode doubleStep_mode growStep_mode)
open PalPeg.CloseoutPreload13 (run_step_quanta)
open PalPeg.CloseoutReadyStage (dpSafeStage_pre_ne_nil)
open PalPeg.DpBudgetBalance (DpBudget dpBudget_spent dpBudget_mono dpBudget_background
  dpBudget_comparison)

/-- `dpEvents n` events are enough to meet the DP's `3186 n + 1683` cell budget. -/
theorem dpEvents_covers (n : ℕ) : 3186 * n + 1683 ≤ 64 * dpEvents n := by
  unfold dpEvents; omega

/-- **The DP budget at a search state.** -/
def DpBudgetAt (v : SearchVM) (k : ℕ) : Prop :=
  ∃ (w : List (Fin 3)) (lower : ℕ) (s0 : GalilScaffoldSearchFinish.State) (bs : List Bool),
    s0.mode = .run ∧ Canonical s0.debt ∧ 0 ≤ value s0.debt ∧
      DpReached w lower s0 bs v.search v.dp ∧
      DpBudget (dpEvents w.length - bs.length) (bs.count true) (value s0.debt).toNat k

/-- **The `ready` direction.**  `DpSafeHere` quantifies its continuation
existentially, so an all-background continuation long enough for the DP turns it
into `spent ≤ debt`. -/
theorem dpSafeHere_of_dpBudgetAt {v : SearchVM} {k : ℕ} (h : DpBudgetAt v k) :
    DpSafeHere v.search v.dp := by
  obtain ⟨w, lower, s0, bs, hs0, hc, hd0, hreach, hbud⟩ := h
  have hcast : (((value s0.debt).toNat : ℕ) : ℤ) = value s0.debt := Int.toNat_of_nonneg hd0
  have hspent : bs.count true ≤ (value s0.debt).toNat := dpBudget_spent hbud
  refine ⟨w, lower, s0, bs, List.replicate (dpEvents w.length) false, ?_, hs0, hc, ?_, hreach⟩
  · have := dpEvents_covers w.length
    simp only [List.length_append, List.length_replicate]
    omega
  · have hcnt : (bs ++ List.replicate (dpEvents w.length) false).count true = bs.count true := by
      simp [List.count_append, List.count_replicate]
    rw [hcnt]
    omega

/-- **The DP has budget left while it runs.**  If the events already given met
the cell budget, `safeQuanta_exists_of_reached` would place the halt at the
current configuration, contradicting `.run`.  This is
`dpSafeStage_pre_ne_nil` at the empty charged prefix. -/
theorem dpBudgetAt_need_pos {v : SearchVM} {w : List (Fin 3)} {lower : ℕ}
    {s0 : GalilScaffoldSearchFinish.State} {bs : List Bool}
    (hm : v.search.mode = .run) (hs0 : s0.mode = .run) (hc : Canonical s0.debt)
    (hd0 : 0 ≤ value s0.debt) (hreach : DpReached w lower s0 bs v.search v.dp)
    (hspent : bs.count true ≤ (value s0.debt).toNat) :
    bs.length < dpEvents w.length := by
  by_contra hcon
  have hcast : (((value s0.debt).toNat : ℕ) : ℤ) = value s0.debt := Int.toNat_of_nonneg hd0
  have hbud : 3186 * w.length + 1683 ≤ 64 * (bs ++ ([] : List Bool)).length := by
    have := dpEvents_covers w.length
    simp only [List.append_nil]
    omega
  have hb : (((bs ++ ([] : List Bool)).count true : ℤ)) ≤ value s0.debt := by
    simp only [List.append_nil]
    omega
  exact dpSafeStage_pre_ne_nil (as := ([] : List Bool)) hm rfl hbud hs0 hc hb hreach rfl

/-- **The `background` step.**  The event meets one unit of the DP's need and
buys one unit of slack; the debt is untouched. -/
theorem dpBudgetAt_background {v v' : SearchVM} {k k' : ℕ} (hm : v.search.mode = .run)
    (hk : k' ≤ k + 1) (h : DpBudgetAt v k)
    (hq : SafeQuanta v.search v.dp [false] v'.search v'.dp) :
    DpBudgetAt v' k' := by
  obtain ⟨w, lower, s0, bs, hs0, hc, hd0, hreach, hbud⟩ := h
  have hneed := dpBudgetAt_need_pos hm hs0 hc hd0 hreach (dpBudget_spent hbud)
  refine ⟨w, lower, s0, bs ++ [false], hs0, hc, hd0, dpReached_step hreach hq, ?_⟩
  have hlen : (bs ++ [false]).length = bs.length + 1 := by simp
  have hcnt : (bs ++ [false]).count true = bs.count true := by simp [List.count_append]
  have harg : dpEvents w.length - (bs.length + 1) = dpEvents w.length - bs.length - 1 := by omega
  rw [hlen, hcnt, harg]
  exact dpBudget_background (by omega) hk hbud

/-- **The `comparison` step.**  The guard `2048 ≤ k + 1` is what pays for the
unit of debt this event spends. -/
theorem dpBudgetAt_comparison {v v' : SearchVM} {k : ℕ} (hm : v.search.mode = .run)
    (hk : 2048 ≤ k + 1) (h : DpBudgetAt v k)
    (hq : SafeQuanta v.search v.dp [true] v'.search v'.dp) :
    DpBudgetAt v' 0 := by
  obtain ⟨w, lower, s0, bs, hs0, hc, hd0, hreach, hbud⟩ := h
  have hneed := dpBudgetAt_need_pos hm hs0 hc hd0 hreach (dpBudget_spent hbud)
  refine ⟨w, lower, s0, bs ++ [true], hs0, hc, hd0, dpReached_step hreach hq, ?_⟩
  have hlen : (bs ++ [true]).length = bs.length + 1 := by simp
  have hcnt : (bs ++ [true]).count true = bs.count true + 1 := by simp [List.count_append]
  have harg : dpEvents w.length - (bs.length + 1) = dpEvents w.length - bs.length - 1 := by omega
  rw [hlen, hcnt, harg]
  exact dpBudget_comparison (by omega) hk hbud

/-- **The `mono` direction.**  A smaller slack is a weaker claim. -/
theorem dpBudgetAt_mono {v : SearchVM} {k k' : ℕ} (hk : k' ≤ k) (h : DpBudgetAt v k) :
    DpBudgetAt v k' := by
  obtain ⟨w, lower, s0, bs, hs0, hc, hd0, hreach, hbud⟩ := h
  exact ⟨w, lower, s0, bs, hs0, hc, hd0, hreach, dpBudget_mono hk hbud⟩

/-! ## 2. The `.run` entry, and the combined readiness predicate -/

/-- **The budget at a fresh `.run` entry.**  `CloseoutRunEntriesS.run_entry_preload`
identifies the handed-over DP machine with the calibrated preload, and
`dpReached_start` is the empty-prefix reach; what is left is exactly the stage
condition: the debt has to cover one comparison per `2048` of the DP's event
need. -/
theorem dpBudgetAt_entry {v : SearchVM} {w : List (Fin 3)} {lower : ℕ}
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.run)
    (hc : Canonical v.search.debt) (hd0 : 0 ≤ value v.search.debt)
    (hfunded : (dpEvents w.length + 2047) / 2048 ≤ (value v.search.debt).toNat) :
    DpBudgetAt v 0 := by
  refine ⟨w, lower, v.search, [], hm, hc, hd0, ?_, ?_⟩
  · show DpReached w lower v.search [] v.search v.dp
    rw [hdp]; exact PalPeg.GalilBranchInvariants2.dpReached_start w lower v.search
  · show DpBudget (dpEvents w.length - [].length) ([].count true) _ 0
    unfold DpBudget
    simpa using hfunded

/-- **Readiness on the whole cycle.**  Outside `.run` the DP clause of
`GalilBranchInvariants2.SearchReady` is vacuous, so only the preparation
invariant is asked for; inside `.run` the budget of §1 is asked for as well. -/
def ReadyAt (v : SearchVM) (k : ℕ) : Prop :=
  PrepInv v.toPrep ∧
    (v.search.mode = GalilScaffoldSearchFinish.Mode.run → DpBudgetAt v k)

/-- **The `ready` field of `CloseoutReadyStage.ReadyIface`, for `ReadyAt`.** -/
theorem searchReady_of_readyAt {v : SearchVM} {k : ℕ} (h : ReadyAt v k) :
    PalPeg.GalilBranchInvariants2.SearchReady v :=
  ⟨h.1, fun hm => dpSafeHere_of_dpBudgetAt (h.2 hm)⟩

/-- **The `mono` field of `CloseoutReadyStage.ReadyIface`, for `ReadyAt`.** -/
theorem readyAt_mono {v : SearchVM} {k k' : ℕ} (hk : k' ≤ k) (h : ReadyAt v k) :
    ReadyAt v k' :=
  ⟨h.1, fun hm => dpBudgetAt_mono hk (h.2 hm)⟩

#print axioms dpBudgetAt_entry
#print axioms searchReady_of_readyAt
#print axioms readyAt_mono

#print axioms dpEvents_covers
#print axioms dpSafeHere_of_dpBudgetAt
#print axioms dpBudgetAt_need_pos
#print axioms dpBudgetAt_background
#print axioms dpBudgetAt_comparison
#print axioms dpBudgetAt_mono

/-! ## 3. Transport along one search quantum -/

/-- **`PrepInv` survives one search quantum.**  This is the first component of
`CloseoutReadyStage.readyRemS_step` on its own: every branch of `searchStep`
either lands outside the four preparation modes (`prepInv_of_notPrep`), runs a
preparation tick (`prepInv_tick`) or dispatches `prepare` (`prepInv_prepare`). -/
theorem prepInv_searchStep {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hprep : PrepInv v.toPrep) (hstep : searchStep center a v v') : PrepInv v'.toPrep := by
  classical
  unfold searchStep at hstep
  cases hm : v.search.mode with
  | idle => rw [hm] at hstep; subst hstep; exact hprep
  | found => rw [hm] at hstep; subst hstep; exact hprep
  | missed => rw [hm] at hstep; subst hstep; exact hprep
  | grow =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      rw [hstep]
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a
        (GalilScaffoldStagePrepare.growStep v.toPrep))
      exact prepInv_afterAdvance a
        (prepInv_of_notPrep (Or.inr (Or.inl (by rw [growStep_mode]; exact hm))))
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      rw [hstep]
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
      exact prepInv_afterAdvance a (prepInv_prepare _ _ _)
  | lower =>
    rw [hm] at hstep; obtain ⟨y, hy, hv'⟩ := hstep
    rw [hv']; show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
    exact prepInv_afterAdvance a (prepInv_tick hy hprep)
  | lowerHome =>
    rw [hm] at hstep; obtain ⟨y, hy, hv'⟩ := hstep
    rw [hv']; show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
    exact prepInv_afterAdvance a (prepInv_tick hy hprep)
  | copy =>
    rw [hm] at hstep; obtain ⟨y, hy, hv'⟩ := hstep
    rw [hv']; show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
    exact prepInv_afterAdvance a (prepInv_tick hy hprep)
  | home =>
    rw [hm] at hstep; obtain ⟨y, hy, hv'⟩ := hstep
    rw [hv']; show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
    exact prepInv_afterAdvance a (prepInv_tick hy hprep)
  | run =>
    rw [hm] at hstep
    obtain ⟨hq, -, -⟩ := hstep
    by_cases hrun : v'.search.mode = GalilScaffoldSearchFinish.Mode.run
    · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inl hrun)))
    · rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm hrun with hf | hmi | hw | hd
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inl hf))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmi)))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw))))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))))
  | wait =>
    rw [hm] at hstep
    have hmode : v'.search.mode = GalilScaffoldSearchFinish.Mode.double ∨
        v'.search.mode = GalilScaffoldSearchFinish.Mode.wait := by
      rw [hstep]
      show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _ ∨
        (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _
      rw [advance_mode]
      rcases waitStep_mode v.search with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hm)
    rcases hmode with h1 | h1
    · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
    · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
  | double =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      have hmode : v'.search.mode = GalilScaffoldSearchFinish.Mode.double := by
        rw [hstep]
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        rw [advance_mode, doubleStep_mode]
        exact hm
      exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmode))))))
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      rw [hstep]
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
      exact prepInv_afterAdvance a (prepInv_prepare _ _ _)

/-- **The `background` field, modulo the entry.**  A background tick inside the
`.run` phase is `dpBudgetAt_background`; a tick that *enters* `.run` is the one
place where the stage debt has to be re-funded, and that is the named
hypothesis. -/
theorem readyAt_background {center : GalilScaffoldPlace.Place} {v v' : SearchVM} {k k' : ℕ}
    (hk : k' ≤ k + 1) (h : ReadyAt v k) (hstep : searchStep center false v v')
    (hentry : v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run →
      v'.search.mode = GalilScaffoldSearchFinish.Mode.run → DpBudgetAt v' k') :
    ReadyAt v' k' := by
  refine ⟨prepInv_searchStep h.1 hstep, fun hrun' => ?_⟩
  by_cases hrun : v.search.mode = GalilScaffoldSearchFinish.Mode.run
  · exact dpBudgetAt_background hrun hk (h.2 hrun) (run_step_quanta hrun hstep).1
  · exact hentry hrun hrun'

/-- **The `comparison` field, modulo the entry.**  The guard `2048 ≤ k + 1` is
what `dpBudgetAt_comparison` spends on the unit of debt. -/
theorem readyAt_comparison {center : GalilScaffoldPlace.Place} {v v' : SearchVM} {k : ℕ}
    (hk : 2048 ≤ k + 1) (h : ReadyAt v k) (hstep : searchStep center true v v')
    (hentry : v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run →
      v'.search.mode = GalilScaffoldSearchFinish.Mode.run → DpBudgetAt v' 0) :
    ReadyAt v' 0 := by
  refine ⟨prepInv_searchStep h.1 hstep, fun hrun' => ?_⟩
  by_cases hrun : v.search.mode = GalilScaffoldSearchFinish.Mode.run
  · exact dpBudgetAt_comparison hrun hk (h.2 hrun) (run_step_quanta hrun hstep).1
  · exact hentry hrun hrun'

#print axioms prepInv_searchStep
#print axioms readyAt_background
#print axioms readyAt_comparison

end PalPeg.DpBudgetState
