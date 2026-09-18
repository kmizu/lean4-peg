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
open PalPeg.GalilBranchInvariants2 (DpReached DpSafeHere dpReached_step)
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

#print axioms dpEvents_covers
#print axioms dpSafeHere_of_dpBudgetAt
#print axioms dpBudgetAt_need_pos
#print axioms dpBudgetAt_background
#print axioms dpBudgetAt_comparison
#print axioms dpBudgetAt_mono

end PalPeg.DpBudgetState
