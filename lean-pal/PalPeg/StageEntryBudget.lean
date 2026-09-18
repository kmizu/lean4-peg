import PalPeg.DpBudgetState

/-!
# The stage entry funds the DP

`DpBudgetState.readyAt_background` / `readyAt_comparison` leave exactly one
residue: at a step that *enters* `.run` the DP is started fresh, and its budget
has to be funded from the stage debt.  `DpBudgetState.dpBudgetAt_entry` reduces
that to one inequality,

```
(dpEvents w.length + 2047) / 2048 ≤ (value v'.search.debt).toNat
```

and this file discharges it from the stage data that
`CloseoutPreload35.dpSafe_of_stagePrepD_slack` already uses: a `PrepAt k m`
origin with `StageInvS k m`, the preparation depth `D ≤ prepLen k`, and the
preparation leg paced at a slack of at most `2047`.

The margin is wide.  `StageInvS` gives the debt
`dpDemandS k m = (prepLen k + 2047)/2048 + (prepLen k + 2047 + dpEvents (m+1))/2048 + 1`,
the preparation leg can spend at most the first of those three terms, and the
DP's own need `⌈dpEvents (m+1) / 2048⌉` is below the second — so the `+ 1` is
never even touched.

**Not done here.**  This funds *one* entry from a `PrepAt` origin.  Assembling
the four phases into a single `Φ` and proving `CloseoutReadyStage.ReadyIface P Φ`
still needs the origin to be re-established at each stage boundary
(`CloseoutPreload10.prepAt_of_double_exit`, `StageDoubleLeg`), so no hypothesis
is removed yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageEntryBudget

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload (run_entry_preload)
open PalPeg.CloseoutPreload5 (ReachP reachP_ne_run append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload9 (dpEvents_mono)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload12 (entry_preload_at_prep entry_debt_at_prep)
open PalPeg.CloseoutPreload35 (dpDemandS StageInvS StagePrepS pacedL_prefix_count_slack)
open PalPeg.DpBudgetState (DpBudgetAt dpBudgetAt_entry)

/-- **The entry is funded.**  Same inputs as
`CloseoutPreload35.dpSafe_of_stagePrepD_slack`, conclusion in the state-local
form `DpBudgetState.DpBudgetAt` instead of the list-charged `DpSafeStage`. -/
theorem dpBudgetAt_of_stagePrepS {k m D slack : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hslack : slack ≤ 2047)
    {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrepS k m D slack v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0 := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  have hne := reachP_ne_run hreach
  have hdlen := hdep bs x x' c a hreach hs hrun
  obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
  obtain ⟨hcan, hdv⟩ := entry_debt_at_prep hp hreach hs hrun
  have hpaced' : PacedL 2048 slack ((bs ++ [a]) ++ as) := by
    rw [← append_cons_eq]; exact hpaced
  have hlenpref : (bs ++ [a]).length ≤ D := by
    simp only [List.length_append, List.length_singleton]; omega
  -- the comparisons the preparation leg can have spent
  have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k + 2047 :=
    le_trans (pacedL_prefix_count_slack hpaced') (by omega)
  -- the DP's own need is below the second term of `dpDemandS`
  have hmono : dpEvents W.length ≤ dpEvents (m + 1) := dpEvents_mono hW
  have hbelow : (dpEvents W.length + 2047) / 2048
      ≤ (prepLen k + 2047 + dpEvents (m + 1)) / 2048 :=
    Nat.div_le_div_right (by omega)
  have hcount : (bs ++ [a]).count true ≤ (prepLen k + 2047) / 2048 := by omega
  unfold StageInvS dpDemandS at hE
  have hfunded : (dpEvents W.length + 2047) / 2048 ≤ (value x'.search.debt).toNat := by
    rw [hdv]; omega
  have hpos : 0 ≤ value x'.search.debt := by rw [hdv]; omega
  exact dpBudgetAt_entry (run_entry_preload hs hne hrun hpreload) hrun hcan hpos hfunded

#print axioms dpBudgetAt_of_stagePrepS

end PalPeg.StageEntryBudget
