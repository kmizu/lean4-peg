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

and this file discharges it from a `PrepAt k m` origin with `StageInvS k m`,
the reach along the preparation leg, and the comparison count that leg has spent.

`CloseoutPreload35.dpSafe_of_stagePrepD_slack` takes the whole `StagePrepS`
datum, whose length and pacing clauses mention the *future* event list.  None of
that is needed: the only thing read from it is the comparison count of the
consumed prefix, so the hypothesis here is that count alone.  That keeps the
predicate free of any quantification over continuations.

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
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload (run_entry_preload)
open PalPeg.CloseoutPreload5 (ReachP reachP_ne_run)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload9 (dpEvents_mono)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload12 (entry_preload_at_prep entry_debt_at_prep)
open PalPeg.CloseoutPreload35 (dpDemandS StageInvS)
open PalPeg.DpBudgetState (DpBudgetAt dpBudgetAt_entry)

/-- **The entry is funded.**  `CloseoutPreload35.dpSafe_of_stagePrepD_slack` takes
the whole `StagePrepS` datum, which mentions the *future* event list; this needs
none of it.  What is actually read there is the reach `ReachP v bs x` and the
comparison count of the consumed prefix `bs ++ [a]`, so those are the
hypotheses here — no `DepthAt`, no slack, no continuation. -/
theorem dpBudgetAt_of_prepEntry {k m : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    {bs : List Bool} {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hreach : ReachP v bs x)
    (hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k + 2047)
    (hs : searchStep c a x x') (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0 := by
  obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
  obtain ⟨hcan, hdv⟩ := entry_debt_at_prep hp hreach hs hrun
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
  exact dpBudgetAt_entry (run_entry_preload hs (reachP_ne_run hreach) hrun hpreload)
    hrun hcan hpos hfunded

#print axioms dpBudgetAt_of_prepEntry

end PalPeg.StageEntryBudget
