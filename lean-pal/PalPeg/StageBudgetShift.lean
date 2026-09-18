import PalPeg.CloseoutPreload7

/-!
# `StageBudgetShift`: the stage budget at the *true* entry depth

`CloseoutPreload7.depth_exceeds_prepLen` is a machine-checked negative result:
the entry depth the preparation phase actually reaches is
`max k 1 + 2 + (prepLen k - 1) = prepLen k + max k 1 + 1`
(`CloseoutPreload7.depth_le_prepLen_shifted`), which is **strictly larger** than
`prepLen k`.  So `CloseoutPreload6.runEntriesS_of_namedG`'s side condition
`D ≤ prepLen k` cannot be met by the depth `CloseoutPreload7.entryDepthG_of_prepBound`
supplies: the chain as written forgets the `max k 1` grow ticks and the
`prepare` dispatch.

The only place `D ≤ prepLen k` is used is to bound the advances consumed on the
way in, through `CloseoutPreload6.budget_adv`'s hypothesis
`2048 * adv ≤ prepLen k`.  **That hypothesis has room.**  This file re-proves the
budget with

    2048 * adv ≤ prepLen k + max k 1 + 1

i.e. exactly the true depth, and the conclusion `adv + m + Rad ≤ 2 * max k 1`
is unchanged.  Both halves of the split are tight:

* `k ≥ 9`: the loose bounds `prepLen_le` / `dpEvents_stage_le` suffice
  (`3 * 2048 * (adv+m+Rad) ≤ 11548 k + 6429 ≤ 12288 k` iff `k ≥ 9`);
* `k ≤ 8`: nine concrete cases; at `k = 1, 2, 3, 5, 6` the margin is exactly `0`.

**This removes one of the three recorded arithmetic gaps of the readiness
chain.**  The other two are `CloseoutPreload35` §3 (the four windows
`8 ≤ mw < 32` at slack `2047`) and the event supply at a stage boundary.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageBudgetShift

open PalPeg
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le dpEvents_stage_le)

/-- **NAMED — the stage budget at the true entry depth, over `ℕ`.**
`CloseoutPreload6.budget_adv_nat` with the advance bound shifted by the
`max k 1` grow ticks and the `prepare` dispatch that
`CloseoutPreload7.depth_exceeds_prepLen` showed were missing. -/
theorem budget_adv_nat_shift {k Rad adv m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k + max k 1 + 1)
    (hm : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
    adv + m + Rad ≤ 2 * max k 1 := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;>
      · simp only [prepLen, dpEvents, stageWindow1] at hadv hm
        norm_num at hadv hm
        omega
  · have h1 := prepLen_le k
    have h2 := dpEvents_stage_le k
    have hmax : max k 1 = k := Nat.max_eq_left (by omega)
    rw [hmax] at hadv h1 h2 ⊢
    omega

/-- **NAMED — the same over `ℤ`.**  `CloseoutPreload6.budget_adv` at the true
entry depth. -/
theorem budget_adv_shift {k Rad adv m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k + max k 1 + 1)
    (hm : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
    (adv : ℤ) + (m : ℤ) ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) := by
  have hnat := budget_adv_nat_shift hstage hadv hm
  have hcast : (adv : ℤ) + (m : ℤ) + (Rad : ℤ) ≤ 2 * max (k : ℤ) 1 := by
    have h := (Nat.cast_le (α := ℤ)).mpr hnat
    push_cast at h
    exact h
  rw [PalPeg.GalilReplaySpan.stageDebt]
  omega

/-- Sanity: the shifted budget subsumes `CloseoutPreload6.budget_adv`. -/
theorem budget_adv_of_shift {k Rad adv m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k)
    (hm : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
    (adv : ℤ) + (m : ℤ) ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) :=
  budget_adv_shift hstage (by omega) hm

#print axioms budget_adv_nat_shift
#print axioms budget_adv_shift
#print axioms budget_adv_of_shift

end PalPeg.StageBudgetShift
