import PalPeg.CloseoutPreload7
import PalPeg.CloseoutPreload35

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
chain.**  §2 shrinks the second: `CloseoutPreload35.bal_of_paced_slack_S` asks
for `32 ≤ mw`, but the bounds it already uses give the balance from `16 ≤ mw`,
and `8 * max k 1 ≤ 2 * mw` makes every stage with `4 ≤ k` land there.  The
residual window is exactly `4 ≤ mw ≤ 15`, i.e. `k ≤ 3`.  The third gap — the
event supply at a stage boundary — is untouched.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageBudgetShift

open PalPeg
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le dpEvents_stage_le)
open PalPeg.CloseoutPreload11 (dpEvents_win_le)
open PalPeg.CloseoutPreload35 (dpDemandS)
open PalPeg.CloseoutReadyStage (PacedL)

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

/-! ## 2. The slack-`2047` balance from `16 ≤ mw` -/

/-- **NAMED — `CloseoutPreload35.bal_of_paced_slack_S` from `16 ≤ mw`.**  Same
proof, same inputs (`prepLen_le`, `dpEvents_win_le`, the pacing at the full
window); the hypothesis `32 ≤ mw` was conservative.  `16` is sharp *for these
bounds*: at `mw = 15` the worst admissible `(prepLen k, dpEvents (2mw+1), count)`
gives a balance of `16 > 15`. -/
theorem bal_of_paced_slack_S16 {k mw slack : ℕ} {bs : List Bool} {a : Bool}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hslack : slack ≤ 2047) (hp : PacedL 2048 slack (bs ++ [a])) :
    4 * dpDemandS k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw := by
  have hc : 2048 * (bs ++ [a]).count true ≤ (bs ++ [a]).length + slack := by
    have h := hp (bs ++ [a]).length
    rwa [List.take_length] at h
  have hl : (bs ++ [a]).length = mw + 1 := by simp [hblen]
  rw [hl] at hc
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le (2 * mw)
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  have hM : 4 * max k 1 ≤ mw := by omega
  unfold dpDemandS
  rcases Nat.lt_or_ge mw 20 with hlt | hge
  · have hk : max k 1 ≤ 4 := by omega
    interval_cases mw <;> omega
  · omega

/-- **Every stage with `4 ≤ k` is covered.**  The calibration
`8 * max k 1 ≤ 2 * mw` forces `4 * k ≤ mw`, so `k ≥ 4` puts the window past the
threshold of `bal_of_paced_slack_S16`.  The residual is therefore `k ≤ 3`
(equivalently `mw ≤ 15`), not the `8 ≤ mw < 32` recorded in
`CloseoutPreload35` §3. -/
theorem window_covered_of_k {k mw : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw) (hk : 4 ≤ k) :
    16 ≤ mw := by
  have h3 : k ≤ max k 1 := le_max_left _ _
  omega

/-- **The residual, exactly.**  What `bal_of_paced_slack_S16` does not reach is
`mw < 16`, and the calibration turns that into `k ≤ 3`: only the first stages.
(`CloseoutPreload35` §3 recorded the residual as `8 ≤ mw < 32`; the true one is
`4 ≤ mw ≤ 15`, and `mw ≤ 3` is vacuous because `8 * max k 1 ≤ 2 * mw` needs
`4 ≤ mw`.) -/
theorem window_residual {k mw : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw) (hmw : mw < 16) :
    k ≤ 3 ∧ 4 ≤ mw := by
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  omega

#print axioms bal_of_paced_slack_S16
#print axioms window_covered_of_k
#print axioms window_residual

end PalPeg.StageBudgetShift
