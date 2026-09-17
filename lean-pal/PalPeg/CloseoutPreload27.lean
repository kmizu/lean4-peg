import PalPeg.CloseoutPreload26

/-!
# Halving the doubling credit: `stageCredit8`

`CloseoutPreload25` / `CloseoutPreload26` established that the doubling credit
`CloseoutPreload11.stageCredit k m = (m - 8 * max k 1) / 4` is too generous for
a `.double` leg of length exactly `mw` (`CloseoutPreload17.double_spends`), and
`CloseoutPreload26` §3 proposed halving it.  This file carries that proposal
through the two arithmetic steps and reports the result.

* §1 `stageCredit8 k m := (m - 8 * max k 1) / 8`, and `budget_adv2_nat8` — the
  stage budget `CloseoutPreload11.budget_adv2_nat` on the halved credit, closed
  by `omega` with the same inputs (`prepLen_le`, `dpEvents_win_le`).
* §2 `double_len_of_leg8` — the `.double` leg's length inequality on the halved
  credit.  The sufficient threshold, unconditional in `Rad`, is
  `mw + 4 * max k 1 + 4 * c + 7`; `double_len_needs8` gives the matching
  necessary condition `mw + 4 * max k 1 + 4 * c + 4 ≤ L + 4 * Rad`, so **at
  `L = mw` the obligation still fails unless `Rad ≥ max k 1 + c + 1`**
  (`double_len_forces_rad8`), and it is refutable at `Rad = 0`
  (`double_len_false_of_rad_zero8`).  Halving the credit removes the
  `mw - 4 * max k 1` excess of `CloseoutPreload25` but not the base debt.
* §3 **no divisor closes it.**  `double_len_needs_any` shows that for *any*
  non-negative credit the leg must satisfy `8 * max k 1 + 4 * c + 4 ≤ L + 4 * Rad`
  — the base stage debt `2 * max k 1` alone, paid at four ticks per unit, is
  `8 * max k 1` ticks, while the calibration `8 * max k 1 ≤ 2 * mw` only gives
  `mw ≥ 4 * max k 1`.  `double_len_needs_window_any` records the consequence at
  `L = mw`: `8 * max k 1 + 4 * c + 4 ≤ mw + 4 * Rad`, which is not derivable
  from `3 * Rad ≤ 5 * k` and the calibration (`double_len_false_any` at
  `Rad = 0`, `mw = 4 * max k 1`).  Divisor `16` is recorded for the record
  (`double_len_needs16`): threshold `≈ mw / 2 + 6 * max k 1 + 4 * c + 4 - 4 * Rad`.

**Consequence:** step 3 of the proposal (`postRunC8_of_double_leg`) is **not**
attempted — the `.double` clause does not close on `stageCredit8` with `bs.length
= mw` and no side condition.  The real shortfall is the *base* debt
`stageDebt Rad k = 2 * max k 1 - Rad`, which `wait_exit_debt_zero` resets and a
leg of `mw ≥ 4 * max k 1` ticks cannot re-earn.  Either the `.wait` exit must
keep (part of) its debt, or the stage bound must be asked at
`Rad ≥ max k 1 + c + 1`, or the `.double` leg must run `≈ 2 * mw` ticks.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload27

open PalPeg
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le)
open PalPeg.CloseoutPreload11 (dpEvents_win_le)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The halved credit and the stage budget -/

/-- **The halved doubling credit**: one unit of debt per *eight* extra cells. -/
def stageCredit8 (k m : ℕ) : ℕ := (m - 8 * max k 1) / 8

theorem stageCredit8_base (k : ℕ) : stageCredit8 k (8 * max k 1) = 0 := by
  unfold stageCredit8; simp

/-- `stageCredit8` is at most half of `stageCredit`. -/
theorem stageCredit8_le (k m : ℕ) :
    2 * stageCredit8 k m ≤ PalPeg.CloseoutPreload11.stageCredit k m := by
  unfold stageCredit8 PalPeg.CloseoutPreload11.stageCredit
  omega

/-- **NAMED — the stage budget at `(k, m)` on the halved credit.**
`CloseoutPreload11.budget_adv2_nat` with `stageCredit` replaced by
`stageCredit8`.  The demand `adv + mm ≈ m / 41` still fits under
`max k 1 + m / 8 - 5 * k / 3 ≈ m / 8 - 2 * k / 3` because `m ≥ 8 * max k 1`. -/
theorem budget_adv2_nat8 {k Rad adv mm m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hm : 8 * max k 1 ≤ m)
    (hadv : 2048 * adv ≤ prepLen k)
    (hmm : 2048 * mm ≤ prepLen k + dpEvents (m + 1) + 2048) :
    adv + mm + Rad ≤ 2 * max k 1 + stageCredit8 k m := by
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le m
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  have h5 : max k 1 ≤ k + 1 := by omega
  have hq := Nat.div_add_mod (m - 8 * max k 1) 8
  have hq2 : (m - 8 * max k 1) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold stageCredit8
  omega

#print axioms budget_adv2_nat8

/-- The integer form, as `CloseoutPreload11.budget_adv2`. -/
theorem budget_adv2_8 {k Rad adv mm m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hm : 8 * max k 1 ≤ m)
    (hadv : 2048 * adv ≤ prepLen k)
    (hmm : 2048 * mm ≤ prepLen k + dpEvents (m + 1) + 2048) :
    (adv : ℤ) + (mm : ℤ) ≤ stageDebt Rad (k : ℤ) + (stageCredit8 k m : ℤ) := by
  have hnat := budget_adv2_nat8 hstage hm hadv hmm
  have hcast : (adv : ℤ) + (mm : ℤ) + (Rad : ℤ)
      ≤ 2 * max (k : ℤ) 1 + (stageCredit8 k m : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hnat
    push_cast at h
    exact h
  have hmax : stageDebt Rad (k : ℤ) = 2 * max (k : ℤ) 1 - (Rad : ℤ) := rfl
  rw [hmax]
  omega

#print axioms budget_adv2_8

/-! ## 2. The `.double` leg's length inequality on the halved credit -/

private theorem cast_max (k : ℕ) : ((max k 1 : ℕ) : ℤ) = max (k : ℤ) 1 := by
  push_cast; rfl

/-- The obligation of `CloseoutPreload24.round_trip_entries` (`hlen`) with an
arbitrary credit `cr`, against a leg of length `L` with `c` firing ticks. -/
def DoubleLenAt (Rad k c L : ℕ) (cr : ℕ) : Prop :=
  4 * (stageDebt Rad (k : ℤ) + (cr : ℤ) + 1) + 4 * (c : ℤ) + 3 ≤ (L : ℤ)

/-- The obligation on the halved credit. -/
def DoubleLen8 (Rad k mw c L : ℕ) : Prop :=
  DoubleLenAt Rad k c L (stageCredit8 k (2 * mw))

/-- `4 * stageCredit8 k (2 * mw)` sits within `3` of `mw - 4 * max k 1`. -/
private theorem credit8_bounds {k mw : ℕ} (_hcal : 8 * max k 1 ≤ 2 * mw) :
    4 * stageCredit8 k (2 * mw) ≤ mw - 4 * max k 1 ∧
      mw - 4 * max k 1 ≤ 4 * stageCredit8 k (2 * mw) + 3 := by
  unfold stageCredit8
  omega

/-- The obligation, unfolded to plain integer arithmetic. -/
private theorem doubleLenAt_iff (Rad k c L cr : ℕ) :
    DoubleLenAt Rad k c L cr ↔
      8 * ((max k 1 : ℕ) : ℤ) - 4 * (Rad : ℤ) + 4 * (cr : ℤ) + 4 + 4 * (c : ℤ) + 3 ≤ (L : ℤ) := by
  unfold DoubleLenAt
  have hd : stageDebt Rad (k : ℤ) = 2 * max (k : ℤ) 1 - (Rad : ℤ) := rfl
  rw [hd, ← cast_max k]
  constructor <;> intro h <;> omega

/-- **NAMED — the sufficient threshold on the halved credit, unconditional in
`Rad`.**  A `.double` leg of length `mw + 4 * max k 1 + 4 * c + 7` discharges
the obligation for every `Rad`.  Compare `CloseoutPreload25.double_len_of_leg`
(`2 * mw + 4 * c + 7`): halving the credit saves `mw - 4 * max k 1` ticks, but
the threshold is **still above `mw`**, by `4 * max k 1 + 4 * c + 7`. -/
theorem double_len_of_leg8 {Rad k mw c L : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (hL : mw + 4 * max k 1 + 4 * c + 7 ≤ L) : DoubleLen8 Rad k mw c L := by
  obtain ⟨hc1, -⟩ := credit8_bounds (k := k) (mw := mw) hcal
  unfold DoubleLen8
  rw [doubleLenAt_iff]
  have h1 : (4 * stageCredit8 k (2 * mw) : ℤ) ≤ ((mw - 4 * max k 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.cast_le.mpr hc1
  have h2 : ((mw - 4 * max k 1 : ℕ) : ℤ) = (mw : ℤ) - 4 * ((max k 1 : ℕ) : ℤ) := by
    have : (4 * max k 1 : ℕ) ≤ mw := by omega
    push_cast [Nat.cast_sub this]
    ring
  have h3 : (0 : ℤ) ≤ (Rad : ℤ) := Int.natCast_nonneg Rad
  have h4 : (mw + 4 * max k 1 + 4 * c + 7 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  push_cast at h1 h2 h4 ⊢
  omega

#print axioms double_len_of_leg8

/-- **NAMED — the matching necessary condition on the halved credit.**  Any leg
discharging the obligation has length `≥ mw + 4 * max k 1 + 4 * c + 4 - 4 * Rad`. -/
theorem double_len_needs8 {Rad k mw c L : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (h : DoubleLen8 Rad k mw c L) : mw + 4 * max k 1 + 4 * c + 4 ≤ L + 4 * Rad := by
  obtain ⟨-, hc2⟩ := credit8_bounds (k := k) (mw := mw) hcal
  unfold DoubleLen8 at h
  rw [doubleLenAt_iff] at h
  have h1 : ((mw - 4 * max k 1 : ℕ) : ℤ) ≤ (4 * stageCredit8 k (2 * mw) : ℤ) + 3 := by
    exact_mod_cast Nat.cast_le.mpr hc2
  have h2 : ((mw - 4 * max k 1 : ℕ) : ℤ) = (mw : ℤ) - 4 * ((max k 1 : ℕ) : ℤ) := by
    have : (4 * max k 1 : ℕ) ≤ mw := by omega
    push_cast [Nat.cast_sub this]
    ring
  have : (mw + 4 * max k 1 + 4 * c + 4 : ℤ) ≤ (L : ℤ) + 4 * (Rad : ℤ) := by
    push_cast at h h1 h2 ⊢; omega
  exact_mod_cast this

#print axioms double_len_needs8

/-- **NAMED — at `L = mw` the halved-credit obligation forces
`Rad ≥ max k 1 + c + 1`.**  The exact gap at the leg length `double_spends`
delivers is `4 * (max k 1 + c + 1 - Rad)` ticks. -/
theorem double_len_forces_rad8 {Rad k mw c : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (h : DoubleLen8 Rad k mw c mw) : max k 1 + c + 1 ≤ Rad := by
  have := double_len_needs8 hcal h
  omega

#print axioms double_len_forces_rad8

/-- **NAMED — still refutable at `Rad = 0`.** -/
theorem double_len_false_of_rad_zero8 {k mw c : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw) :
    ¬ DoubleLen8 0 k mw c mw := by
  intro h
  have := double_len_forces_rad8 hcal h
  omega

#print axioms double_len_false_of_rad_zero8

/-! ## 3. No divisor closes it: the base debt is the obstruction -/

/-- **NAMED — for any non-negative credit, the leg must pay the base debt.**
`4 * (2 * max k 1 - Rad + cr + 1) + 4 * c + 3 ≤ L` with `cr ≥ 0` forces
`8 * max k 1 + 4 * c + 4 ≤ L + 4 * Rad`, independently of how the credit is
computed.  This is the base stage debt `2 * max k 1` paid at four ticks per
unit (the `.double` balance `4 * debt + quarter`). -/
theorem double_len_needs_any {Rad k c L cr : ℕ} (h : DoubleLenAt Rad k c L cr) :
    8 * max k 1 + 4 * c + 4 ≤ L + 4 * Rad := by
  rw [doubleLenAt_iff] at h
  have h0 : (0 : ℤ) ≤ (cr : ℤ) := Int.natCast_nonneg cr
  have : (8 * max k 1 + 4 * c + 4 : ℤ) ≤ (L : ℤ) + 4 * (Rad : ℤ) := by
    push_cast at h ⊢; omega
  exact_mod_cast this

#print axioms double_len_needs_any

/-- **NAMED — at `L = mw`, for any credit.**  The window must satisfy
`8 * max k 1 + 4 * c + 4 ≤ mw + 4 * Rad`; the calibration only gives
`4 * max k 1 ≤ mw`. -/
theorem double_len_needs_window_any {Rad k mw c cr : ℕ} (h : DoubleLenAt Rad k c mw cr) :
    8 * max k 1 + 4 * c + 4 ≤ mw + 4 * Rad :=
  double_len_needs_any h

#print axioms double_len_needs_window_any

/-- **NAMED — refutable at the calibration boundary for every credit.**  At
`Rad = 0` and `mw = 4 * max k 1` (which satisfies `8 * max k 1 ≤ 2 * mw`), no
credit value makes the leg of length `mw` discharge the obligation.  So no
choice of divisor in `stageCredit` closes the `.double` clause without a side
condition on `Rad` or on `mw`. -/
theorem double_len_false_any {k c cr : ℕ} :
    ¬ DoubleLenAt 0 k c (4 * max k 1) cr := by
  intro h
  have := double_len_needs_any h
  omega

#print axioms double_len_false_any

/-- Divisor `16`, for the record: `stageCredit16 k m := (m - 8 * max k 1) / 16`. -/
def stageCredit16 (k m : ℕ) : ℕ := (m - 8 * max k 1) / 16

/-- **NAMED — the necessary condition at divisor `16`**:
`2 * L + 8 * Rad ≥ mw + 12 * max k 1 + 8 * c + 7`, i.e. the threshold is
`≈ mw / 2 + 6 * max k 1 + 4 * c + 4 - 4 * Rad`, again above `mw` at `Rad = 0`
whenever `mw < 12 * max k 1 + 8 * c + 7`. -/
theorem double_len_needs16 {Rad k mw c L : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (h : DoubleLenAt Rad k c L (stageCredit16 k (2 * mw))) :
    mw + 12 * max k 1 + 8 * c + 7 ≤ 2 * L + 8 * Rad := by
  rw [doubleLenAt_iff] at h
  have hc2 : mw - 4 * max k 1 ≤ 8 * stageCredit16 k (2 * mw) + 7 := by
    unfold stageCredit16; omega
  have h1 : ((mw - 4 * max k 1 : ℕ) : ℤ) ≤ (8 * stageCredit16 k (2 * mw) : ℤ) + 7 := by
    exact_mod_cast Nat.cast_le.mpr hc2
  have h2 : ((mw - 4 * max k 1 : ℕ) : ℤ) = (mw : ℤ) - 4 * ((max k 1 : ℕ) : ℤ) := by
    have : (4 * max k 1 : ℕ) ≤ mw := by omega
    push_cast [Nat.cast_sub this]
    ring
  have : (mw + 12 * max k 1 + 8 * c + 7 : ℤ) ≤ 2 * (L : ℤ) + 8 * (Rad : ℤ) := by
    push_cast at h h1 h2 ⊢; omega
  exact_mod_cast this

#print axioms double_len_needs16

/-!
## 4. What is left

Closed here: `budget_adv2_nat8` / `budget_adv2_8` (the stage budget on the
halved credit, §1); `double_len_of_leg8` / `double_len_needs8` (exact threshold
`mw + 4 * max k 1 + 4 * c + 7`, necessary `mw + 4 * max k 1 + 4 * c + 4 - 4 * Rad`,
§2); `double_len_needs_any` / `double_len_false_any` (no divisor closes it, §3).

**NOT done:** `postRunC8_of_double_leg` — the `.double` clause on `stageCredit8`
with `bs.length = mw` is false at `Rad = 0` (`double_len_false_of_rad_zero8`),
so the budget chain (`CloseoutPreload11`–`24`) is not re-derived on
`stageCredit8`.  The obstruction is the base debt `2 * max k 1` reset by
`CloseoutPreload24.wait_exit_debt_zero`; the credit's divisor is irrelevant to
it (`double_len_needs_any`).  Candidate fixes, none attempted: (a) the `.wait`
exit keeps its debt (then the `.double` leg starts at `≈ 2 * max k 1`, not `0`);
(b) the stage bound is asked at `Rad ≥ max k 1 + c + 1` (a side condition, as
`CloseoutPreload26`); (c) the `.double` leg runs `≈ 2 * mw` ticks
(`CloseoutPreload25`).

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload27
