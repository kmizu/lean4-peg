/-
# Scheduling arithmetic: turning amortized bounds into real-time guarantees

Two purely arithmetic developments over `ℕ` (discrete time), independent of the
rest of `PalPeg`:

* **S1 (in-order / FIFO service with arrivals and a rate).**  Jobs `1, 2, …`,
  job `i` carrying `work i` units and arriving at time `arr i`, served strictly
  in order by a server that performs `r` work units per time step (a step may be
  split among several jobs, so the server is work-conserving).  We define the
  completion time `finishTime work arr r i` and prove the exact FIFO identity
  `finishTime i = max_{1 ≤ j ≤ i} (arr j + ⌈(∑_{m=j}^{i} work m) / r⌉)`,
  together with the real-time corollary used for a sliding window of length
  `2 * W`: if the cumulative work satisfies `∑_{m ≤ i} work m ≤ c * i`, symbol
  `i` arrives at time `W + i`, and `r ≥ 2 * c`, then every `i ≤ 2 * W`
  finishes by time `2 * W + i`.

* **S2 (Galil's FIFO service inequality / Lindley's recursion).**  Jobs of cost
  `d i` released one per round, a server doing `R` units per round, FIFO order.
  With `backlog i` the number of units still owed at the end of round `i`
  (`backlog (i+1) = (backlog i + d (i+1)) - R`, truncated subtraction), we prove
  Lindley's closed form
  `backlog i = max_{1 ≤ j ≤ i} (∑_{m=j}^{i} d m - R * (i + 1 - j))`,
  the characterisation `backlog i = 0 ↔ every busy interval fits`, and hence
  `fifo_meets_deadlines`: under the interval hypothesis
  `∑_{m=j}^{i} d m ≤ R * (i - j + 1)` the server is never behind at a round
  boundary, i.e. every job `i` is finished by the end of round `i`.

Everything is stated with truncated `ℕ` subtraction and the `Nat.ceil`-free
ceiling division `cdiv a r = (a + r - 1) / r`; maxima are `Finset.sup` over
`Finset.Icc 1 i` (which is `0` on the empty range, exactly what is wanted).
-/
import Mathlib

namespace PalPeg
namespace Schedule

open Finset

/-! ## Ceiling division, `Nat.ceil`-free -/

/-- `cdiv a r = ⌈a / r⌉`, written without `Nat.ceil`. -/
def cdiv (a r : ℕ) : ℕ := (a + r - 1) / r

@[simp] theorem cdiv_zero (r : ℕ) : cdiv 0 r = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [cdiv]
  · simp only [cdiv, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)

theorem cdiv_le_iff {a r k : ℕ} (hr : 0 < r) : cdiv a r ≤ k ↔ a ≤ r * k := by
  rw [cdiv, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hr, Nat.succ_mul, Nat.mul_comm r k]
  omega

theorem cdiv_mono {a b : ℕ} (r : ℕ) (h : a ≤ b) : cdiv a r ≤ cdiv b r :=
  Nat.div_le_div_right (by omega)

theorem cdiv_max (a b r : ℕ) : cdiv (max a b) r = max (cdiv a r) (cdiv b r) :=
  Monotone.map_max (fun _ _ h => cdiv_mono r h)

/-- `⌈(r * a + b) / r⌉ = a + ⌈b / r⌉`. -/
theorem cdiv_mul_add {r : ℕ} (hr : 0 < r) (a b : ℕ) : cdiv (r * a + b) r = a + cdiv b r := by
  have h : r * a + b + r - 1 = r * a + (b + r - 1) := by omega
  rw [cdiv, cdiv, h, Nat.mul_add_div hr]

/-! ## S1: in-order service with arrivals and a rate -/

section S1

variable (work arr : ℕ → ℕ) (r : ℕ)

/-- `cap work arr r i` is the *work clock* at which job `i` completes: the total
number of work units the server has been able to spend by then, jobs being
served strictly in order and job `i` not startable before its arrival time
`arr i` (i.e. before work clock `r * arr i`).  Since the server does exactly `r`
units per step and may split a step between consecutive jobs, this fluid account
is exact at step boundaries. -/
def cap : ℕ → ℕ
  | 0 => 0
  | (i + 1) => max (cap i) (r * arr (i + 1)) + work (i + 1)

/-- The completion time of job `i`, in time steps: job `i` is finished at the end
of step `finishTime work arr r i - 1`, i.e. "by time `finishTime … i`". -/
def finishTime (i : ℕ) : ℕ := cdiv (cap work arr r i) r

@[simp] theorem cap_zero : cap work arr r 0 = 0 := rfl

theorem cap_succ (i : ℕ) :
    cap work arr r (i + 1) = max (cap work arr r i) (r * arr (i + 1)) + work (i + 1) := rfl

/-- Every FIFO busy-period lower bound is dominated by the work clock. -/
theorem le_cap : ∀ (i j : ℕ), 1 ≤ j → j ≤ i →
    r * arr j + ∑ m ∈ Finset.Icc j i, work m ≤ cap work arr r i := by
  intro i
  induction i with
  | zero => intro j hj1 hj2; omega
  | succ i ih =>
    intro j hj1 hj2
    rcases Nat.lt_or_ge j (i + 1) with h | h
    · have hji : j ≤ i := by omega
      rw [Finset.sum_Icc_succ_top (by omega : j ≤ i + 1), cap_succ]
      have hIH := ih j hj1 hji
      have hmax : cap work arr r i ≤ max (cap work arr r i) (r * arr (i + 1)) :=
        le_max_left _ _
      omega
    · have hj : j = i + 1 := by omega
      subst hj
      rw [cap_succ, Finset.Icc_self, Finset.sum_singleton]
      have hmax : r * arr (i + 1) ≤ max (cap work arr r i) (r * arr (i + 1)) :=
        le_max_right _ _
      omega

/-- The work clock is *attained* by some busy-period start `j`. -/
theorem exists_cap : ∀ (i : ℕ), 1 ≤ i →
    ∃ j, 1 ≤ j ∧ j ≤ i ∧
      cap work arr r i = r * arr j + ∑ m ∈ Finset.Icc j i, work m := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨1, le_refl _, le_refl _, ?_⟩
      simp only [Nat.zero_add]
      rw [cap_succ, cap_zero, Finset.Icc_self, Finset.sum_singleton]
      simp only [Nat.zero_add]
      omega
    · obtain ⟨j, hj1, hj2, hj⟩ := ih hi
      rcases Nat.lt_or_ge (r * arr (i + 1)) (cap work arr r i) with h | h
      · refine ⟨j, hj1, by omega, ?_⟩
        rw [Finset.sum_Icc_succ_top (by omega : j ≤ i + 1), cap_succ,
          max_eq_left (le_of_lt h)]
        omega
      · refine ⟨i + 1, by omega, le_refl _, ?_⟩
        rw [cap_succ, Finset.Icc_self, Finset.sum_singleton, max_eq_right h]

/-- **Work-clock form of the FIFO bound.** -/
theorem cap_eq_sup (i : ℕ) :
    cap work arr r i =
      (Finset.Icc 1 i).sup (fun j => r * arr j + ∑ m ∈ Finset.Icc j i, work m) := by
  refine le_antisymm ?_ (Finset.sup_le ?_)
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨j, hj1, hj2, hj⟩ := exists_cap work arr r i hi
      rw [hj]
      exact Finset.le_sup (f := fun j => r * arr j + ∑ m ∈ Finset.Icc j i, work m)
        (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact le_cap work arr r i j hj.1 hj.2

/-- **The FIFO finish-time identity.**  With arrivals `arr` and service rate `r`,
job `i` finishes exactly at
`max_{1 ≤ j ≤ i} (arr j + ⌈(∑_{m=j}^{i} work m) / r⌉)`
(the maximum over all possible busy-period starts `j`; the empty maximum is `0`,
so `finishTime … 0 = 0`). -/
theorem finishTime_eq_sup (hr : 0 < r) (i : ℕ) :
    finishTime work arr r i =
      (Finset.Icc 1 i).sup (fun j => arr j + cdiv (∑ m ∈ Finset.Icc j i, work m) r) := by
  have hbot : (fun x => cdiv x r) (⊥ : ℕ) = (⊥ : ℕ) := cdiv_zero r
  have hsup : ∀ x y : ℕ, (fun x => cdiv x r) (x ⊔ y)
      = (fun x => cdiv x r) x ⊔ (fun x => cdiv x r) y := fun x y => cdiv_max x y r
  rw [finishTime, cap_eq_sup, Finset.apply_sup_eq_sup_comp (fun x => cdiv x r) hsup hbot]
  refine Finset.sup_congr rfl (fun j _ => ?_)
  simp only [Function.comp_apply]
  rw [cdiv_mul_add hr]

/-- **Real-time corollary (sliding window of length `2 * W`).**
If the cumulative work up to job `i` is at most `c * i`, job `i` arrives at time
`W + i`, and the server runs at rate `r ≥ 2 * c`, then every job `i ≤ 2 * W`
finishes by time `2 * W + i`.

(Instantiation: Manacher over a window of length `2 * W`, symbol `i` arriving at
time `W + i` and its flag due at time `2 * W + i`.) -/
theorem finishTime_le (hr : 0 < r) (c W : ℕ)
    (hwork : ∀ i, ∑ m ∈ Finset.Icc 1 i, work m ≤ c * i)
    (harr : ∀ i, arr i = W + i)
    (hrate : 2 * c ≤ r) (i : ℕ) (hi : i ≤ 2 * W) :
    finishTime work arr r i ≤ 2 * W + i := by
  rw [finishTime_eq_sup work arr r hr]
  refine Finset.sup_le (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have harrj : arr j ≤ W + i := by rw [harr]; omega
  have hsub : ∑ m ∈ Finset.Icc j i, work m ≤ ∑ m ∈ Finset.Icc 1 i, work m :=
    Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc hj.1 le_rfl)
  have hceil : cdiv (∑ m ∈ Finset.Icc j i, work m) r ≤ W := by
    rw [cdiv_le_iff hr]
    calc ∑ m ∈ Finset.Icc j i, work m ≤ c * i := le_trans hsub (hwork i)
      _ ≤ c * (2 * W) := Nat.mul_le_mul_left c hi
      _ = 2 * c * W := by ring
      _ ≤ r * W := Nat.mul_le_mul_right W hrate
  omega

end S1

/-! ## S2: Galil's FIFO service inequality (Lindley's recursion) -/

section S2

variable (d : ℕ → ℕ) (R : ℕ)

/-- `backlog d R i` is the number of work units still owed at the end of round
`i`: in round `i` the job of cost `d i` is released and the server performs `R`
units, FIFO.  (`-` is truncated subtraction, i.e. `max 0 (…)`.) -/
def backlog : ℕ → ℕ
  | 0 => 0
  | (i + 1) => (backlog i + d (i + 1)) - R

@[simp] theorem backlog_zero : backlog d R 0 = 0 := rfl

theorem backlog_succ (i : ℕ) :
    backlog d R (i + 1) = (backlog d R i + d (i + 1)) - R := rfl

/-- Every busy-interval deficit is a lower bound for the backlog. -/
theorem le_backlog : ∀ (i j : ℕ), 1 ≤ j → j ≤ i →
    (∑ m ∈ Finset.Icc j i, d m) - R * (i + 1 - j) ≤ backlog d R i := by
  intro i
  induction i with
  | zero => intro j hj1 hj2; omega
  | succ i ih =>
    intro j hj1 hj2
    rcases Nat.lt_or_ge j (i + 1) with h | h
    · have hji : j ≤ i := by omega
      have hstep : R * (i + 1 + 1 - j) = R * (i + 1 - j) + R := by
        have he : i + 1 + 1 - j = (i + 1 - j) + 1 := by omega
        rw [he, Nat.mul_succ]
      rw [Finset.sum_Icc_succ_top (by omega : j ≤ i + 1), hstep, backlog_succ]
      have hIH := ih j hj1 hji
      omega
    · have hj : j = i + 1 := by omega
      subst hj
      rw [Finset.Icc_self, Finset.sum_singleton, backlog_succ]
      have hstep : R * (i + 1 + 1 - (i + 1)) = R := by
        have he : i + 1 + 1 - (i + 1) = 1 := by omega
        rw [he, Nat.mul_one]
      rw [hstep]
      omega

/-- A nonzero backlog is *attained* by some busy-interval start `j`. -/
theorem exists_backlog : ∀ (i : ℕ), backlog d R i = 0 ∨
    ∃ j, 1 ≤ j ∧ j ≤ i ∧
      backlog d R i = (∑ m ∈ Finset.Icc j i, d m) - R * (i + 1 - j) := by
  intro i
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    by_cases hb : backlog d R (i + 1) = 0
    · exact Or.inl hb
    refine Or.inr ?_
    have hstep1 : R * (i + 1 + 1 - (i + 1)) = R := by
      have he : i + 1 + 1 - (i + 1) = 1 := by omega
      rw [he, Nat.mul_one]
    rcases ih with h0 | ⟨j, hj1, hj2, hj⟩
    · -- the server was idle at the end of round `i`: the busy interval starts here
      refine ⟨i + 1, by omega, le_refl _, ?_⟩
      rw [Finset.Icc_self, Finset.sum_singleton, hstep1, backlog_succ, h0]
      omega
    · rcases Nat.eq_zero_or_pos (backlog d R i) with h0 | hpos
      · refine ⟨i + 1, by omega, le_refl _, ?_⟩
        rw [Finset.Icc_self, Finset.sum_singleton, hstep1, backlog_succ, h0]
        omega
      · -- the earlier busy interval `j..i` was not truncated, so it extends
        have hstep : R * (i + 1 + 1 - j) = R * (i + 1 - j) + R := by
          have he : i + 1 + 1 - j = (i + 1 - j) + 1 := by omega
          rw [he, Nat.mul_succ]
        refine ⟨j, hj1, by omega, ?_⟩
        rw [Finset.sum_Icc_succ_top (by omega : j ≤ i + 1), hstep, backlog_succ]
        omega

/-- **Lindley's recursion in closed form.**  The backlog at the end of round `i`
is the largest deficit over all busy intervals ending at `i`:
`backlog i = max_{1 ≤ j ≤ i} (∑_{m=j}^{i} d m - R * (i + 1 - j))`
(truncated subtraction; the empty maximum is `0`). -/
theorem backlog_eq_sup (i : ℕ) :
    backlog d R i =
      (Finset.Icc 1 i).sup (fun j => (∑ m ∈ Finset.Icc j i, d m) - R * (i + 1 - j)) := by
  refine le_antisymm ?_ (Finset.sup_le ?_)
  · rcases exists_backlog d R i with h0 | ⟨j, hj1, hj2, hj⟩
    · omega
    · rw [hj]
      exact Finset.le_sup
        (f := fun j => (∑ m ∈ Finset.Icc j i, d m) - R * (i + 1 - j))
        (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact le_backlog d R i j hj.1 hj.2

/-- **The backlog vanishes exactly when every busy interval fits.** -/
theorem backlog_eq_zero_iff (i : ℕ) :
    backlog d R i = 0 ↔
      ∀ j, 1 ≤ j → j ≤ i → (∑ m ∈ Finset.Icc j i, d m) ≤ R * (i + 1 - j) := by
  rw [backlog_eq_sup]
  constructor
  · intro h j hj1 hj2
    have := (Finset.sup_eq_bot_iff _ _).mp h j (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
    simp only [bot_eq_zero] at this
    omega
  · intro h
    refine (Finset.sup_eq_bot_iff _ _).mpr (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have := h j hj.1 hj.2
    simp only [bot_eq_zero]
    omega

/-- **Galil's FIFO service inequality.**  If every busy interval `j..i` satisfies
`∑_{m=j}^{i} d m ≤ R * (i - j + 1)`, then a FIFO server doing `R` units per round
is never behind at a round boundary: `backlog i = 0` for all `i`, i.e. the job
released in round `i` is finished by the end of round `i`. -/
theorem fifo_meets_deadlines
    (h : ∀ j i, 1 ≤ j → j ≤ i → (∑ m ∈ Finset.Icc j i, d m) ≤ R * (i - j + 1)) :
    ∀ i, backlog d R i = 0 := by
  intro i
  refine (backlog_eq_zero_iff d R i).mpr (fun j hj1 hj2 => ?_)
  have he : i + 1 - j = i - j + 1 := by omega
  rw [he]
  exact h j i hj1 hj2

end S2

end Schedule
end PalPeg
