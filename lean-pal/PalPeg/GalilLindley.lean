import PalPeg.GalilPredictability

/-!
# Lindley recursion versus the FIFO backlog

Arrivals every `τ` ticks; checkpoint `m` needs `d m` work ticks after both the
previous checkpoint and the arrival of letter `m` (time `m·τ`). The completion
time `S` obeys the Lindley recursion. With `2c ≤ τ` it stays within
`backlog d c m + 2c` of the arrival, so a zero backlog means the checkpoint is
done before the next arrival.
-/

set_option autoImplicit false
namespace PalPeg.Lindley

open PalPeg.Predictability

/-- Completion time of checkpoint `m`. -/
def S (d : ℕ → ℕ) (τ : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => max (S d τ m) ((m+1)*τ) + d (m+1)

theorem S_succ (d : ℕ → ℕ) (τ m : ℕ) :
    S d τ (m+1) = max (S d τ m) ((m+1)*τ) + d (m+1) := rfl

/-- **Lindley ≤ backlog.** -/
theorem lindley_le_backlog (d : ℕ → ℕ) (c τ : ℕ) (hτ : 2*c ≤ τ) :
    ∀ m, S d τ m ≤ m*τ + backlog d c m + 2*c := by
  intro m
  induction m with
  | zero => simp [S, backlog]
  | succ m ih =>
    have hb : backlog d c (m+1) = backlog d c m + d (m+1) - 2*c := rfl
    rw [S_succ, hb, Nat.succ_mul]
    rcases le_total (S d τ m) (m*τ + τ) with h | h
    · rw [Nat.succ_mul, max_eq_right h]; omega
    · rw [Nat.succ_mul, max_eq_left h]; omega

/-- A caught-up backlog means the checkpoint finishes before the next arrival. -/
theorem checkpoint_on_time (d : ℕ → ℕ) (c τ : ℕ) (hτ : 2*c ≤ τ) (m : ℕ)
    (h0 : backlog d c m = 0) : S d τ m ≤ (m+1)*τ := by
  have := lindley_le_backlog d c τ hτ m
  rw [Nat.succ_mul]; omega

/-- One step of the monotone upper bound: a run reaching checkpoint `m+1`
within `d (m+1)` ticks after `max t ((m+1)τ)`, with `t ≤ S m`, is on time
for `S (m+1)`. -/
theorem S_of_run_step (d : ℕ → ℕ) (τ m t t' : ℕ) (ht : t ≤ S d τ m)
    (ht' : t' ≤ max t ((m+1)*τ) + d (m+1)) : t' ≤ S d τ (m+1) := by
  rw [S_succ]
  have : max t ((m+1)*τ) ≤ max (S d τ m) ((m+1)*τ) := max_le_max ht le_rfl
  omega

/-- **Runs are bounded by `S`.** Any run obeying the Lindley step as an upper
bound (possibly faster) reaches every checkpoint no later than `S`. -/
theorem S_of_run (d : ℕ → ℕ) (τ : ℕ) (T : ℕ → ℕ) (h0 : T 0 = 0)
    (hstep : ∀ m, T (m+1) ≤ max (T m) ((m+1)*τ) + d (m+1)) :
    ∀ m, T m ≤ S d τ m := by
  intro m
  induction m with
  | zero => simp [h0, S]
  | succ m ih => exact S_of_run_step d τ m (T m) (T (m+1)) ih (hstep m)

/-- Combined: a run whose backlog is zero at `m` has reached checkpoint `m`
by the arrival of letter `m+1`. -/
theorem run_on_time (d : ℕ → ℕ) (c τ : ℕ) (hτ : 2*c ≤ τ) (T : ℕ → ℕ) (h0 : T 0 = 0)
    (hstep : ∀ m, T (m+1) ≤ max (T m) ((m+1)*τ) + d (m+1)) (m : ℕ)
    (hz : backlog d c m = 0) : T m ≤ (m+1)*τ :=
  le_trans (S_of_run d τ T h0 hstep m) (checkpoint_on_time d c τ hτ m hz)

#print axioms lindley_le_backlog
#print axioms checkpoint_on_time
#print axioms S_of_run
#print axioms run_on_time

end PalPeg.Lindley
