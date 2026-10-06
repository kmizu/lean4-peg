import MacroPeg.HigherOrder.KExp.DiagBoundSpec

/-!
# The worst-case steps of the diagonal machine are below a tower of height `j + 1`

`diagBoundN j n ≤ tower (j + 1) (c · (n + 1)^2)` for a constant `c` (`diagBoundN_le`). Every piece of `diagBoundN`
is built from `diagX j n ≤ tower (j + 1) ((n + 2)^2)` and `n + 3 ≤ (n + 2)^2` by sums, products and constant
multiples, which stay below a tower of height `j + 1` with a linear argument (`diagBound_generic`).
-/

namespace Shallot.MacroPeg.KExp

open Shallot.MacroPeg.HO Shallot.MacroPeg.Mach

/-- A fourth power below a tower of height `J ≥ 1`. -/
theorem tw_pow4 {J : Nat} (hJ : 1 ≤ J) {a A : Nat} (ha : a ≤ tower J A) : a ^ 4 ≤ tower J (4 * A + 6) := by
  have h : a ^ 4 = a * a * a * a := by simp [Nat.pow_succ, Nat.mul_assoc]
  rw [h]
  exact tw_mono' (tw_mul hJ (tw_mul hJ (tw_mul hJ ha ha) ha) ha) (by omega)

/-- A square below a tower of height `J ≥ 1`. -/
theorem tw_sq {J : Nat} (hJ : 1 ≤ J) {a A : Nat} (ha : a ≤ tower J A) : a ^ 2 ≤ tower J (2 * A + 2) := by
  have h : a ^ 2 = a * a := by simp [Nat.pow_succ]
  rw [h]
  exact tw_mono' (tw_mul hJ ha ha) (by omega)

/-- **The shape of `diagBoundN`, for any `X` below `tower J A` with `n + 3 ≤ A`.** -/
theorem diagBound_generic {J : Nat} (hJ : 1 ≤ J) {X n A : Nat} (hX : X ≤ tower J A) (hN : n + 3 ≤ A) :
    1000 * (n + 2) ^ 4 + 1000 * (X + 2) ^ 2 + 10 +
      X * (1000 * (7 * n + 4 + X * ((n + 1) * (n + 3)) + 2) ^ 4) + 2 ≤ tower J (30 * A + 4000) := by
  have hA : A ≤ tower J A := le_tower J A
  have hn2 : n + 2 ≤ tower J A := Nat.le_trans (by omega) hA
  have hn1 : n + 1 ≤ tower J A := Nat.le_trans (by omega) hA
  have hn3 : n + 3 ≤ tower J A := Nat.le_trans hN hA
  have h2 : 2 ≤ tower J 2 := le_tower J 2
  have h10 : 10 ≤ tower J 10 := le_tower J 10
  -- 1000 (n+2)^4
  have q1 := tw_cmul hJ 1000 (tw_pow4 hJ hn2)
  -- 1000 (X+2)^2
  have q2 := tw_cmul hJ 1000 (tw_sq hJ (tw_add hX h2))
  -- the inner sum
  have h7 : 7 * n + 4 ≤ tower J (A + 7) :=
    Nat.le_trans (by omega) (tw_cmul hJ 7 hn1)
  have hp := tw_mul hJ hX (tw_mul hJ hn1 hn3)
  have hin := tw_add (tw_add h7 hp) h2
  have q3 := tw_mul hJ hX (tw_cmul hJ 1000 (tw_pow4 hJ hin))
  have hall := tw_add (tw_add (tw_add (tw_add q1 q2) h10) q3) h2
  exact tw_mono' hall (by omega)

/-- `n + 3 ≤ (n + 2)^2`. -/
theorem succ3_le_sq (n : Nat) : n + 3 ≤ (n + 2) * (n + 2) := by
  have : 2 * (n + 2) ≤ (n + 2) * (n + 2) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- `(n + 2)^2 ≤ 4 (n + 1)^2`. -/
theorem sq2_le (n : Nat) : (n + 2) * (n + 2) ≤ 4 * (n + 1) ^ 2 := by
  have h : n + 2 ≤ 2 * (n + 1) := by omega
  have h' : (n + 2) * (n + 2) ≤ (2 * (n + 1)) * (2 * (n + 1)) := Nat.mul_le_mul h h
  have e : (2 * (n + 1)) * (2 * (n + 1)) = 4 * (n + 1) ^ 2 := by
    rw [Nat.pow_two, Nat.mul_mul_mul_comm]
  omega

/-- `1 ≤ (n + 1)^2`. -/
theorem one_le_sq (n : Nat) : 1 ≤ (n + 1) ^ 2 := by
  have h := Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 2
  rw [Nat.one_pow] at h
  exact h

/-- **The worst-case steps of the diagonal machine are below `tower (j + 1)` of a quadratic.** -/
theorem diagBoundN_le (j : Nat) : ∃ c : Nat, ∀ n : Nat, diagBoundN j n ≤ tower (j + 1) (c * (n + 1) ^ 2) := by
  refine ⟨4120, fun n => ?_⟩
  have hX : diagX j n ≤ tower (j + 1) ((n + 2) * (n + 2)) := tower_unary_le j n
  have hg := diagBound_generic (by omega) hX (succ3_le_sq n)
  have h4 := sq2_le n
  have h1 := one_le_sq n
  unfold diagBoundN
  refine tw_mono' hg ?_
  generalize (n + 2) * (n + 2) = A at h4
  generalize (n + 1) ^ 2 = M at h4 h1
  omega

end Shallot.MacroPeg.KExp
