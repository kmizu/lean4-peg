import MacroPeg.HigherOrder.Mach.TowerArith

/-!
# A power of two under a tower is one level higher

`tower j (2^m) = tower (j+1) m` (`tower_two_pow`). With `(n+1)^(n+1)` below `2^((n+1)^2)`, a tower of height `j`
of a number given in unary stays below a tower of height `j+1` of a polynomial (`tower_unary_le`).
-/

namespace Shallot.MacroPeg.KExp

open Shallot.MacroPeg.HO

theorem tower_two_pow : ∀ (j m : Nat), tower j (2 ^ m) = tower (j + 1) m
  | 0, _ => rfl
  | j + 1, m => by rw [tower, tower_two_pow j m]; rfl

theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := Nat.lt_two_pow_self

/-- `a^b ≤ 2^(a·b)`. -/
theorem pow_le_two_pow_mul (a b : Nat) : a ^ b ≤ 2 ^ (a * b) := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_of_lt (lt_two_pow_self a)) b

/-- **A tower of height `j` of `(n+1)·(n+1)^(n+1)` is below a tower of height `j+1` of `(n+2)^2`.** -/
theorem tower_unary_le (j n : Nat) : tower j ((n + 1) * (n + 1) ^ (n + 1)) ≤ tower (j + 1) ((n + 2) * (n + 2)) := by
  rw [← tower_two_pow]
  apply tower_mono
  have h₁ : (n + 1) * (n + 1) ^ (n + 1) = (n + 1) ^ (n + 2) := by
    rw [show (n + 1) ^ (n + 2) = (n + 1) ^ (n + 1) * (n + 1) from Nat.pow_succ _ _, Nat.mul_comm]
  rw [h₁]
  refine Nat.le_trans (pow_le_two_pow_mul _ _) (Nat.pow_le_pow_right (by decide) ?_)
  exact Nat.mul_le_mul (by omega) (Nat.le_refl _)

end Shallot.MacroPeg.KExp
