/-!
# Towers of exponentials

`tower k m` is `2^2^…^m` with `k` twos: `tower 0 m = m`, `tower (k+1) m = 2 ^ tower k m`. The `k`-fold exponential
bounds of higher-order Macro PEG are stated with it. Sums, products and powers of towers are again towers of the same
height, after adding a constant to the argument:

* `tower_add`: `tower k a + tower k b + 2 ≤ tower k (a + b + 2)`;
* `tower_mul`: `tower (k+1) a * tower (k+1) b ≤ tower (k+1) (a + b + 2)`;
* `tower_pow`: `tower (k+2) a ^ tower (k+1) b ≤ tower (k+2) (a + b + 2)`.
-/

namespace Shallot.MacroPeg.HO

def tower : Nat → Nat → Nat
  | 0, m => m
  | k + 1, m => 2 ^ tower k m

@[simp] theorem tower_zero (m : Nat) : tower 0 m = m := rfl
theorem tower_succ (k m : Nat) : tower (k + 1) m = 2 ^ tower k m := rfl

theorem tower_mono (k : Nat) {a b : Nat} (h : a ≤ b) : tower k a ≤ tower k b := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.pow_le_pow_right (by omega) ih

theorem le_tower : ∀ (k m : Nat), m ≤ tower k m
  | 0, _ => Nat.le_refl _
  | k + 1, m => Nat.le_trans (le_tower k m) (Nat.le_of_lt (Nat.lt_two_pow_self))

theorem tower_le_succ (k m : Nat) : tower k m ≤ tower (k + 1) m := Nat.le_of_lt Nat.lt_two_pow_self

theorem two_pow_add_le (x y : Nat) : 2 ^ x + 2 ^ y + 2 ≤ 2 ^ (x + y + 2) := by
  have hx : 2 ^ x ≤ 2 ^ (x + y) := Nat.pow_le_pow_right (by omega) (by omega)
  have hy : 2 ^ y ≤ 2 ^ (x + y) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ 2 ^ (x + y) := Nat.one_le_two_pow
  rw [Nat.pow_add, Nat.pow_two]; omega

/-- A sum of two towers is a tower. -/
theorem tower_add : ∀ (k a b : Nat), tower k a + tower k b + 2 ≤ tower k (a + b + 2)
  | 0, _, _ => Nat.le_refl _
  | k + 1, a, b => by
    simp only [tower_succ]
    exact Nat.le_trans (two_pow_add_le _ _) (Nat.pow_le_pow_right (by omega) (tower_add k a b))

/-- A product of two towers of positive height is a tower. -/
theorem tower_mul (k a b : Nat) : tower (k + 1) a * tower (k + 1) b ≤ tower (k + 1) (a + b + 2) := by
  simp only [tower_succ, ← Nat.pow_add]
  exact Nat.pow_le_pow_right (by omega) (Nat.le_trans (by omega) (tower_add k a b))

/-- A tower to the power of a lower tower is a tower. -/
theorem tower_pow (k a b : Nat) : tower (k + 2) a ^ tower (k + 1) b ≤ tower (k + 2) (a + b + 2) := by
  rw [tower_succ (k + 1) a, ← Nat.pow_mul, tower_succ (k + 1) (a + b + 2)]
  exact Nat.pow_le_pow_right (by omega) (tower_mul k a b)

/-- Adding a constant inside the tower adds at least as much outside. -/
theorem tower_add_const : ∀ (k x c : Nat), tower k x + c ≤ tower k (x + c)
  | 0, _, _ => Nat.le_refl _
  | k + 1, x, c => by
    simp only [tower_succ]
    have h := tower_add_const k x c
    have hc : c < 2 ^ c := Nat.lt_two_pow_self
    calc 2 ^ tower k x + c ≤ 2 ^ tower k x * 2 ^ c := by
          have hX : 1 ≤ 2 ^ tower k x := Nat.one_le_two_pow
          have h1 : 2 ^ tower k x * (c + 1) ≤ 2 ^ tower k x * 2 ^ c := Nat.mul_le_mul_left _ hc
          have h2 : c ≤ 2 ^ tower k x * c := Nat.le_mul_of_pos_left c hX
          rw [Nat.mul_succ] at h1
          omega
      _ = 2 ^ (tower k x + c) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ tower k (x + c) := Nat.pow_le_pow_right (by omega) h

/-- A constant multiple of a tower of positive height is a tower. -/
theorem tower_mul_const (k x c : Nat) : c * tower (k + 1) x ≤ tower (k + 1) (x + c) := by
  rw [tower_succ, tower_succ]
  have hc : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
  calc c * 2 ^ tower k x ≤ 2 ^ c * 2 ^ tower k x := Nat.mul_le_mul_right _ hc
    _ = 2 ^ (tower k x + c) := by rw [← Nat.pow_add, Nat.add_comm]
    _ ≤ 2 ^ tower k (x + c) := Nat.pow_le_pow_right (by omega) (tower_add_const k x c)

end Shallot.MacroPeg.HO
