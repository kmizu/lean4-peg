import MacroPeg.HigherOrder.Tower
import MacroPeg.HigherOrder.KExp.LmTime

/-!
# Arithmetic under a tower of height `j ≥ 1`

Sums, products, fifth powers and constant multiples of numbers below towers stay below a tower of the same height,
with the arguments added (`tw_add`, `tw_mul`, `tw_pow5`, `tw_cmul`). A function below `tower j` of a polynomial is
`TowerPoly j` (`towerPoly_of_le`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO

variable {j : Nat}

theorem tw_of_le {a A : Nat} (h : a ≤ A) : a ≤ tower j A := Nat.le_trans h (le_tower _ _)

theorem tw_mono' {a A B : Nat} (h : a ≤ tower j A) (hAB : A ≤ B) : a ≤ tower j B :=
  Nat.le_trans h (tower_mono j hAB)

theorem tw_add {a b A B : Nat} (ha : a ≤ tower j A) (hb : b ≤ tower j B) : a + b ≤ tower j (A + B + 2) := by
  have := tower_add j A B; omega

theorem tw_mul (hj : 1 ≤ j) {a b A B : Nat} (ha : a ≤ tower j A) (hb : b ≤ tower j B) :
    a * b ≤ tower j (A + B + 2) := by
  have := tower_mul (j - 1) A B
  rw [show j - 1 + 1 = j by omega] at this
  exact Nat.le_trans (Nat.mul_le_mul ha hb) this

theorem tw_pow5 (hj : 1 ≤ j) {a A : Nat} (ha : a ≤ tower j A) : a * a * a * a * a ≤ tower j (5 * A + 8) :=
  tw_mono' (tw_mul hj (tw_mul hj (tw_mul hj (tw_mul hj ha ha) ha) ha) ha) (by omega)

theorem tw_cmul (hj : 1 ≤ j) {a A : Nat} (c : Nat) (ha : a ≤ tower j A) : c * a ≤ tower j (A + c) := by
  have := tower_mul_const (j - 1) A c
  rw [show j - 1 + 1 = j by omega] at this
  exact Nat.le_trans (Nat.mul_le_mul_left c ha) this

/-- **Below a tower of a polynomial**: a `TowerPoly j` function. -/
theorem towerPoly_of_le (f : Nat → Nat) (c d : Nat) (h : ∀ n, f n ≤ tower j (c * (n + 1) ^ d)) :
    KExp.TowerPoly j f :=
  ⟨c, d, h⟩

end Shallot.MacroPeg.Mach
