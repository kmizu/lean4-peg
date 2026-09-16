import PalPeg.GSPreprocessProg29

/-! # Amortized bounds for a complete second-phase iteration -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

def soRRate (k : ℕ) : ℕ := 10 * k + 200
def soRPotential (k : ℕ) : ℕ := 7 * k + 100

theorem soR_abort_cost (k q j W : ℕ) (hj : j ≤ W) :
    (17 * j + 9) + 4 + soRPotential k * (q + j) ≤
      soRRate k * (1 + W) + soRPotential k * q := by
  have hh := Nat.mul_le_mul_left (soRPotential k + 17) hj
  unfold soRPotential soRRate at *
  nlinarith

theorem soR_period_cost (k q j W f : ℕ) (hj : j ≤ W) (hf : f ≤ q + j) :
    (17 * j + 8 + ((4 * k + 10) * f + 3 * k + 11) + (f * (3 * k + 17) + 8)) +
      4 + soRPotential k * (q + j - f) ≤
      soRRate k * (1 + W) + soRPotential k * q := by
  have hh := Nat.mul_le_mul_left (soRPotential k + 17) hj
  have he : soRPotential k * (q + j - f) + soRPotential k * f =
      soRPotential k * (q + j) := by rw [← Nat.mul_add, Nat.sub_add_cancel hf]
  unfold soRPotential soRRate at *
  nlinarith

theorem soR_reset_cost (k q j W delta : ℕ) (hj : j ≤ W) (hd : delta ≤ q + j + 1) :
    (17 * j + 8 + (14 * (q + j) + 11) +
      (19 * (q + j) + 7 + (3 * k + 7) * delta)) + 4 ≤
      soRRate k * (1 + W) + soRPotential k * q := by
  have hh := Nat.mul_le_mul_left (soRPotential k + 17) hj
  have hd' := Nat.mul_le_mul_left (3 * k + 7) hd
  unfold soRPotential soRRate at *
  nlinarith

end PalPeg.GSPreProg
