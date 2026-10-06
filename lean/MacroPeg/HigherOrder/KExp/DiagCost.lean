import MacroPeg.HigherOrder.KExp.DiagBoundSpec
import MacroPeg.HigherOrder.KExp.DiagFront
import MacroPeg.HigherOrder.KExp.DiagRows
import Complexity.Univ.SimBound
import Complexity.Univ.CodeSize

/-!
# The steps of the diagonal machine are within `diagBoundN`

On an input of the right shape, the table, the constants and the initial configuration are no larger than the
input (`diag_sizes`), so the front, the simulation and the answer stay within `diagBoundN j |w|`
(`diag_cost_le`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

section Sizes

variable {w : List Bool} {k nq na c d : Nat} {rest : List Nat}

/-- The numbers of the code, and the table, are no larger than the input. -/
theorem diag_sizes (h : DiagShape w k nq na c d rest) :
    k ≤ w.length ∧ c ≤ w.length ∧ d ≤ w.length ∧ tsz (tableOfNums k nq na rest) ≤ w.length := by
  have hs := deUnary_size w
  rw [h.1] at hs
  simp only [List.length_cons, List.sum_cons] at hs
  have ht : tsz (tableOfNums k nq na rest) = rest.length + rest.sum + k + na := by
    simp only [tsz, tableOfNums, encRows_decRows]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The steps simulated are at most `diagX j |w|`. -/
theorem diagSteps_le (j : Nat) (hc : c ≤ w.length) (hd : d ≤ w.length) : diagSteps j c d w ≤ diagX j w.length := by
  unfold diagSteps diagX
  apply tower_mono
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

end Sizes

/-- The simulation bound is monotone in the size of the table, the configuration and the steps. -/
theorem simBound_le_of {T : TTable} {cf : FCfg} {B : Nat} {s g X : Nat} (ht : tsz T + csz cf ≤ s)
    (hg : growth T ≤ g) (hB : B ≤ X) :
    simBound T cf B ≤ 10 + X * (1000 * (s + X * g + 2) ^ 4) := by
  unfold simBound
  have h₁ : B * growth T ≤ X * g := Nat.mul_le_mul hB hg
  have h₂ : (tsz T + csz cf + B * growth T + 2) ^ 4 ≤ (s + X * g + 2) ^ 4 :=
    Nat.pow_le_pow_left (by omega) _
  have h₃ := Nat.mul_le_mul hB (Nat.mul_le_mul_left 1000 h₂)
  omega

/-- **The front, `B` simulated steps and the answer stay within `diagBoundN`.** -/
theorem diag_cost_le (j : Nat) {w : List Bool} {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    frontCost j w + simBound (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w) + 2 ≤
      diagBoundN j w.length := by
  obtain ⟨hk, hc, hd, ht⟩ := diag_sizes h
  have hcs := finit_csz k w
  have hg : growth (tableOfNums k nq na rest) ≤ (w.length + 1) * (w.length + 3) := by
    unfold growth
    exact Nat.mul_le_mul (by simp [tableOfNums]; omega) (by omega)
  have hs := simBound_le_of (T := tableOfNums k nq na rest) (cf := finit k w)
    (s := 7 * w.length + 4) (by omega) hg (diagSteps_le j hc hd)
  unfold diagBoundN frontCost
  unfold diagX at hs ⊢
  omega

end Shallot.MacroPeg.KExp
