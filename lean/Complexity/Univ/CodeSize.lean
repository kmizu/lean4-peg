import Complexity.Univ.Code

/-!
# Unary numbers are no larger than their code

The numbers read back from `w`, counted and summed, are at most `|w|` (`deUnary_size`).
-/

namespace Complexity.Univ

theorem deUnaryGo_size : ∀ (a : Nat) (w : List Bool), (deUnaryGo a w).length + (deUnaryGo a w).sum ≤ a + w.length
  | _, [] => by simp [deUnaryGo]
  | a, true :: bs => by
    have := deUnaryGo_size (a + 1) bs
    simp only [deUnaryGo, List.length_cons]; omega
  | a, false :: bs => by
    have := deUnaryGo_size 0 bs
    simp only [deUnaryGo, List.length_cons, List.sum_cons]; omega

/-- **The numbers of a unary code, counted and summed, are at most its length.** -/
theorem deUnary_size (w : List Bool) : (deUnary w).length + (deUnary w).sum ≤ w.length := by
  have := deUnaryGo_size 0 w; unfold deUnary; omega

end Complexity.Univ
