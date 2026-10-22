import Shallot.Peg.Separation.Main

/-!
# Diagonal decoder boundary cases

Malformed codes reject before simulation. Small zero-tape examples check
that the diagonal answer complements acceptance, including halted runs.
-/

namespace Shallot.PegSeparation.Examples

open Complexity.Univ

example : ¬ PolyDiag 15 [] := by simp [PolyDiag, deUnary, deUnaryGo]
example : ¬ PolyDiag 15 (unary [1, 3, 3, 0, 999, 0]) := by unfold PolyDiag; rw [deUnary_unary]; decide
example : PolyDiag 0 (unary [0, 3, 3, 0, 0]) := by unfold PolyDiag; rw [deUnary_unary]; decide
example : ¬ PolyDiag 0 (unary [0, 3, 3, 0, 0, 0, 0, 0]) := by unfold PolyDiag; rw [deUnary_unary]; decide

/-- The lifted witness has no words containing a character outside the binary alphabet. -/
example : ¬ liftBinary (PolyDiag 15) ['x'] := by
  rintro ⟨w, hw, _⟩
  cases w with
  | nil => cases hw
  | cons b bs =>
    have he : 'x' = binaryChar b := (List.cons.inj hw).1
    cases b <;> cases he

end Shallot.PegSeparation.Examples
