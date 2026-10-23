import MacroPeg.CBV.SpanMachine
import Shallot.Peg.Separation.Reduce

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- The interval dictionary has quadratic length. -/
theorem spans_length_le (n : Nat) : (spans n).length ≤ (n + 1) * (n + 1) := by
  have h := length_subStrs_le (List.replicate n '0')
  rw [← spans_length] at h
  simpa using h

def spanLookupCost (n : Nat) : Nat := internCost ((n + 1) * (n + 1)) n + 1

theorem spanLookupCost_bound (n : Nat) : internCost (spans n).length n + 1 ≤ spanLookupCost n := by
  have h := Nat.mul_le_mul_right (internStepCost n + 30) (Nat.add_le_add_right (spans_length_le n) 1)
  unfold spanLookupCost
  unfold internCost at *
  omega

/-- Dictionary lookup is a real polynomial-time stack operation, with no constant-time table oracle. -/
theorem spanLookupCost_poly : IsPoly spanLookupCost := by
  have hn := isPoly_add isPoly_id (isPoly_const 1)
  have h2 := isPoly_mul (isPoly_const 2) isPoly_id
  have hstep : IsPoly internStepCost :=
    isPoly_add (isPoly_mul (isPoly_const 2)
      (isPoly_add (isPoly_mul (isPoly_add h2 (isPoly_const 1))
        (isPoly_add h2 (isPoly_const 6))) (isPoly_const 20))) (isPoly_const 22)
  exact isPoly_add (isPoly_mul (isPoly_add (isPoly_mul hn hn) (isPoly_const 1))
    (isPoly_add hstep (isPoly_const 30))) (isPoly_const 1)

end Shallot.MacroPeg.CBV
