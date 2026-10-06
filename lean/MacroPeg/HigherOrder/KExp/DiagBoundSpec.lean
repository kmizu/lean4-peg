import MacroPeg.HigherOrder.KExp.TowerShift

/-!
# The worst-case steps of the diagonal machine, in the length of the input

`diagX j n` bounds the steps it simulates, and `diagBoundN j n` bounds the front, the simulation and the answer.
-/

namespace Shallot.MacroPeg.KExp

open Shallot.MacroPeg.HO

/-- The largest number of steps simulated on an input of length `n`. -/
def diagX (j n : Nat) : Nat := tower j ((n + 1) * (n + 1) ^ (n + 1))

/-- The steps of the diagonal machine on an input of length `n`. -/
def diagBoundN (j n : Nat) : Nat :=
  1000 * (n + 2) ^ 4 + 1000 * (diagX j n + 2) ^ 2 + 10 +
    diagX j n * (1000 * (7 * n + 4 + diagX j n * ((n + 1) * (n + 3)) + 2) ^ 4) + 2

end Shallot.MacroPeg.KExp
