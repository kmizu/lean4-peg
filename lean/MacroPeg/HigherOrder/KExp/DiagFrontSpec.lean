import MacroPeg.HigherOrder.KExp.Diag
import Complexity.NStackIO
import Complexity.NKit

/-!
# What the front of the diagonal machine does

From the input stacks `nInit UK w`, the front reads `w` back as unary numbers. When they are
`k :: nq :: na :: c :: d :: rest` with `rest` in whole chunks of `2k+1`, it lays out the table and the initial
configuration of `w` for the simulator (`SimSt`) and puts the number of steps `diagSteps j c d w` on `CNT`;
otherwise it halts with `false`. Either way it takes at most `frontCost j w` steps.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- The input has the shape of a code. -/
def DiagShape (w : List Bool) (k nq na c d : Nat) (rest : List Nat) : Prop :=
  deUnary w = k :: nq :: na :: c :: d :: rest ∧ rest.length % (2 * k + 1) = 0

/-- A bound on the steps of the front: polynomial in `|w|`, plus the square of the largest number of steps. -/
def frontCost (j : Nat) (w : List Bool) : Nat :=
  1000 * (w.length + 2) ^ 4 + 1000 * (tower j ((w.length + 1) * (w.length + 1) ^ (w.length + 1)) + 2) ^ 2

end Shallot.MacroPeg.KExp
