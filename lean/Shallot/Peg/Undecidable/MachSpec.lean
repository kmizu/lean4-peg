import Shallot.Peg.Undecidable.Chain
import Shallot.Peg.Undecidable.Code
import Complexity.NStackIO
import Complexity.NKit

/-!
# What the stack programs of the reduction do

The reduction `w ↦ encG (k1Grammar w)` runs in two stages on 40 stacks:
- the cards stage turns the input stacks of a good code `w` into the cards of `tablePCPN` on stack 0 and the flag 0
  on stack 1 (`cardsSt`), and of any other input into the flag 1 alone (`badSt`);
- the printing stage turns these into the input stacks of the grammar's bits: Ford's grammar of the cards, or the
  empty grammar — or, for completeness, the loop grammar of either.
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

/-- A card list on a stack: each card as the length and symbols of its top, then of its bottom. -/
def encCards (N : List Card) : List Nat := N.flatMap fun c => c.1.length :: (c.1 ++ c.2.length :: c.2)

/-- After the cards stage on a good code. -/
def cardsSt (N : List Card) : Lists UK := fun i => if i.val = 0 then encCards N else if i.val = 1 then [0] else []

/-- After the cards stage on any other input. -/
def badSt : Lists UK := fun i => if i.val = 1 then [1] else []

/-- The input is the code of a one-tape table in whole chunks. -/
def GoodCode (w : List Bool) (nq na : Nat) (rest : List Nat) : Prop :=
  deUnary w = 1 :: nq :: na :: rest ∧ rest.length % 3 = 0

end Shallot
