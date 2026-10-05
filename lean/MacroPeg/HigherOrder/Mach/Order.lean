import MacroPeg.HigherOrder.Mach.EvalNum

/-!
# The order check on the tables of a reading

`ordNum`: the order of type number `k`, from the arrow table. `ordOK j st`: every rule type has order `≤ j` and every
lambda item binds a type of order `< j` — exactly `GOrd j g s` for the grammar and start that were read (`ordOK_iff`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- The order of type number `k`. -/
def ordNum (tt : List (Nat × Nat)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then max (ordNum tt a + 1) (ordNum tt b) else 0
    | none => 0
termination_by k => k
decreasing_by all_goals omega

/-- The order check on a finished reading. -/
def ordOK (j : Nat) (st : PSt) : Bool :=
  st.rt.all (fun t => decide (ordNum st.tt t ≤ j)) &&
    (st.bodies.flatten ++ st.start).all (fun it => it.tag != 11 || decide (ordNum st.tt it.a + 1 ≤ j))

end Shallot.MacroPeg.Mach
