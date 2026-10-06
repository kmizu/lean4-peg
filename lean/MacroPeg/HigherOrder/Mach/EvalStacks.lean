import MacroPeg.HigherOrder.Mach.EvalTables
import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# The stacks of the evaluation stage

After reading, the stacks `6`–`17` keep the tables of the reading (`TTs CTs LTs RTs BOD NB STA XS NTT NCT NLT NRT`).
The evaluation stage adds:

* `ORD` (34), `SZ` (35): the order and the capped size of every type number (entry `k` at index `k` from the bottom);
* `CNT` (36): the number of tabulated rows of every type number; `ROWS` (38): all tabulated rows, type by type,
  row by row, flattened; `ROFF` (0): where the rows of each type number start in `ROWS`;
* `VALT` (37): the length of the written-out values of every type number; `ENVT` (2): the number of environments
  of every context number;
* `CAP` (39): the cap; `NX` (1): the length of the input string;
* `EV` (3), `EVL` (4): the evaluation stack (packed vectors one after another) and their lengths; `RV` (5): the
  values of the rules, one after another; `RV2` (16): the values of the next round.

Stacks `18`–`33` are scratch: empty before and after every procedure.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

abbrev ROFF : Fin NK := 0
abbrev NX : Fin NK := 1
abbrev ENVT : Fin NK := 2
abbrev EV : Fin NK := 3
abbrev EVL : Fin NK := 4
abbrev RV : Fin NK := 5
abbrev RV2 : Fin NK := 16
abbrev ORD : Fin NK := 34
abbrev SZ : Fin NK := 35
abbrev CNT : Fin NK := 36
abbrev VALT : Fin NK := 37
abbrev ROWS : Fin NK := 38
abbrev CAP : Fin NK := 39

/-- The scratch stacks are empty. -/
def ScratchEmpty (S : Lists NK) : Prop := ∀ i : Fin NK, 18 ≤ i.val → i.val ≤ 33 → S i = []

/-! ## The tables, as lists -/

section Tables

variable (j cap N : Nat) (tt ct : List (Nat × Nat))

/-- Entry `k` of a table over the type numbers `0, …, tt.length`. -/
def typeTable (f : Nat → Nat) : List Nat := (List.range (tt.length + 1)).map f

def cntTable : List Nat := typeTable tt (fun k => (rowsT j cap N tt k).length)
def valTable : List Nat := typeTable tt (valT j cap N tt)
def rowsFlat : List Nat := ((List.range (tt.length + 1)).map (fun k => (rowsT j cap N tt k).flatten)).flatten
def roffTable : List Nat :=
  typeTable tt (fun k => (((List.range k).map (fun k' => (rowsT j cap N tt k').flatten)).flatten).length)
/-- Entry `c` is the number of environments of context number `c`, for `c ≤ ct.length`. -/
def envTable : List Nat := (List.range (ct.length + 1)).map (envT j cap N tt ct)

end Tables

end Shallot.MacroPeg.Mach
