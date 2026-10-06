import Complexity.Univ.Sim
import Complexity.NKit

/-!
# What the stack simulator of tables does

The simulator runs a table `T` on a finite configuration `c` on 40 stacks (`SimSt`):
- `TBL`: the rows, each as `q :: ws ++ ms` (`encRows`);
- `KS`, `NA`: the number of tapes and of symbols;
- `ST`: the state; `POS`: the heads; `TP`: the tapes, each as its length followed by its cells (`encTapes`);
- `CNT`: the number of steps still to run;
- stacks `7 … 39` are scratch, empty before and after (`UScratch`).

One step costs at most `stepCost T c`, a polynomial of the sizes and of the numbers on the stacks.
-/

namespace Complexity.Univ

abbrev UK : Nat := 40

abbrev TBL : Fin UK := 0
abbrev KS : Fin UK := 1
abbrev NA : Fin UK := 2
abbrev ST : Fin UK := 3
abbrev POS : Fin UK := 4
abbrev TP : Fin UK := 5
abbrev CNT : Fin UK := 6

def encRows (rows : List Row) : List Nat := rows.flatMap fun r => r.1 :: r.2.1 ++ r.2.2

def encTapes (ts : List (List Nat)) : List Nat := ts.flatMap fun t => t.length :: t

/-- Every row writes and moves on `k` tapes. -/
def RowsOK (T : TTable) : Prop := ∀ r ∈ T.rows, r.2.1.length = T.k ∧ r.2.2.length = T.k

/-- The configuration has `k` heads and `k` tapes. -/
def CfgOK (T : TTable) (c : FCfg) : Prop := c.pos.length = T.k ∧ c.tapes.length = T.k

def UScratch (S : Lists UK) : Prop := ∀ i : Fin UK, 7 ≤ i.val → S i = []

/-- The stacks hold the table `T` and the configuration `c`. -/
def SimSt (S : Lists UK) (T : TTable) (c : FCfg) : Prop :=
  S TBL = encRows T.rows ∧ S KS = [T.k] ∧ S NA = [T.na] ∧ S ST = [c.state] ∧ S POS = c.pos ∧
    S TP = encTapes c.tapes

/-- The stacks with the configuration `c` in place. -/
def putCfg (S : Lists UK) (c : FCfg) : Lists UK :=
  ((S.set ST [c.state]).set POS c.pos).set TP (encTapes c.tapes)

def tsz (T : TTable) : Nat := (encRows T.rows).length + (encRows T.rows).sum + T.k + T.na

def csz (c : FCfg) : Nat := c.state + c.pos.length + c.pos.sum + (encTapes c.tapes).length + (encTapes c.tapes).sum

/-- The steps of one simulated step. -/
def stepCost (T : TTable) (c : FCfg) : Nat := 1000 * (tsz T + csz c + 2) ^ 4

/-- The steps of `B` simulated steps. -/
def simCost (T : TTable) (c : FCfg) : Nat → Nat
  | 0 => 10
  | B + 1 => simCost T c B + stepCost T (frun T c B)

end Complexity.Univ
