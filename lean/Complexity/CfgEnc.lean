import Complexity.Formula
import Complexity.Prog

/-!
# Configurations as blocks of Boolean variables

For a machine `M` and a space bound `S`, a configuration that fits (`Good`) is encoded on a *block* `b : Name` by the
variables `b ++ v` for the suffix patterns `v ∈ blockSuf M S`: `[0, q]` (state `q`), `[1, i, j]` (head of tape `i` at
cell `j`), `[2, i, j, c]` (tape `i` holds `c` at cell `j`). `bit c v` is the value of pattern `v` in configuration `c`,
and `Encodes ρ b c` says the block holds exactly these values.

Formulas over blocks: `initF` (the block holds a given configuration), `eqF` (two blocks hold the same values),
`accF` (the state is `0`), `wfF` (the block holds some fitting configuration: exactly one state, one head position per
tape, one symbol per cell), and `stepF` (the second block holds the successor of the first).
-/

namespace Complexity

def sSuf (nq : Nat) : List (List Nat) := (List.range nq).map (fun q => [0, q])

def hSuf (k S : Nat) : List (List Nat) := (List.range k).flatMap (fun i => (List.range S).map (fun j => [1, i, j]))

def cSuf (k S na : Nat) : List (List Nat) :=
  (List.range k).flatMap (fun i => (List.range S).flatMap (fun j => (List.range na).map (fun c => [2, i, j, c])))

section Enc

variable {k : Nat} (M : TM k) (S : Nat)

def blockSuf : List (List Nat) := sSuf M.nq ++ hSuf k S ++ cSuf k S M.na

def blockVars (b : Name) : List Name := (blockSuf M S).map (b ++ ·)

/-- The configuration fits: state and symbols in range, heads inside `S`, blank from `S` on. -/
def Good (c : Cfg k) : Prop :=
  c.state < M.nq ∧ ∀ i : Fin k, c.pos i < S ∧ ∀ j, (j < S → c.cells i j < M.na) ∧ (S ≤ j → c.cells i j = 0)

variable {M} {S}

/-- The value of a suffix pattern in a configuration. -/
def bit (c : Cfg k) : List Nat → Bool
  | [0, q] => decide (c.state = q)
  | [1, i, j] => if h : i < k then decide (c.pos ⟨i, h⟩ = j) else false
  | [2, i, j, s] => if h : i < k then decide (c.cells ⟨i, h⟩ j = s) else false
  | _ => false

variable (M) (S)

def Encodes (ρ : Name → Bool) (b : Name) (c : Cfg k) : Prop := ∀ v ∈ blockSuf M S, ρ (b ++ v) = bit c v

/-- The block holds the configuration `c` (as constants). -/
def initF (b : Name) (c : Cfg k) : Formula :=
  bigAnd ((blockSuf M S).map (fun v => if bit c v then .var (b ++ v) else .not (.var (b ++ v))))

def eqF (b b' : Name) : Formula := bigAnd ((blockSuf M S).map (fun v => Formula.iff (.var (b ++ v)) (.var (b' ++ v))))

def accF (b : Name) : Formula := .var (b ++ [0, 0])

/-- Pairs of distinct positions of a list. -/
def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

def exOneF (vs : List Name) : Formula :=
  .and (bigOr (vs.map .var)) (bigAnd ((pairsOf vs).map (fun p => .not (.and (.var p.1) (.var p.2)))))

/-- The block holds some fitting configuration. -/
def wfF (b : Name) : Formula :=
  bigAnd (exOneF ((sSuf M.nq).map (b ++ ·)) ::
    ((List.range k).map (fun i => exOneF ((List.range S).map (fun j => b ++ [1, i, j])))) ++
    ((List.range k).flatMap (fun i => (List.range S).map (fun j =>
      exOneF ((List.range M.na).map (fun s => b ++ [2, i, j, s]))))))

/-! ### The step formula -/

def readWords : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, na => (List.range na).flatMap (fun s => (readWords n na).map (fun w => s :: w))

/-- All read vectors `Fin k → Nat` with entries below `na`. -/
def allReads (k na : Nat) : List (Fin k → Nat) := (readWords k na).map (fun w => fun i => w.getD i.val 0)

/-- The successor's state, written symbols and moves, as determined by `(q, r)` (halted states stay). -/
def nextState (q : Nat) (r : Fin k → Nat) : Nat := if q ≤ 1 then q else (M.delta q r).1
def writeSym (q : Nat) (r : Fin k → Nat) (i : Fin k) : Nat := if q ≤ 1 then r i else (M.delta q r).2.1 i
def moveOf (q : Nat) (r : Fin k → Nat) (i : Fin k) : Move := if q ≤ 1 then .S else (M.delta q r).2.2 i

def combos : List (Nat × (Fin k → Nat)) := (List.range M.nq).flatMap (fun q => (allReads k M.na).map (fun r => (q, r)))

/-- Tape `i` reads `s` under the head (block `b`). -/
def readF (b : Name) (i : Fin k) (s : Nat) : Formula :=
  bigOr ((List.range S).map (fun j => .and (.var (b ++ [1, i.val, j])) (.var (b ++ [2, i.val, j, s]))))

/-- The block is in state `q` reading `r`. -/
def combF (b : Name) (q : Nat) (r : Fin k → Nat) : Formula :=
  .and (.var (b ++ [0, q])) (bigAnd ((List.finRange k).map (fun i => readF S b i (r i))))

def stateBitsF (b b' : Name) : List Formula :=
  (List.range M.nq).map (fun q' => Formula.iff (.var (b' ++ [0, q']))
    (bigOr (((combos M).filter (fun p => nextState M p.1 p.2 = q')).map (fun p => combF S b p.1 p.2))))

def headBitF (b b' : Name) (i : Fin k) (j : Nat) : Formula :=
  Formula.iff (.var (b' ++ [1, i.val, j]))
    (bigOr ((combos M).map (fun p => .and (combF S b p.1 p.2)
      (bigOr (((List.range S).filter (fun j' => (moveOf M p.1 p.2 i).apply j' = j)).map
        (fun j' => .var (b ++ [1, i.val, j'])))))))

def cellBitF (b b' : Name) (i : Fin k) (j s : Nat) : Formula :=
  Formula.iff (.var (b' ++ [2, i.val, j, s]))
    (.or (.and (.not (.var (b ++ [1, i.val, j]))) (.var (b ++ [2, i.val, j, s])))
      (.and (.var (b ++ [1, i.val, j]))
        (bigOr (((combos M).filter (fun p => writeSym M p.1 p.2 i = s)).map (fun p => combF S b p.1 p.2)))))

/-- The block `b'` holds the successor of the configuration in block `b`. -/
def stepF (b b' : Name) : Formula :=
  bigAnd (stateBitsF M S b b' ++
    (List.finRange k).flatMap (fun i => (List.range S).map (fun j => headBitF M S b b' i j)) ++
    (List.finRange k).flatMap (fun i => (List.range S).flatMap (fun j => (List.range M.na).map (fun s =>
      cellBitF M S b b' i j s))))

end Enc

end Complexity
