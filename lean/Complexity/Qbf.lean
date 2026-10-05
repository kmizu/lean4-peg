import Complexity.TM

/-!
# Quantified Boolean formulas and the language TQBF

A formula is in prenex form: a quantifier prefix followed by a Boolean circuit (the matrix). Variables and gates are
named by tuples of naturals (`Name := List Nat`), which keeps the formulas built in the hardness proof free of index
arithmetic. A gate refers to variables and to gates defined before it; an undefined reference reads `false`. The value
of the matrix is the value of its last gate.

Encoding: a formula is a list of 4-bit tokens. `decode` is total — every bit string denotes some formula (trailing bits
that do not fill a token are ignored, unexpected tokens are skipped) — and `decode (encode φ) = φ`. `TQBF` is the set of
bit strings whose decoding is true.
-/

namespace Complexity

abbrev Name := List Nat

inductive Op where
  | var (x : Name)
  | tt
  | ff
  | not (g : Name)
  | and (g h : Name)
  | or (g h : Name)
  deriving DecidableEq, Repr

structure Gate where
  out : Name
  op : Op
  deriving DecidableEq, Repr

structure Qbf where
  /-- `(true, x)` is `∀x`, `(false, x)` is `∃x`, outermost first. -/
  quants : List (Bool × Name)
  gates : List Gate
  deriving DecidableEq, Repr

/-! ## Semantics -/

def lookup (σ : List (Name × Bool)) (x : Name) : Bool :=
  match σ.find? (fun p => p.1 == x) with
  | some p => p.2
  | none => false

def Op.eval (ρ : List (Name × Bool)) (vals : List (Name × Bool)) : Op → Bool
  | .var x => lookup ρ x
  | .tt => true
  | .ff => false
  | .not g => !lookup vals g
  | .and g h => lookup vals g && lookup vals h
  | .or g h => lookup vals g || lookup vals h

/-- Evaluate the gates in order; `vals` holds the values so far (newest first). The result is the last gate's value. -/
def evalGates (ρ : List (Name × Bool)) : List Gate → List (Name × Bool) → Bool → Bool
  | [], _, last => last
  | g :: gs, vals, _ =>
    let v := g.op.eval ρ vals
    evalGates ρ gs ((g.out, v) :: vals) v

def matrixValue (gates : List Gate) (ρ : List (Name × Bool)) : Bool := evalGates ρ gates [] false

/-- The value under the assignment `ρ` of the variables bound so far (newest first). -/
def qEval (gates : List Gate) : List (Bool × Name) → List (Name × Bool) → Bool
  | [], ρ => matrixValue gates ρ
  | (true, x) :: pre, ρ => qEval gates pre ((x, true) :: ρ) && qEval gates pre ((x, false) :: ρ)
  | (false, x) :: pre, ρ => qEval gates pre ((x, true) :: ρ) || qEval gates pre ((x, false) :: ρ)

def Qbf.value (φ : Qbf) : Bool := qEval φ.gates φ.quants []

/-! ## Tokens and bits -/

namespace Tok
def one : Nat := 1
def sep : Nat := 2
def fin : Nat := 3
def all : Nat := 4
def ex : Nat := 5
def gate : Nat := 6
def var : Nat := 7
def tt : Nat := 8
def ff : Nat := 9
def neg : Nat := 10
def conj : Nat := 11
def disj : Nat := 12
end Tok

def encName (x : Name) : List Nat := x.flatMap (fun n => List.replicate n Tok.one ++ [Tok.sep]) ++ [Tok.fin]

def Op.enc : Op → List Nat
  | .var x => Tok.var :: encName x
  | .tt => [Tok.tt]
  | .ff => [Tok.ff]
  | .not g => Tok.neg :: encName g
  | .and g h => Tok.conj :: encName g ++ encName h
  | .or g h => Tok.disj :: encName g ++ encName h

def Gate.enc (g : Gate) : List Nat := Tok.gate :: encName g.out ++ g.op.enc

def Qbf.toks (φ : Qbf) : List Nat :=
  φ.quants.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2) ++ φ.gates.flatMap Gate.enc

/-- A token as 4 bits, most significant first. -/
def tokBits (t : Nat) : List Bool := [t / 8 % 2 == 1, t / 4 % 2 == 1, t / 2 % 2 == 1, t % 2 == 1]

def bitsTok (b₃ b₂ b₁ b₀ : Bool) : Nat :=
  (if b₃ then 8 else 0) + (if b₂ then 4 else 0) + (if b₁ then 2 else 0) + (if b₀ then 1 else 0)

def toBits (ts : List Nat) : List Bool := ts.flatMap tokBits

def ofBits : List Bool → List Nat
  | b₃ :: b₂ :: b₁ :: b₀ :: bs => bitsTok b₃ b₂ b₁ b₀ :: ofBits bs
  | _ => []

def Qbf.encode (φ : Qbf) : List Bool := toBits φ.toks

/-! ## Total decoding -/

/-- Read `one*` and return the count and the rest. -/
def countOnes : List Nat → Nat × List Nat
  | t :: ts => if t = Tok.one then ((countOnes ts).1 + 1, (countOnes ts).2) else (0, t :: ts)
  | [] => (0, [])

/-- Read a name: components `one^n sep`, ended by `fin`. Anything else ends the name early (and is not consumed). -/
def parseName : Nat → List Nat → Name × List Nat
  | 0, ts => ([], ts)
  | fuel + 1, ts =>
    let (n, rest) := countOnes ts
    match rest with
    | t :: rest' =>
      if t = Tok.sep then
        let (x, r) := parseName fuel rest'
        (n :: x, r)
      else if t = Tok.fin then ([], rest')
      else ([], rest)
    | [] => ([], [])

def parseOp (fuel : Nat) : List Nat → Option (Op × List Nat)
  | t :: ts =>
    if t = Tok.var then let (x, r) := parseName fuel ts; some (.var x, r)
    else if t = Tok.tt then some (.tt, ts)
    else if t = Tok.ff then some (.ff, ts)
    else if t = Tok.neg then let (g, r) := parseName fuel ts; some (.not g, r)
    else if t = Tok.conj then
      let (g, r) := parseName fuel ts
      let (h, r') := parseName fuel r
      some (.and g h, r')
    else if t = Tok.disj then
      let (g, r) := parseName fuel ts
      let (h, r') := parseName fuel r
      some (.or g h, r')
    else none
  | [] => none

/-- Decode a token list (with fuel for termination; `ts.length + 1` suffices). Prefix items and gates are collected in
order; an unexpected token is skipped. -/
def decodeToks : Nat → List Nat → Qbf
  | 0, _ => ⟨[], []⟩
  | _ + 1, [] => ⟨[], []⟩
  | fuel + 1, t :: ts =>
    if t = Tok.all ∨ t = Tok.ex then
      let (x, r) := parseName ts.length ts
      let φ := decodeToks fuel r
      ⟨(t = Tok.all, x) :: φ.quants, φ.gates⟩
    else if t = Tok.gate then
      let (g, r) := parseName ts.length ts
      match parseOp r.length r with
      | some (op, r') =>
        let φ := decodeToks fuel r'
        ⟨φ.quants, ⟨g, op⟩ :: φ.gates⟩
      | none => decodeToks fuel r
    else decodeToks fuel ts

def Qbf.decode (s : List Bool) : Qbf := decodeToks ((ofBits s).length + 1) (ofBits s)

/-- TQBF: the bit strings that decode to true formulas. -/
def TQBF : Lang := fun s => (Qbf.decode s).value = true

end Complexity
