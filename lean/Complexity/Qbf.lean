import Complexity.TM

/-!
# Quantified Boolean formulas and the language TQBF

A formula is in prenex form: a quantifier prefix followed by a matrix written in reverse Polish notation (RPN).
Variables are named by tuples of naturals (`Name := List Nat`), which keeps the formulas built in the hardness proof
free of index arithmetic. The matrix is evaluated with a stack of Booleans; a missing operand reads `false`, and the
value is the top of the stack at the end (`false` if empty), so every token list has a value.

Encoding: a formula is a list of 4-bit tokens. `decode` is total — every bit string denotes some formula (trailing bits
that do not fill a token are ignored, unexpected tokens are skipped) — and `decode (encode φ) = φ`. `TQBF` is the set of
bit strings whose decoding is true.
-/

namespace Complexity

abbrev Name := List Nat

/-- Matrix tokens. -/
inductive RTok where
  | var (x : Name)
  | tt
  | ff
  | neg
  | conj
  | disj
  deriving DecidableEq, Repr

structure Qbf where
  /-- `(true, x)` is `∀x`, `(false, x)` is `∃x`, outermost first. -/
  quants : List (Bool × Name)
  matrix : List RTok
  deriving DecidableEq, Repr

/-! ## Semantics -/

def lookup (σ : List (Name × Bool)) (x : Name) : Bool :=
  match σ.find? (fun p => p.1 == x) with
  | some p => p.2
  | none => false

/-- Run RPN tokens on a stack (top first). -/
def evalRPN (σ : List (Name × Bool)) : List RTok → List Bool → List Bool
  | [], st => st
  | .var x :: ts, st => evalRPN σ ts (lookup σ x :: st)
  | .tt :: ts, st => evalRPN σ ts (true :: st)
  | .ff :: ts, st => evalRPN σ ts (false :: st)
  | .neg :: ts, st => evalRPN σ ts ((!st.headD false) :: st.tail)
  | .conj :: ts, st => evalRPN σ ts ((st.tail.headD false && st.headD false) :: st.tail.tail)
  | .disj :: ts, st => evalRPN σ ts ((st.tail.headD false || st.headD false) :: st.tail.tail)

def matrixValue (m : List RTok) (σ : List (Name × Bool)) : Bool := (evalRPN σ m []).headD false

/-- The value under the assignment `σ` of the variables bound so far (newest first). -/
def qEval (m : List RTok) : List (Bool × Name) → List (Name × Bool) → Bool
  | [], σ => matrixValue m σ
  | (true, x) :: pre, σ => qEval m pre ((x, true) :: σ) && qEval m pre ((x, false) :: σ)
  | (false, x) :: pre, σ => qEval m pre ((x, true) :: σ) || qEval m pre ((x, false) :: σ)

def Qbf.value (φ : Qbf) : Bool := qEval φ.matrix φ.quants []

/-! ## Tokens and bits -/

namespace Tok
def one : Nat := 1
def sep : Nat := 2
def fin : Nat := 3
def all : Nat := 4
def ex : Nat := 5
def var : Nat := 6
def tt : Nat := 7
def ff : Nat := 8
def neg : Nat := 9
def conj : Nat := 10
def disj : Nat := 11
end Tok

def encName (x : Name) : List Nat := x.flatMap (fun n => List.replicate n Tok.one ++ [Tok.sep]) ++ [Tok.fin]

def RTok.enc : RTok → List Nat
  | .var x => Tok.var :: encName x
  | .tt => [Tok.tt]
  | .ff => [Tok.ff]
  | .neg => [Tok.neg]
  | .conj => [Tok.conj]
  | .disj => [Tok.disj]

def Qbf.toks (φ : Qbf) : List Nat :=
  φ.quants.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2) ++ φ.matrix.flatMap RTok.enc

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

/-- Decode a token list (with fuel for termination; `ts.length + 1` suffices). Quantifiers and matrix tokens are
collected in order; an unexpected token is skipped. -/
def decodeToks : Nat → List Nat → Qbf
  | 0, _ => ⟨[], []⟩
  | _ + 1, [] => ⟨[], []⟩
  | fuel + 1, t :: ts =>
    if t = Tok.all ∨ t = Tok.ex then
      let (x, r) := parseName ts.length ts
      let φ := decodeToks fuel r
      ⟨(t = Tok.all, x) :: φ.quants, φ.matrix⟩
    else if t = Tok.var then
      let (x, r) := parseName ts.length ts
      let φ := decodeToks fuel r
      ⟨φ.quants, .var x :: φ.matrix⟩
    else
      let φ := decodeToks fuel ts
      if t = Tok.tt then ⟨φ.quants, .tt :: φ.matrix⟩
      else if t = Tok.ff then ⟨φ.quants, .ff :: φ.matrix⟩
      else if t = Tok.neg then ⟨φ.quants, .neg :: φ.matrix⟩
      else if t = Tok.conj then ⟨φ.quants, .conj :: φ.matrix⟩
      else if t = Tok.disj then ⟨φ.quants, .disj :: φ.matrix⟩
      else φ

def Qbf.decode (s : List Bool) : Qbf := decodeToks ((ofBits s).length + 1) (ofBits s)

/-- TQBF: the bit strings that decode to true formulas. -/
def TQBF : Lang := fun s => (Qbf.decode s).value = true

end Complexity
