import Complexity.Prog

/-!
# List machines

A layer above structured tape programs: each tape holds a list of naturals (a stack whose top is the last element).
Tape `i` represents the list `l` as: cell `0` holds the marker `3`, cell `j + 1` holds `l[j] + 4`, everything after is
blank, and the head is at cell `0` (`TapeRep`, `Rep`).

Instructions: `push i e` (append the constant `e`), `pop i` (drop the last element), `copy i j` (append the last element
of list `i` to list `j`), and control (`seq`, `ite`, `loop`, `halt`) branching on the *last symbol* of one list
(`lastSym`: `3` if empty, `e + 4` if the last element is `e`).

This file holds the tape programs implementing the instructions (`pushP`, `popP`, `copyP`, `goEnd`, `goHome`,
`goLast`) and the list-level syntax and semantics.
-/

namespace Complexity

variable {k : Nat}

/-! ## Representation -/

/-- `f` holds the list `l` after the marker at cell `0`. -/
def TapeRep (l : List Nat) (f : Nat → Nat) : Prop :=
  f 0 = 3 ∧ (∀ j (h : j < l.length), f (j + 1) = l[j] + 4) ∧ ∀ j, l.length < j → f j = 0

abbrev Lists (k : Nat) := Fin k → List Nat

def Lists.set (L : Lists k) (i : Fin k) (l : List Nat) : Lists k := fun j => if j = i then l else L j

/-- All heads at the marker, every tape represents its list. -/
def Rep (L : Lists k) (τ : Tapes k) : Prop := ∀ i, τ.pos i = 0 ∧ TapeRep (L i) (τ.cells i)

/-- The symbol under the head of tape `i` when the head is on the last element (or on the marker if empty). -/
def lastSym (l : List Nat) : Nat :=
  match l.getLast? with
  | none => 3
  | some e => e + 4

/-- Lengths are small enough that every program point fits in `B` cells. -/
def LenOK (B : Nat) (L : Lists k) : Prop := ∀ i, (L i).length + 2 ≤ B

/-! ## Tape programs -/

def Tapes.setPos (τ : Tapes k) (i : Fin k) (p : Nat) : Tapes k := ⟨fun j => if j = i then p else τ.pos j, τ.cells⟩

def mvAct (i : Fin k) (m : Move) : Action k := fun r => (r, fun j => if j = i then m else .S)

def mv (i : Fin k) (m : Move) : Prog k := .act (mvAct i m)

/-- Move head `i` right to the first blank. -/
def goEnd (i : Fin k) : Prog k := .loop (fun r => r i != 0) (mv i .R)

/-- Move head `i` left to the marker. -/
def goHome (i : Fin k) : Prog k := .loop (fun r => r i != 3) (mv i .L)

/-- Move head `i` to the last element (to the marker if the list is empty). -/
def goLast (i : Fin k) : Prog k := .seq (goEnd i) (mv i .L)

def pushP (i : Fin k) (e : Nat) : Prog k :=
  .seq (goEnd i) (.seq (.act (fun r => (fun j => if j = i then e + 4 else r j, fun _ => .S))) (goHome i))

def popP (i : Fin k) : Prog k :=
  .seq (goLast i) (.seq (.act (fun r => (fun j => if j = i ∧ r i ≠ 3 then 0 else r j, fun _ => .S))) (goHome i))

def copyP (i j : Fin k) : Prog k :=
  .seq (goEnd j) (.seq (goLast i)
    (.seq (.act (fun r => (fun x => if x = j ∧ r i ≠ 3 then r i else r x, fun _ => .S))) (.seq (goHome i) (goHome j))))

/-! ## List programs -/

inductive LProg (k : Nat) where
  | push (i : Fin k) (e : Nat)
  | pop (i : Fin k)
  | copy (i j : Fin k)
  | seq (p q : LProg k)
  | ite (i : Fin k) (c : Nat → Bool) (p q : LProg k)
  | loop (i : Fin k) (c : Nat → Bool) (p : LProg k)
  | halt (accept : Bool)

inductive LOutcome (k : Nat) where
  | cont (L : Lists k)
  | stop (accept : Bool) (L : Lists k)

/-- Big-step semantics; `t` counts instructions and tests; every visited state satisfies `Q`. -/
inductive LExec (Q : Lists k → Prop) : LProg k → Lists k → Nat → LOutcome k → Prop
  | push {i : Fin k} {e : Nat} {L : Lists k} : Q L → Q (L.set i (L i ++ [e])) →
      LExec Q (.push i e) L 1 (.cont (L.set i (L i ++ [e])))
  | pop {i : Fin k} {L : Lists k} : Q L → Q (L.set i (L i).dropLast) →
      LExec Q (.pop i) L 1 (.cont (L.set i (L i).dropLast))
  | copy {i j : Fin k} {L : Lists k} : i ≠ j → Q L → Q (L.set j (L j ++ (L i).getLast?.toList)) →
      LExec Q (.copy i j) L 1 (.cont (L.set j (L j ++ (L i).getLast?.toList)))
  | halt {b : Bool} {L : Lists k} : Q L → LExec Q (.halt b) L 1 (.stop b L)
  | seqC {p q : LProg k} {L L₁ : Lists k} {t₁ t₂ : Nat} {o : LOutcome k} :
      LExec Q p L t₁ (.cont L₁) → LExec Q q L₁ t₂ o → LExec Q (.seq p q) L (t₁ + t₂) o
  | seqS {p q : LProg k} {L L₁ : Lists k} {t₁ : Nat} {b : Bool} :
      LExec Q p L t₁ (.stop b L₁) → LExec Q (.seq p q) L t₁ (.stop b L₁)
  | iteT {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k} :
      Q L → c (lastSym (L i)) = true → LExec Q p L t o → LExec Q (.ite i c p q) L (t + 1) o
  | iteF {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k} :
      Q L → c (lastSym (L i)) = false → LExec Q q L t o → LExec Q (.ite i c p q) L (t + 1) o
  | loopF {i : Fin k} {c : Nat → Bool} {p : LProg k} {L : Lists k} :
      Q L → c (lastSym (L i)) = false → LExec Q (.loop i c p) L 1 (.cont L)
  | loopC {i : Fin k} {c : Nat → Bool} {p : LProg k} {L L₁ : Lists k} {t₁ t₂ : Nat} {o : LOutcome k} :
      Q L → c (lastSym (L i)) = true → LExec Q p L t₁ (.cont L₁) → LExec Q (.loop i c p) L₁ t₂ o →
      LExec Q (.loop i c p) L (t₁ + 1 + t₂) o
  | loopS {i : Fin k} {c : Nat → Bool} {p : LProg k} {L L₁ : Lists k} {t₁ : Nat} {b : Bool} :
      Q L → c (lastSym (L i)) = true → LExec Q p L t₁ (.stop b L₁) → LExec Q (.loop i c p) L (t₁ + 1) (.stop b L₁)

def LProg.compile : LProg k → Prog k
  | .push i e => pushP i e
  | .pop i => popP i
  | .copy i j => copyP i j
  | .seq p q => .seq p.compile q.compile
  | .ite i c p q => .seq (goLast i) (.ite (fun r => c (r i)) (.seq (goHome i) p.compile) (.seq (goHome i) q.compile))
  | .loop i c p =>
    .seq (goLast i) (.seq (.loop (fun r => c (r i)) (.seq (goHome i) (.seq p.compile (goLast i)))) (goHome i))
  | .halt b => .halt b

end Complexity
