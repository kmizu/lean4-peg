import Complexity.LProgs

/-!
# Stack machines over natural numbers

A list program can only push constants, so numbers live in unary. `NProg K` hides this: its `K` stacks hold arbitrary
natural numbers, with primitives on the tops (`NPrim`: push `0`, `+1`, `−1`, pop, copy the top onto another stack)
and tests "empty" / "top is `0`" (`NTest`). Every primitive is total: on an empty stack it does nothing.

`NProg.compile` translates to a list program over `K + 1` lists (the last one is scratch, kept empty): the number `v`
is written `2 1ᵛ` (`encN`), a stack is the concatenation of its numbers (`encS`). The translation is verified once
(`NStackSpec.lean`), so programs on numbers only need reasoning about lists of numbers.
-/

namespace Complexity

variable {K : Nat}

/-! ## Syntax and semantics -/

inductive NTest where
  /-- The stack is empty. -/
  | empty
  /-- The top is `0` (false on an empty stack). -/
  | zero
  /-- The stack is not empty. -/
  | nonempty
  /-- The top is positive (false on an empty stack). -/
  | pos

def NTest.eval : NTest → List Nat → Bool
  | .empty, l => l.isEmpty
  | .zero, l => l.getLast? == some 0
  | .nonempty, l => !l.isEmpty
  | .pos, l => match l.getLast? with | some (_ + 1) => true | _ => false

inductive NPrim (K : Nat) where
  | pushZ (i : Fin K)
  | inc (i : Fin K)
  | dec (i : Fin K)
  | pop (i : Fin K)
  /-- Push a copy of the top of `i` onto `j`. -/
  | dup (i j : Fin K) (h : i ≠ j)

/-- The top changed by `f` (nothing on an empty stack). -/
def mapTop (f : Nat → Nat) (l : List Nat) : List Nat := l.dropLast ++ (l.getLast?.map f).toList

def NPrim.apply : NPrim K → Lists K → Lists K
  | .pushZ i, S => S.set i (S i ++ [0])
  | .inc i, S => S.set i (mapTop (· + 1) (S i))
  | .dec i, S => S.set i (mapTop (· - 1) (S i))
  | .pop i, S => S.set i (S i).dropLast
  | .dup i j _, S => S.set j (S j ++ (S i).getLast?.toList)

inductive NProg (K : Nat) where
  | prim (a : NPrim K)
  | seq (p q : NProg K)
  | ite (i : Fin K) (c : NTest) (p q : NProg K)
  | loop (i : Fin K) (c : NTest) (p : NProg K)
  | halt (accept : Bool)

/-- Big-step semantics with step counts; every visited state satisfies `Q`. -/
inductive NExec (Q : Lists K → Prop) : NProg K → Lists K → Nat → LOutcome K → Prop
  | prim {a : NPrim K} {S : Lists K} : Q S → Q (a.apply S) → NExec Q (.prim a) S 1 (.cont (a.apply S))
  | halt {b : Bool} {S : Lists K} : Q S → NExec Q (.halt b) S 1 (.stop b S)
  | seqC {p q : NProg K} {S S₁ : Lists K} {t₁ t₂ : Nat} {o : LOutcome K} :
      NExec Q p S t₁ (.cont S₁) → NExec Q q S₁ t₂ o → NExec Q (.seq p q) S (t₁ + t₂) o
  | seqS {p q : NProg K} {S S₁ : Lists K} {t₁ : Nat} {b : Bool} :
      NExec Q p S t₁ (.stop b S₁) → NExec Q (.seq p q) S t₁ (.stop b S₁)
  | iteT {i : Fin K} {c : NTest} {p q : NProg K} {S : Lists K} {t : Nat} {o : LOutcome K} :
      Q S → c.eval (S i) = true → NExec Q p S t o → NExec Q (.ite i c p q) S (t + 1) o
  | iteF {i : Fin K} {c : NTest} {p q : NProg K} {S : Lists K} {t : Nat} {o : LOutcome K} :
      Q S → c.eval (S i) = false → NExec Q q S t o → NExec Q (.ite i c p q) S (t + 1) o
  | loopF {i : Fin K} {c : NTest} {p : NProg K} {S : Lists K} :
      Q S → c.eval (S i) = false → NExec Q (.loop i c p) S 1 (.cont S)
  | loopC {i : Fin K} {c : NTest} {p : NProg K} {S S₁ : Lists K} {t₁ t₂ : Nat} {o : LOutcome K} :
      Q S → c.eval (S i) = true → NExec Q p S t₁ (.cont S₁) → NExec Q (.loop i c p) S₁ t₂ o →
      NExec Q (.loop i c p) S (t₁ + 1 + t₂) o
  | loopS {i : Fin K} {c : NTest} {p : NProg K} {S S₁ : Lists K} {t₁ : Nat} {b : Bool} :
      Q S → c.eval (S i) = true → NExec Q p S t₁ (.stop b S₁) → NExec Q (.loop i c p) S (t₁ + 1) (.stop b S₁)

/-! ## Translation to list programs -/

/-- The number `v` in unary: the mark `2`, then `v` ones. -/
def encN (v : Nat) : List Nat := 2 :: List.replicate v 1

/-- A stack of numbers. -/
def encS (l : List Nat) : List Nat := l.flatMap encN

/-- Stack `i` of the list program. -/
def lift (i : Fin K) : Fin (K + 1) := i.castSucc

/-- The scratch list. -/
def scratch (K : Nat) : Fin (K + 1) := Fin.last K

/-- The lists of the translated program: the encoded stacks, then the empty scratch list. -/
def encL (S : Lists K) : Lists (K + 1) := fun i => if h : i.val < K then encS (S ⟨i.val, h⟩) else []

def encO : LOutcome K → LOutcome (K + 1)
  | .cont S => .cont (encL S)
  | .stop b S => .stop b (encL S)

/-- The test on the last symbol (`3`: empty, `5`: a one, `6`: a mark). -/
def NTest.sym : NTest → Nat → Bool
  | .empty, s => s == 3
  | .zero, s => s == 6
  | .nonempty, s => s != 3
  | .pos, s => s == 5

/-- Move the ones on top of `i` to the scratch list. -/
def onesOut (i : Fin (K + 1)) : LProg (K + 1) := .loop i (· == 5) (moveTop i (scratch K))

/-- Move the ones of the scratch list back onto `i`, and copy them onto `j`. -/
def onesBack (i j : Fin (K + 1)) : LProg (K + 1) :=
  .loop (scratch K) (· == 5) (.seq (.copy (scratch K) i) (.seq (.copy (scratch K) j) (.pop (scratch K))))

def NPrim.compile : NPrim K → LProg (K + 1)
  | .pushZ i => .push (lift i) 2
  | .inc i => .ite (lift i) (· == 3) (skipP (lift i)) (.push (lift i) 1)
  | .dec i => .ite (lift i) (· == 5) (.pop (lift i)) (skipP (lift i))
  | .pop i => .seq (.loop (lift i) (· == 5) (.pop (lift i)))
      (.ite (lift i) (· == 3) (skipP (lift i)) (.pop (lift i)))
  | .dup i j _ => .ite (lift i) (· == 3) (skipP (lift i))
      (.seq (onesOut (lift i)) (.seq (.push (lift j) 2) (onesBack (lift i) (lift j))))

def NProg.compile : NProg K → LProg (K + 1)
  | .prim a => a.compile
  | .seq p q => .seq p.compile q.compile
  | .ite i c p q => .ite (lift i) c.sym p.compile q.compile
  | .loop i c p => .loop (lift i) c.sym p.compile
  | .halt b => .halt b

/-- Every encoded stack and the scratch list fit in `B`. -/
def NFits (B : Nat) (S : Lists K) : Prop := 2 ≤ B ∧ ∀ i, (encS (S i)).length + 2 ≤ B

/-- The list-program steps per stack-machine step. -/
def ncost (B : Nat) : Nat := 8 * B + 16

end Complexity
