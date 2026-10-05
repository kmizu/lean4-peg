import MacroPeg.HigherOrder.Mach.Tables

/-!
# Reading and typing an instance in one pass

An abstract machine with explicit stacks reads the token codes left to right, types every subexpression as soon as
it is read, and writes the items of the bodies and the start in postfix order (the specification of the machine
program). The control stack holds what to do next:

* `0`: read an expression; `1`: read a type;
* `2`–`13`: what to do when a subexpression or a component type is finished (`seq`, `alt`, `star`, `!`, a lambda's
  binder type and body, an application's function and argument, an arrow's two sides);
* `14`–`18`: the rule types, the bodies, the start, then the string.

Items are numbers `(tag, a, b, ctx)` (`MItem`); types and contexts are numbers (`Tables.lean`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- An item as numbers: tags `0`–`4` leaves, `5`–`8` the parser operators, `9` a variable, `10` a rule, `11` a lambda
(binder and body types), `12` an application (argument and result types). -/
structure MItem where
  tag : Nat
  a : Nat
  b : Nat
  ctx : Nat
  deriving DecidableEq

structure PSt where
  tk : List Nat
  ctl : List Nat
  ty : List Nat
  /-- The items of the current body, newest first. -/
  out : List MItem
  cur : Nat
  tt : List (Nat × Nat)
  ct : List (Nat × Nat)
  /-- The literals, as character codes. -/
  lt : List (List Nat)
  /-- The rule types. -/
  rt : List Nat
  bodies : List (List MItem)
  start : List MItem
  x : List Nat
  ok : Bool

/-- Stop, rejecting. -/
def PSt.fail (s : PSt) : PSt := { s with ctl := [], ok := false }

/-- Emit an item and push its type. -/
def PSt.leaf (s : PSt) (it : MItem) (τ : Nat) (tk : List Nat) (K : List Nat) : PSt :=
  { s with tk := tk, ctl := K, ty := τ :: s.ty, out := it :: s.out }

/-- The `i`-th variable's type in context `c`. -/
def varTy (ct : List (Nat × Nat)) : Nat → Nat → Option Nat
  | 0, _ => none
  | c + 1, 0 => (ct[c]?).map Prod.snd
  | c + 1, i + 1 =>
    match ct[c]? with
    | some (par, _) => if par ≤ c then varTy ct par i else none
    | none => none
termination_by c => c
decreasing_by omega

/-- Read an expression. -/
def readExpr (s : PSt) (K : List Nat) : PSt :=
  match s.tk with
  | 0 :: r => s.leaf ⟨0, 0, 0, s.cur⟩ 0 r K
  | 1 :: r => s.leaf ⟨1, 0, 0, s.cur⟩ 0 r K
  | 2 :: r =>
    match parseChar r with
    | some (c, r₁) => s.leaf ⟨2, c.toNat, 0, s.cur⟩ 0 r₁ K
    | none => s.fail
  | 3 :: r =>
    match parseChar r with
    | some (lo, r₁) =>
      match parseChar r₁ with
      | some (hi, r₂) => s.leaf ⟨3, lo.toNat, hi.toNat, s.cur⟩ 0 r₂ K
      | none => s.fail
    | none => s.fail
  | 4 :: r =>
    match parseStr r.length r with
    | some (str, r₁) => { s.leaf ⟨4, s.lt.length, 0, s.cur⟩ 0 r₁ K with lt := s.lt ++ [str.map Char.toNat] }
    | none => s.fail
  | 5 :: r => { s with tk := r, ctl := 0 :: 2 :: K }
  | 6 :: r => { s with tk := r, ctl := 0 :: 4 :: K }
  | 7 :: r => { s with tk := r, ctl := 0 :: 6 :: K }
  | 8 :: r => { s with tk := r, ctl := 0 :: 7 :: K }
  | 9 :: r =>
    match parseNat r with
    | some (i, r₁) =>
      match varTy s.ct s.cur i with
      | some τ => s.leaf ⟨9, i, 0, s.cur⟩ τ r₁ K
      | none => s.fail
    | none => s.fail
  | 10 :: r =>
    match parseNat r with
    | some (i, r₁) =>
      match s.rt[i]? with
      | some τ => s.leaf ⟨10, i, 0, s.cur⟩ τ r₁ K
      | none => s.fail
    | none => s.fail
  | 11 :: r => { s with tk := r, ctl := 1 :: 8 :: K }
  | 12 :: r => { s with tk := r, ctl := 0 :: 10 :: K }
  | _ => s.fail

/-- Read a type. -/
def readType (s : PSt) (K : List Nat) : PSt :=
  match s.tk with
  | 0 :: r => { s with tk := r, ctl := K, ty := 0 :: s.ty }
  | 1 :: r => { s with tk := r, ctl := 1 :: 12 :: K }
  | _ => s.fail

/-- A finished parser operand of a binary operator: check it, then emit the operator. -/
def binDone (s : PSt) (tag : Nat) (K : List Nat) : PSt :=
  match s.ty with
  | 0 :: 0 :: r => { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out }
  | _ => s.fail

def unDone (s : PSt) (tag : Nat) (K : List Nat) : PSt :=
  match s.ty with
  | 0 :: r => { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out }
  | _ => s.fail

/-- One step. -/
def pstep (s : PSt) : PSt :=
  match s.ctl with
  | [] => s
  | 0 :: K => readExpr s K
  | 1 :: K => readType s K
  -- `seq`/`alt`: after the first operand (a parser), read the second
  | 2 :: K => match s.ty with | 0 :: _ => { s with ctl := 0 :: 3 :: K } | _ => s.fail
  | 3 :: K => binDone s 5 K
  | 4 :: K => match s.ty with | 0 :: _ => { s with ctl := 0 :: 5 :: K } | _ => s.fail
  | 5 :: K => binDone s 6 K
  | 6 :: K => unDone s 7 K
  | 7 :: K => unDone s 8 K
  -- a lambda: after its binder type, enter the extended context and read the body
  | 8 :: K =>
    match s.ty with
    | a :: r =>
      { s with
        ctl := 0 :: 9 :: a :: s.cur :: K
        ty := r
        ct := s.ct ++ [(s.cur, a)]
        cur := s.ct.length + 1 }
    | [] => s.fail
  | 9 :: a :: c :: K =>
    match s.ty with
    | σ :: r =>
      { s with
        ctl := K
        ty := (intern s.tt a σ).2 :: r
        tt := (intern s.tt a σ).1
        cur := c
        out := ⟨11, a, σ, c⟩ :: s.out }
    | [] => s.fail
  -- an application: after the function, read the argument; then check the argument type
  | 10 :: K => { s with ctl := 0 :: 11 :: K }
  | 11 :: K =>
    match s.ty with
    | α :: φ :: r =>
      match φ with
      | k + 1 =>
        match s.tt[k]? with
        | some (α', β) =>
          if α' = α then { s with ctl := K, ty := β :: r, out := ⟨12, α, β, s.cur⟩ :: s.out } else s.fail
        | none => s.fail
      | 0 => s.fail
    | _ => s.fail
  -- an arrow type: after its left side, read its right side; then register it
  | 12 :: K => { s with ctl := 1 :: 13 :: K }
  | 13 :: K =>
    match s.ty with
    | b :: a :: r => { s with ctl := K, ty := (intern s.tt a b).2 :: r, tt := (intern s.tt a b).1 }
    | _ => s.fail
  -- the rule types
  | 14 :: K =>
    match s.tk with
    | 0 :: r => { s with tk := r, ctl := 16 :: K }
    | 1 :: r => { s with tk := r, ctl := 1 :: 15 :: K }
    | _ => s.fail
  | 15 :: K =>
    match s.ty with
    | t :: r => { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] }
    | [] => s.fail
  -- the bodies, each in the empty context
  | 16 :: K =>
    match s.tk with
    | 0 :: r => if s.bodies.length = s.rt.length then { s with tk := r, ctl := 0 :: 18 :: K, cur := 0 } else s.fail
    | 1 :: r => { s with tk := r, ctl := 0 :: 17 :: K, cur := 0 }
    | _ => s.fail
  | 17 :: K =>
    match s.ty with
    | σ :: r =>
      if s.rt[s.bodies.length]? = some σ then
        { s with
          ctl := 16 :: K
          ty := r
          bodies := s.bodies ++ [s.out.reverse]
          out := [] }
      else s.fail
    | [] => s.fail
  -- the start (a parser), then the string, then nothing
  | 18 :: K =>
    match s.ty with
    | 0 :: r =>
      match parseStr s.tk.length s.tk with
      | some (x, []) =>
        { s with
          ctl := K
          ty := r
          start := s.out.reverse
          out := []
          x := x.map Char.toNat }
      | _ => s.fail
    | _ => s.fail
  | _ => s.fail

/-- The machine at the start. -/
def pinit (tk : List Nat) : PSt :=
  ⟨tk, [14], [], [], 0, [], [], [], [], [], [], [], true⟩

/-- Steps of the machine. -/
def pruns (s : PSt) : Nat → PSt
  | 0 => s
  | n + 1 => pruns (pstep s) n

end Shallot.MacroPeg.Mach
