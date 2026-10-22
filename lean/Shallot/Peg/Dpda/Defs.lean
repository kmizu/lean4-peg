import Shallot.Peg.Semantics

/-!
# Deterministic pushdown automata

States and stack symbols are natural numbers below `nQ` and `nG`; the input symbols are the characters of the
finite list `alpha`. A move `δ q a Z = some (p, γ)` reads `a` (`none` is an ε-move), pops the top `Z`, pushes `γ`
(its head on top) and goes to `p`. Determinism (Birman–Ullman 1973, §2): when an ε-move is defined, no reading move
is.

`run n c` is the configuration after `n` moves (`none` once the automaton is stuck). A word is accepted by final
state: the automaton reads all of it and reaches a final state (`language`). The automaton may get stuck or loop;
nothing is assumed about reading the whole input.
-/

namespace Shallot.Dpda

/-- A deterministic pushdown automaton. -/
structure DPDA where
  nQ : Nat
  nG : Nat
  alpha : List Char
  δ : Nat → Option Char → Nat → Option (Nat × List Nat)
  q0 : Nat
  Z0 : Nat
  final : Nat → Bool
  q0_lt : q0 < nQ
  Z0_lt : Z0 < nG
  /-- Moves exist only for states below `nQ` and stack symbols below `nG`. -/
  dom : ∀ q a Z r, δ q a Z = some r → q < nQ ∧ Z < nG
  /-- Moves stay within the bounds. -/
  cod : ∀ q a Z p γ, δ q a Z = some (p, γ) → p < nQ ∧ ∀ X ∈ γ, X < nG
  /-- Reading moves read letters of the alphabet. -/
  read : ∀ q a Z r, δ q (some a) Z = some r → a ∈ alpha
  /-- Determinism: an ε-move excludes reading moves. -/
  det : ∀ q Z r, δ q none Z = some r → ∀ a, δ q (some a) Z = none

/-- A configuration: state, remaining input, stack (top first). -/
abbrev Config := Nat × List Char × List Nat

namespace DPDA

variable (M : DPDA)

/-- One move. -/
def step : Config → Option Config
  | (_, _, []) => none
  | (q, x, Z :: β) =>
    match M.δ q none Z with
    | some (p, γ) => some (p, x, γ ++ β)
    | none =>
      match x with
      | [] => none
      | a :: x' =>
        match M.δ q (some a) Z with
        | some (p, γ) => some (p, x', γ ++ β)
        | none => none

/-- The configuration after `n` moves. -/
def run : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
    match M.step c with
    | some c' => run n c'
    | none => none

/-- **The language accepted by final state**: read the whole input and reach a final state. -/
def language : List Char → Prop := fun w =>
  ∃ n f β, M.run n (M.q0, w, [M.Z0]) = some (f, [], β) ∧ M.final f = true

end DPDA

end Shallot.Dpda
