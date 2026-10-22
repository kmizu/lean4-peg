import Shallot.Peg.Dpda.Run

/-!
# The PEG of a DPDA (after Birman–Ullman 1973, Theorem 2.2)

Two families of nonterminals, for states `q, r < nQ` and stack symbols `Z < nG`:

* `P q Z r` (*pop*): consumes exactly what the automaton reads from `(q, Z)` until `Z` is popped, and succeeds iff the
  state is then `r`. This is Birman–Ullman's `[qZr]`.
* `A q Z` (*accept*): succeeds iff the automaton, started on the stack `[Z]`, reaches a final state with the input used
  up while `Z` or its descendants are still being processed (or at the moment the stack becomes empty).

A move that pushes `γ = X₁ … Xₖ` is a sequence over the pushed symbols; the state in which `Xᵢ` is popped is found by
an ordered choice over all states. Determinism makes at most one choice succeed. No normalization of the automaton is
needed: the grammar may loop where the automaton does, and `isPEL_iff_isTotalPEL` removes such inputs afterwards.
-/

namespace Shallot.Dpda

/-- A rule that always fails: the empty range. -/
def failE : PExp := .range '\u0001' '\u0000'

/-- End of input `!.`. -/
def eofE : PExp := .notP .any

/-- Ordered choice over a list; the empty choice fails. -/
def altList : List PExp → PExp
  | [] => failE
  | e :: es => .alt e (altList es)

namespace DPDA

variable (M : DPDA)

/-- `PS p γ r`: pop all of `γ` (top first) starting in state `p`, ending in state `r`. -/
def popS (r : Nat) (pidx : Nat → Nat → Nat → Nat) : Nat → List Nat → PExp
  | p, [] => if p = r then .eps else failE
  | p, X :: γ => altList ((List.range M.nQ).map fun q₁ => .seq (.nt (pidx p X q₁)) (popS r pidx q₁ γ))

/-- `AS p γ`: reach acceptance while processing the stack `γ` (top first), starting in state `p`. -/
def accS (pidx : Nat → Nat → Nat → Nat) (aidx : Nat → Nat → Nat) : Nat → List Nat → PExp
  | p, [] => if M.final p then eofE else failE
  | p, X :: γ =>
    .alt (.nt (aidx p X))
      (altList ((List.range M.nQ).map fun q₁ => .seq (.nt (pidx p X q₁)) (accS pidx aidx q₁ γ)))

/-- The alternative for reading the letter `a` in `(q, Z)`. -/
def moveAlt (cont : Nat → List Nat → PExp) (q Z : Nat) (a : Char) : PExp :=
  match M.δ q (some a) Z with
  | some (p, γ) => .seq (.chr a) (cont p γ)
  | none => failE

/-- The moves from `(q, Z)`: the ε-move if there is one, otherwise a choice over the letters. -/
def moves (cont : Nat → List Nat → PExp) (q Z : Nat) : PExp :=
  match M.δ q none Z with
  | some (p, γ) => cont p γ
  | none => altList (M.alpha.map (M.moveAlt cont q Z))

/-- Index of `P q Z r`. -/
def pidx (q Z r : Nat) : Nat := M.nQ * (q * M.nG + Z) + r

/-- Index of `A q Z`. -/
def aidx (q Z : Nat) : Nat := M.nQ * M.nG * M.nQ + (q * M.nG + Z)

def popRule (q Z r : Nat) : PExp := M.moves (fun p γ => M.popS r M.pidx p γ) q Z

def accRule (q Z : Nat) : PExp :=
  .alt (if M.final q then eofE else failE) (M.moves (fun p γ => M.accS M.pidx M.aidx p γ) q Z)

/-- The rule at index `i`. -/
def ruleOf (i : Nat) : PExp :=
  if i < M.nQ * M.nG * M.nQ then
    M.popRule ((i / M.nQ) / M.nG) ((i / M.nQ) % M.nG) (i % M.nQ)
  else
    M.accRule ((i - M.nQ * M.nG * M.nQ) / M.nG) ((i - M.nQ * M.nG * M.nQ) % M.nG)

/-- The grammar; its start rule is `A q₀ Z₀`. -/
def grammar : Grammar where
  rules := (List.range (M.nQ * M.nG * M.nQ + M.nQ * M.nG)).map M.ruleOf
  start := M.aidx M.q0 M.Z0

end DPDA

end Shallot.Dpda
