import Shallot.Peg.Semantics

/-!
# The packrat table, filled by iteration

For a grammar `g` and an input `x`, the table holds, for an expression `e` and a position `i`, the result of `e` on
the suffix `x.drop i`: failure (`some none`), success eating `k` characters (`some (some k)`), or nothing yet
(`none`). One round `F` fills an entry from the entries it depends on; the table is filled by iterating `F` from the
empty table (`iter`).

Entries of judgments without derivations stay empty forever — a left-recursive rule, or a repetition of an
expression that succeeds without eating, depends on itself — so the iteration needs no well-formedness. The entries
that matter are those of the subterms of the start and the rules (`dom`) at the positions `0 … |x|`; there are
`(dom g).length * (|x| + 1)` of them, and `bound g x` rounds fill every entry that will ever be filled.
-/

namespace Shallot.Packrat

/-- A result: failure (`none`) or success eating some characters. -/
abbrev Res := Option Nat

/-- A partial table. -/
abbrev Tbl := PExp → Nat → Option Res

/-- **One round of filling.** -/
def F (g : Grammar) (x : List Char) (T : Tbl) : Tbl := fun e i =>
  match e with
  | .eps => some (some 0)
  | .any => some (if i < x.length then some 1 else none)
  | .chr c => some (match x[i]? with
    | some d => if beqChar c d then some 1 else none
    | none => none)
  | .range lo hi => some (match x[i]? with
    | some d => if (leChar lo d && leChar d hi) then some 1 else none
    | none => none)
  | .lit s => some (match stripPrefix? s (x.drop i) with
    | some _ => some s.length
    | none => none)
  | .nt j => match ruleAt g.rules j with
    | none => some none
    | some b => T b i
  | .seq a b => match T a i with
    | none => none
    | some none => some none
    | some (some k) => match T b (i + k) with
      | none => none
      | some none => some none
      | some (some m) => some (some (k + m))
  | .alt a b => match T a i with
    | none => none
    | some (some k) => some (some k)
    | some none => T b i
  | .star a => match T a i with
    | none => none
    | some none => some (some 0)
    | some (some k) => match T (.star a) (i + k) with
      | some (some m) => some (some (k + m))
      | _ => none
  | .notP a => match T a i with
    | none => none
    | some none => some (some 0)
    | some (some _) => some none

/-- The table after `k` rounds. -/
def iter (g : Grammar) (x : List Char) : Nat → Tbl
  | 0 => fun _ _ => none
  | k + 1 => F g x (iter g x k)

/-- The subterms of an expression, itself first. -/
def subterms : PExp → List PExp
  | .seq a b => .seq a b :: (subterms a ++ subterms b)
  | .alt a b => .alt a b :: (subterms a ++ subterms b)
  | .star a => .star a :: subterms a
  | .notP a => .notP a :: subterms a
  | e => [e]

/-- The expressions whose entries matter: the subterms of the start and of the rules. -/
def dom (g : Grammar) : List PExp := ((PExp.nt g.start) :: g.rules).flatMap subterms

/-- Enough rounds to fill every entry that will ever be filled. -/
def bound (g : Grammar) (x : List Char) : Nat := (dom g).length * (x.length + 1) + 1

end Shallot.Packrat
