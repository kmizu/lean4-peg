import Cfg.Semantics
import Cfg.Syntax

/-!
# Greibach's hardest context-free language

Following Nipkow's Isabelle formalization (AFP `Greibach_Hardest`, 2026) of Greibach (SIAM J. Comput. 1973), with
the letters as characters: the brackets `a₁ = '('`, `¦a₁ = ')'`, `a₂ = '['`, `¦a₂ = ']'`, `c = 'c'`,
`¢ = '$'`, and the block separator `d = 'd'`.

- `Dyck`: the balanced words over the two bracket pairs.
- `L0 = {ε} ∪ {x₁ c y₁ c z₁ d … xₙ c yₙ c zₙ d | n ≥ 1, y₁…yₙ ∈ ¢D, xᵢ, zᵢ ∈ T*, yᵢ ∈ brackets* for i ≥ 2}`.
- `invHom h L`: the inverse image of `L` under the homomorphism given by `h` on letters.
- `StdForm g`: Greibach's standard form — every right side is a terminal followed by nonterminals, and the start is
  on no right side.

Greibach's theorem: every context-free language, without `ε`, is `h⁻¹(L0)` without `ε` for a nonerasing `h`.
-/

namespace Shallot.Cfg

/-- The bracket letters. -/
def isBracket (c : Char) : Bool := c == '(' || c == ')' || c == '[' || c == ']'

/-- Greibach's alphabet `T`: the brackets, `c` and `¢` (not the separator `d`). -/
def isT (c : Char) : Bool := isBracket c || c == 'c' || c == '$'

/-- **The balanced words** over `(`,`)` and `[`,`]`. -/
inductive Dyck : List Char → Prop
  | nil : Dyck []
  | append {u v : List Char} : Dyck u → Dyck v → Dyck (u ++ v)
  | paren {u : List Char} : Dyck u → Dyck ('(' :: (u ++ [')']))
  | brack {u : List Char} : Dyck u → Dyck ('[' :: (u ++ [']']))

/-- A block `x c y c z d`. -/
def blk (b : List Char × List Char × List Char) : List Char := b.1 ++ 'c' :: (b.2.1 ++ 'c' :: (b.2.2 ++ ['d']))

/-- **Greibach's hardest context-free language.** -/
def L0 : Language := fun w =>
  w = [] ∨
  ∃ bs : List (List Char × List Char × List Char), bs ≠ [] ∧ w = (bs.map blk).flatten ∧
    (∀ b ∈ bs, (∀ c ∈ b.1, isT c = true) ∧ (∀ c ∈ b.2.2, isT c = true)) ∧
    (∀ b ∈ bs.tail, ∀ c ∈ b.2.1, isBracket c = true) ∧
    ∃ v, Dyck v ∧ (bs.map fun b => b.2.1).flatten = '$' :: v

/-- **The inverse image under a homomorphism**, given by its letters. -/
def invHom (h : Char → List Char) (L : Language) : Language := fun w => L (w.map h).flatten

/-- **Greibach's standard form**: right sides are a terminal followed by nonterminals; the start is on none. -/
def StdForm (g : CFGrammar) : Prop :=
  ∀ alts ∈ g.rules, ∀ rhs ∈ alts, (∃ a rest, rhs = .t a :: rest ∧ ∀ s ∈ rest, ∃ j, s = .nt j) ∧ Sym.nt g.start ∉ rhs

end Shallot.Cfg
