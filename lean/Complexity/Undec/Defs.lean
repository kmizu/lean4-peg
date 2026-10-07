/-!
# String rewriting and correspondence problems over numbers

The chain to Post's correspondence problem follows Forster, Heiter and Smolka (ITP 2018):
a Turing machine's acceptance becomes reachability in a string rewriting system (`SRStar`), that becomes a modified
correspondence problem with a fixed first card (`MPCPSol`), and that becomes the plain one (`PCPNSol`). Strings are
lists of numbers; a card is a pair of strings, its top and its bottom.
-/

namespace Complexity.Undec

/-- A string of symbols. -/
abbrev Word := List Nat

/-- A string rewriting system: rules `l → r`. -/
abbrev SRS := List (Word × Word)

/-- One rewrite: replace an occurrence of the left side of a rule by its right side. -/
inductive SRStep (R : SRS) : Word → Word → Prop
  | rw (u v l r : Word) (h : (l, r) ∈ R) : SRStep R (u ++ l ++ v) (u ++ r ++ v)

/-- Any number of rewrites. -/
inductive SRStar (R : SRS) : Word → Word → Prop
  | refl (x : Word) : SRStar R x x
  | step {x y z : Word} : SRStep R x y → SRStar R y z → SRStar R x z

/-- A card: a top string and a bottom string. -/
abbrev Card := Word × Word

/-- The tops of a list of cards, concatenated. -/
def tops (A : List Card) : Word := (A.map Prod.fst).flatten

/-- The bottoms of a list of cards, concatenated. -/
def bots (A : List Card) : Word := (A.map Prod.snd).flatten

/-- **The modified correspondence problem**: cards of `P` after the first card `d` match. -/
def MPCPSol (d : Card) (P : List Card) : Prop := ∃ A : List Card, (∀ c ∈ A, c ∈ P) ∧ tops (d :: A) = bots (d :: A)

/-- **The correspondence problem over numbers**: a nonempty list of cards of `P` that matches. -/
def PCPNSol (P : List Card) : Prop := ∃ A : List Card, A ≠ [] ∧ (∀ c ∈ A, c ∈ P) ∧ tops A = bots A

/-- All symbols of a list of cards are below `n`. -/
def CardsBelow (n : Nat) (P : List Card) : Prop := ∀ c ∈ P, (∀ a ∈ c.1, a < n) ∧ (∀ a ∈ c.2, a < n)

/-- All symbols of a rewriting system are below `n`. -/
def RulesBelow (n : Nat) (R : SRS) : Prop := ∀ p ∈ R, (∀ a ∈ p.1, a < n) ∧ (∀ a ∈ p.2, a < n)

/-- Every card has a nonempty top and a nonempty bottom. -/
def CardsNonempty (P : List Card) : Prop := ∀ c ∈ P, c.1 ≠ [] ∧ c.2 ≠ []

end Complexity.Undec
