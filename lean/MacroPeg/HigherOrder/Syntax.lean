/-!
# Higher-order Macro PEG: syntax and types

First-order Macro PEG passes *parsers* to rules. Higher-order Macro PEG also passes *functions* — rules applied to fewer
arguments than they take, and lambdas that may mention the variables of the enclosing scope (closures). This is the
simply typed λ-calculus over one base type `p` of parsers, with the PEG operators as constants and named, mutually
recursive rules, in the spirit of higher-order recursion schemes.

* Types `Ty`: the base type `p` and arrows. The *order* of a type counts the nesting of arrows to the left: parsers
  have order 0, a first-order rule `p → … → p` has order 1, a rule taking such a rule has order 2.
* Expressions `HExp`: the PEG operators, de Bruijn variables `var i`, rules used as values `rule i`, lambdas and
  (curried) application. Call-by-name: an argument is passed unevaluated, and a parser argument is run wherever the
  body uses it.
* `HasTy R Γ e τ`: `e` has type `τ` in context `Γ` when rule `i` has type `R[i]`.

Compared with `MacroPeg/Syntax.lean` (`MExp`): there a rule's parameter is a de Bruijn index into the current rule's
argument list and a lambda body cannot see the enclosing rule's parameters; here lambdas nest and capture.
-/

namespace Shallot.MacroPeg.HO

inductive Ty where
  /-- Parsers. -/
  | p
  | arr (a b : Ty)
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arr

/-- The order of a type: `p` has order 0, `a ⇒ b` has order `max (order a + 1) (order b)`. -/
def Ty.order : Ty → Nat
  | .p => 0
  | .arr a b => max (a.order + 1) b.order

/-- `p ⇒ … ⇒ p ⇒ p` with `n` arguments: the type of a first-order rule of arity `n`. -/
def Ty.parsers : Nat → Ty
  | 0 => .p
  | n + 1 => .p ⇒ Ty.parsers n

inductive HExp where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (s : List Char)
  | seq (e₁ e₂ : HExp)
  | alt (e₁ e₂ : HExp)
  | star (e : HExp)
  | notP (e : HExp)
  /-- A bound variable (de Bruijn index: `0` is the innermost lambda). -/
  | var (i : Nat)
  /-- Rule `i`, as a value. -/
  | rule (i : Nat)
  | lam (τ : Ty) (body : HExp)
  | app (f a : HExp)
  deriving DecidableEq, Repr

/-- The always-failing parser `!ε`. -/
def HExp.failAlways : HExp := .notP .eps

/-- `f a₁ … aₙ`. -/
def HExp.apps (f : HExp) : List HExp → HExp
  | [] => f
  | a :: as => HExp.apps (.app f a) as

structure HRule where
  ty : Ty
  /-- A closed expression of type `ty`. -/
  body : HExp

structure HGrammar where
  rules : List HRule

def HGrammar.types (g : HGrammar) : List Ty := g.rules.map HRule.ty

/-- The order of a grammar: the largest order of a rule type. -/
def HGrammar.order (g : HGrammar) : Nat := (g.rules.map (fun r => r.ty.order)).foldr max 0

/-! ## Typing -/

inductive HasTy (R : List Ty) : List Ty → HExp → Ty → Prop where
  | eps (Γ : List Ty) : HasTy R Γ .eps .p
  | any (Γ : List Ty) : HasTy R Γ .any .p
  | chr (Γ : List Ty) (c : Char) : HasTy R Γ (.chr c) .p
  | range (Γ : List Ty) (lo hi : Char) : HasTy R Γ (.range lo hi) .p
  | lit (Γ : List Ty) (s : List Char) : HasTy R Γ (.lit s) .p
  | seq {Γ : List Ty} {a b : HExp} : HasTy R Γ a .p → HasTy R Γ b .p → HasTy R Γ (.seq a b) .p
  | alt {Γ : List Ty} {a b : HExp} : HasTy R Γ a .p → HasTy R Γ b .p → HasTy R Γ (.alt a b) .p
  | star {Γ : List Ty} {a : HExp} : HasTy R Γ a .p → HasTy R Γ (.star a) .p
  | notP {Γ : List Ty} {a : HExp} : HasTy R Γ a .p → HasTy R Γ (.notP a) .p
  | var {Γ : List Ty} {i : Nat} {τ : Ty} : Γ[i]? = some τ → HasTy R Γ (.var i) τ
  | rule {Γ : List Ty} {i : Nat} {τ : Ty} : R[i]? = some τ → HasTy R Γ (.rule i) τ
  | lam {Γ : List Ty} {τ σ : Ty} {b : HExp} : HasTy R (τ :: Γ) b σ → HasTy R Γ (.lam τ b) (τ ⇒ σ)
  | app {Γ : List Ty} {τ σ : Ty} {f a : HExp} : HasTy R Γ f (τ ⇒ σ) → HasTy R Γ a τ → HasTy R Γ (.app f a) σ

/-- Every rule body is closed and has the rule's type. -/
def HGrammar.WellTyped (g : HGrammar) : Prop := ∀ r ∈ g.rules, HasTy g.types [] r.body r.ty

end Shallot.MacroPeg.HO
