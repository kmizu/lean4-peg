import MacroPeg.Properties.MExpEq
import MacroPeg.Properties.FiniteArgs
import MacroPeg.Properties.ArgEquiv

/-!
# Defunctionalizing the callable-value slice (M-PEG-4)

The slice lets a rule receive a lambda `.lam a b` and invoke it (`.callParam k args`). Lambdas have no free variables
(`MExp.subst` treats `.lam` as a leaf), so every lambda a run ever meets is one written in the grammar or the start
expression: a finite list `Λ`. This file turns such a grammar into a first-order one.

* A *tag* says what an actual argument is: `0` = not a lambda, `ℓ + 1` = the lambda `Λ[ℓ]`. The tag of an argument is
  known statically from the tags of the enclosing activation (`tagOf`).
* A *unit* is something with a body to run: a rule `u < |rules|`, or the lambda `Λ[u - |rules|]`.
* The first-order grammar has one rule per *spec* `(u, v)`: unit `u` specialized to a tag vector `v`. Its body is
  `tr Λ v body` — the body translated with the parameters' tags known: invoking a parameter tagged `ℓ + 1` becomes a
  call of the spec of the lambda `Λ[ℓ]`; a lambda (or `dbg`) evaluated as a parser becomes `ε`, which matches it
  (both are a zero-width success).

The key fact is that translation commutes with substitution (`tr_subst`): translating the substituted body equals
substituting the translated arguments into the translated body. `DefunCorrect.lean` uses it to show that the runs agree.
-/

namespace Shallot.MacroPeg

/-! ## Collecting the lambdas -/

mutual
  /-- Every lambda `(arity, body)` occurring in `e`, including inside lambda bodies and `invoke`s. -/
  def MExp.lams : MExp → List (Nat × MExp)
    | .lam a b => (a, b) :: MExp.lams b
    | .invoke a b args => (a, b) :: MExp.lams b ++ MExp.lamsArgs args
    | .call _ args | .callParam _ args => MExp.lamsArgs args
    | .seq e₁ e₂ | .alt e₁ e₂ => MExp.lams e₁ ++ MExp.lams e₂
    | .star e | .notP e | .dbg e => MExp.lams e
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => []

  def MExp.lamsArgs : List MExp → List (Nat × MExp)
    | [] => []
    | e :: es => MExp.lams e ++ MExp.lamsArgs es
end

/-- The lambdas of a grammar together with a start expression. -/
def lamsOf (g : MGrammar) (e : MExp) : List (Nat × MExp) := g.rules.flatMap (fun r => r.body.lams) ++ e.lams

/-! ## Tags -/

/-- The tag of an actual argument `a`, given the tags `v` of the enclosing activation's parameters. -/
def tagOf (Λ : List (Nat × MExp)) (v : List Nat) : MExp → Nat
  | .param j => v.getD j 0
  | .lam a b => if (a, b) ∈ Λ then indexIn (a, b) Λ + 1 else 0
  | _ => 0

def tagsOf (Λ : List (Nat × MExp)) (v : List Nat) (args : List MExp) : List Nat := args.map (tagOf Λ v)

/-! ## Units and specs -/

/-- What a unit runs: rule `u`, or the lambda `Λ[u - |rules|]`. -/
def unitRule (g : MGrammar) (Λ : List (Nat × MExp)) (u : Nat) : MRule :=
  if u < g.rules.length then g.rules.getD u ⟨0, MExp.failAlways⟩
  else match Λ[u - g.rules.length]? with
    | some (a, b) => ⟨a, b⟩
    | none => ⟨0, MExp.failAlways⟩

/-- All specs `(u, v)`: every unit with every tag vector of its arity. -/
def specsOf (g : MGrammar) (Λ : List (Nat × MExp)) : List (Nat × List Nat) :=
  (List.range (g.rules.length + Λ.length)).flatMap
    (fun u => (vecs (Λ.length + 1) (unitRule g Λ u).arity).map (fun v => (u, v)))

/-- The index of the first-order rule for spec `(u, v)`. -/
def specCode (g : MGrammar) (Λ : List (Nat × MExp)) (u : Nat) (v : List Nat) : Nat :=
  indexIn (u, v) (specsOf g Λ)

/-! ## The translation -/

section Translate

variable (g : MGrammar) (Λ : List (Nat × MExp))

/-- A call of unit `u` with the actual arguments `args` (translated to `targs`) of an activation with tags `v`; fails
like the source when the arity is wrong. -/
def callUnit (v : List Nat) (u : Nat) (args targs : List MExp) : MExp :=
  if (unitRule g Λ u).arity = args.length then .call (specCode g Λ u (tagsOf Λ v args)) targs else MExp.failAlways

mutual
  /-- Translate `e`, a body whose parameters have the tags `v`. -/
  def tr (v : List Nat) : MExp → MExp
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit s => .lit s
    | .param k => .param k
    | .lam _ _ => .eps
    | .dbg _ => .eps
    | .seq e₁ e₂ => .seq (tr v e₁) (tr v e₂)
    | .alt e₁ e₂ => .alt (tr v e₁) (tr v e₂)
    | .star e => .star (tr v e)
    | .notP e => .notP (tr v e)
    | .call i args =>
      if i < g.rules.length then callUnit g Λ v i args (trArgs v args) else MExp.failAlways
    | .callParam k args =>
      match v.getD k 0 with
      | 0 => MExp.failAlways
      | ℓ + 1 => callUnit g Λ v (g.rules.length + ℓ) args (trArgs v args)
    | .invoke a b args =>
      if (a, b) ∈ Λ then callUnit g Λ v (g.rules.length + indexIn (a, b) Λ) args (trArgs v args)
      else MExp.failAlways

  def trArgs (v : List Nat) : List MExp → List MExp
    | [] => []
    | e :: es => tr v e :: trArgs v es
end

/-- The first-order grammar: one rule per spec. -/
def defunGrammar : MGrammar :=
  ⟨(specsOf g Λ).map (fun (u, v) => ⟨(unitRule g Λ u).arity, tr g Λ v (unitRule g Λ u).body⟩)⟩

end Translate

/-- Defunctionalize a grammar and a start expression together. -/
def defun (g : MGrammar) (e : MExp) : MGrammar × MExp :=
  (defunGrammar g (lamsOf g e), tr g (lamsOf g e) [] e)

end Shallot.MacroPeg
