import MacroPeg.HigherOrder.Flat.Envs

/-!
# Evaluating a term with numbers

A typed term is written as its items in postfix order (`items`); each item has an operation and the context of its
subterm. Running the items from left to right (`run`, a `foldl`) with a stack of vectors leaves the *vector* of the
term on the stack: its values over all environments of its context, written out (`vec`, `run_items`).

The operations on numbers:

* a leaf, a variable, a rule: a constant vector, or `varVec`;
* a parser operator: position-wise on the rows of the parser values (`seqNum` …);
* a lambda: its body's vector cut into one block per environment, each block a row of the table (`chunksN`);
* an application: entry `y` of row `f` of the table of the function type.
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

/-! ## Items -/

inductive Op where
  /-- `ε`, `.`, a character, a range or a literal. -/
  | leaf (e : HExp)
  | seq
  | alt
  | star
  | notP
  | var (i : Nat)
  | rule (i : Nat)
  /-- A lambda with binder type `a` and body type `σ`. -/
  | lam (a σ : HO.Ty)
  /-- An application of a function of type `a ⇒ b`. -/
  | app (a b : HO.Ty)

structure Item where
  op : Op
  ctx : List HO.Ty

/-- The items of a term, in postfix order. -/
def items {R : List HO.Ty} : {Γ : List HO.Ty} → {τ : HO.Ty} → Tm R Γ τ → List Item
  | Γ, _, .eps => [⟨.leaf .eps, Γ⟩]
  | Γ, _, .any => [⟨.leaf .any, Γ⟩]
  | Γ, _, .chr c => [⟨.leaf (.chr c), Γ⟩]
  | Γ, _, .range lo hi => [⟨.leaf (.range lo hi), Γ⟩]
  | Γ, _, .lit s => [⟨.leaf (.lit s), Γ⟩]
  | Γ, _, .seq a b => items a ++ items b ++ [⟨.seq, Γ⟩]
  | Γ, _, .alt a b => items a ++ items b ++ [⟨.alt, Γ⟩]
  | Γ, _, .star a => items a ++ [⟨.star, Γ⟩]
  | Γ, _, .notP a => items a ++ [⟨.notP, Γ⟩]
  | Γ, _, .var i _ => [⟨.var i, Γ⟩]
  | Γ, _, .rule i _ => [⟨.rule i, Γ⟩]
  | Γ, _, @Tm.lam _ _ a σ body => items body ++ [⟨.lam a σ, Γ⟩]
  | Γ, _, @Tm.app _ _ a b f y => items f ++ items y ++ [⟨.app a b, Γ⟩]

/-! ## Parser operations on codes -/

section Num

variable (x : List Char)

/-- The parser value with codes `c`. -/
def pOf (c : List Nat) : Dom .p := c.map resOf

theorem pOf_flatVal (d : Dom .p) : pOf (flatVal x.length .p d) = d := by
  simp only [pOf, flatVal, List.map_map]
  have e : ∀ l : List Res, l.map (resOf ∘ resCode) = l := fun l => by simp [Function.comp_def, resOf_resCode]
  exact e d

def leafCodes (e : HExp) : List Nat := flatVal x.length .p (baseVec x (leafRes x e))
def seqCodes (ca cb : List Nat) : List Nat := flatVal x.length .p (baseVec x (seqRes (pOf ca) (pOf cb)))
def altCodes (ca cb : List Nat) : List Nat := flatVal x.length .p (baseVec x (altRes (pOf ca) (pOf cb)))
def starCodes (ca : List Nat) : List Nat := flatVal x.length .p (baseVec x (starRes (pOf ca)))
def notCodes (ca : List Nat) : List Nat := flatVal x.length .p (baseVec x (notRes (pOf ca)))

end Num

/-! ## The evaluator -/

section Run

variable (x : List Char) (Tf : List (List Nat))

/-- Block `k` of length `m` of a written-out function. -/
def block (m k : Nat) (fv : List Nat) : List Nat := (fv.drop (k * m)).take m

/-- One item, on a stack of vectors (one written-out value per environment). -/
def step : Item → List (List (List Nat)) → List (List (List Nat))
  | ⟨.leaf e, Γ⟩, st => List.replicate (envSize x.length Γ) (leafCodes x e) :: st
  | ⟨.seq, _⟩, vb :: va :: st => List.zipWith (seqCodes x) va vb :: st
  | ⟨.alt, _⟩, vb :: va :: st => List.zipWith (altCodes x) va vb :: st
  | ⟨.star, _⟩, va :: st => va.map (starCodes x) :: st
  | ⟨.notP, _⟩, va :: st => va.map (notCodes x) :: st
  | ⟨.var i, Γ⟩, st => (varVec x.length Γ i).map (fun k => (eRows x.length (Γ.getD i .p)).getD k []) :: st
  | ⟨.rule i, Γ⟩, st => List.replicate (envSize x.length Γ) (Tf.getD i []) :: st
  | ⟨.lam a _, Γ⟩, vb :: st => (chunksN (elems x.length a).length (envSize x.length Γ) vb).map List.flatten :: st
  | ⟨.app a b, _⟩, vy :: vf :: st =>
      List.zipWith (fun fv yv => block (valSize x.length b) (indexIn yv (eRows x.length a)) fv) vf vy :: st
  | _, st => st

def run (is : List Item) (st : List (List (List Nat))) : List (List (List Nat)) :=
  is.foldl (fun st it => step x Tf it st) st

end Run

/-! ## Correctness -/

section Correct

variable (x : List Char) {R : List HO.Ty} (T : HO.Env R)

/-- The values of `t` over all environments of its context, written out. -/
def vec {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) : List (List Nat) :=
  (envs x.length Γ).map (fun ρ => flatVal x.length τ (den x t T ρ))

theorem zipWith_map_map {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) :
    ∀ l : List α, List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a))
  | [] => rfl
  | _ :: l => by simp [zipWith_map_map f g h l]

theorem run_append (Tf : List (List Nat)) (is js : List Item) (st : List (List (List Nat))) :
    run x Tf (is ++ js) st = run x Tf js (run x Tf is st) := by
  simp [run, List.foldl_append]

theorem run_single (Tf : List (List Nat)) (it : Item) (st : List (List (List Nat))) :
    run x Tf [it] st = step x Tf it st := rfl

variable {x T}

theorem den_mem (hT : Env.Mem x.length T) {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) {ρ : HO.Env Γ}
    (hρ : ρ ∈ envs x.length Γ) : den x t T ρ ∈ elems x.length τ :=
  (den_mono x t hT hT (Env.le_refl T) (envs_mem _ hρ) (envs_mem _ hρ) (Env.le_refl ρ)).1

theorem flatMap_eq_flatten {α β : Type} (f : α → List β) : ∀ l : List α, l.flatMap f = (l.map f).flatten
  | [] => rfl
  | a :: l => by simp [flatMap_eq_flatten f l]

theorem replicate_eq_map {α β : Type} (b : β) (l : List α) : List.replicate l.length b = l.map (fun _ => b) := by
  induction l <;> simp_all [List.replicate_succ]

/-- **The evaluator computes the written-out values of a term**, given those of the rules. -/
theorem run_items (hT : Env.Mem x.length T) {Tf : List (List Nat)}
    (hTf : ∀ (i : Nat) {τ : HO.Ty} (h : R[i]? = some τ), Tf.getD i [] = flatVal x.length τ (Env.get T i h)) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) (st : List (List (List Nat))),
      run x Tf (items t) st = vec x T t :: st := by
  intro Γ τ t
  induction t with
  | eps | any | chr | range | lit =>
    intro st
    simp only [items, run_single, step, vec, den]
    rw [← envs_length, replicate_eq_map]
    rfl
  | seq a b iha ihb | alt a b iha ihb =>
    intro st
    simp only [items]
    rw [run_append, run_append, iha, ihb, run_single]
    simp only [step, vec, zipWith_map_map, seqCodes, altCodes, pOf_flatVal]
    rfl
  | star a ih | notP a ih =>
    intro st
    simp only [items]
    rw [run_append, ih, run_single]
    simp only [step, vec, List.map_map, Function.comp_def, starCodes, notCodes, pOf_flatVal]
    rfl
  | var i h =>
    rename_i Γ' τ'
    intro st
    simp only [items, run_single, step, vec, den]
    rw [varVec_eq _ _ i h, List.map_map]
    have hτ : Γ'.getD i .p = τ' := by rw [List.getD_eq_getElem?_getD, h, Option.getD_some]
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    simp only [Function.comp_apply]
    rw [hτ, eRows_getD (Env.get_mem (envs_mem _ hρ) i h)]
  | rule i h =>
    intro st
    simp only [items, run_single, step, vec, den]
    rw [← envs_length, replicate_eq_map, hTf i h]
  | lam body ih =>
    rename_i Γ a σ
    intro st
    simp only [items]
    rw [run_append, ih, run_single]
    simp only [step, vec, envs, List.map_flatMap, List.map_map]
    have hblocks : (envs x.length Γ).flatMap (fun ρ => (elems x.length a).map
        ((fun ρ' => flatVal x.length σ (den x body T ρ')) ∘ fun d => (d, ρ))) =
        ((envs x.length Γ).map (fun ρ => (elems x.length a).map (fun d => flatVal x.length σ (den x body T (d, ρ))))).flatten := by
      rw [flatMap_eq_flatten]; rfl
    rw [hblocks, ← envs_length, ← List.length_map (f := fun ρ => (elems x.length a).map
      (fun d => flatVal x.length σ (den x body T (d, ρ)))), chunksN_flatten]
    · rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro ρ _
      simp only [Function.comp_apply, den, flatVal, List.flatMap_map]
      rw [flatMap_eq_flatten]
    · intro r hr
      obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 hr
      simp
  | app f y ihf ihy =>
    rename_i Γ a b
    intro st
    simp only [items]
    rw [run_append, run_append, ihf, ihy, run_single]
    simp only [step, vec, zipWith_map_map]
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    have hf := den_mem hT f hρ
    have hy := den_mem hT y hρ
    simp only [block]
    rw [indexIn_eRows hy, ← flatVal_app hf hy]
    rfl

end Correct

end Shallot.MacroPeg.Flat
