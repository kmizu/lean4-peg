import MacroPeg.HigherOrder.Flat.Envs

/-!
# Evaluating a term with numbers

A typed term is written as its items in prefix order (`items`); each item has an operation and the context of its
subterm. Running the items from right to left (`run`, a `foldr`) with a stack of vectors leaves the *vector* of the
term on the stack: the numbers of its values over all environments of its context (`vec`, `run_items`).

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

/-- The items of a term, in prefix order. -/
def items {R : List HO.Ty} : {Γ : List HO.Ty} → {τ : HO.Ty} → Tm R Γ τ → List Item
  | Γ, _, .eps => [⟨.leaf .eps, Γ⟩]
  | Γ, _, .any => [⟨.leaf .any, Γ⟩]
  | Γ, _, .chr c => [⟨.leaf (.chr c), Γ⟩]
  | Γ, _, .range lo hi => [⟨.leaf (.range lo hi), Γ⟩]
  | Γ, _, .lit s => [⟨.leaf (.lit s), Γ⟩]
  | Γ, _, .seq a b => ⟨.seq, Γ⟩ :: (items a ++ items b)
  | Γ, _, .alt a b => ⟨.alt, Γ⟩ :: (items a ++ items b)
  | Γ, _, .star a => ⟨.star, Γ⟩ :: items a
  | Γ, _, .notP a => ⟨.notP, Γ⟩ :: items a
  | Γ, _, .var i _ => [⟨.var i, Γ⟩]
  | Γ, _, .rule i _ => [⟨.rule i, Γ⟩]
  | Γ, _, @Tm.lam _ _ a σ body => ⟨.lam a σ, Γ⟩ :: items body
  | Γ, _, @Tm.app _ _ a b f y => ⟨.app a b, Γ⟩ :: (items f ++ items y)

/-! ## Parser operations on numbers -/

section Num

variable (x : List Char)

/-- The parser value with number `i`. -/
def pVal (i : Nat) : Dom .p := ((rows x.length .p).getD i []).map resOf

/-- The number of a parser value. -/
def pNum (d : Dom .p) : Nat := indexIn (row x.length .p d) (rows x.length .p)

def leafNum (e : HExp) : Nat := pNum x (baseVec x (leafRes x e))
def seqNum (i j : Nat) : Nat := pNum x (baseVec x (seqRes (pVal x i) (pVal x j)))
def altNum (i j : Nat) : Nat := pNum x (baseVec x (altRes (pVal x i) (pVal x j)))
def starNum (i : Nat) : Nat := pNum x (baseVec x (starRes (pVal x i)))
def notNum (i : Nat) : Nat := pNum x (baseVec x (notRes (pVal x i)))

theorem pVal_vIdx {d : Dom .p} (hd : d ∈ elems x.length .p) : pVal x (vIdx x.length .p d) = d := by
  simp only [pVal, List.getD_eq_getElem?_getD, rows_getElem? hd, Option.getD_some, row, List.map_map]
  have e : ∀ l : List Res, l.map (resOf ∘ resCode) = l := fun l => by simp [Function.comp_def, resOf_resCode]
  exact e d

theorem pNum_eq {d : Dom .p} (hd : d ∈ elems x.length .p) : pNum x d = vIdx x.length .p d := indexIn_rows hd

end Num

/-! ## The evaluator -/

section Run

variable (x : List Char) (Tn : List Nat)

/-- One item, on a stack of vectors. -/
def step : Item → List (List Nat) → List (List Nat)
  | ⟨.leaf e, Γ⟩, st => List.replicate (envSize x.length Γ) (leafNum x e) :: st
  | ⟨.seq, _⟩, va :: vb :: st => List.zipWith (seqNum x) va vb :: st
  | ⟨.alt, _⟩, va :: vb :: st => List.zipWith (altNum x) va vb :: st
  | ⟨.star, _⟩, va :: st => va.map (starNum x) :: st
  | ⟨.notP, _⟩, va :: st => va.map (notNum x) :: st
  | ⟨.var i, Γ⟩, st => varVec x.length Γ i :: st
  | ⟨.rule i, Γ⟩, st => List.replicate (envSize x.length Γ) (Tn.getD i 0) :: st
  | ⟨.lam a σ, Γ⟩, vb :: st =>
      (chunksN (elems x.length a).length (envSize x.length Γ) vb).map (indexIn · (rows x.length (a ⇒ σ))) :: st
  | ⟨.app a b, _⟩, vf :: vy :: st =>
      List.zipWith (fun i j => ((rows x.length (a ⇒ b)).getD i []).getD j 0) vf vy :: st
  | _, st => st

def run (is : List Item) (st : List (List Nat)) : List (List Nat) := is.foldr (step x Tn) st

end Run

/-! ## Correctness -/

section Correct

variable (x : List Char) {R : List HO.Ty} (T : HO.Env R)

/-- The numbers of the values of `t` over all environments of its context. -/
def vec {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) : List Nat :=
  (envs x.length Γ).map (fun ρ => vIdx x.length τ (den x t T ρ))

theorem zipWith_map_map {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) :
    ∀ l : List α, List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a))
  | [] => rfl
  | _ :: l => by simp [zipWith_map_map f g h l]

theorem run_append (Tn : List Nat) (is js : List Item) (st : List (List Nat)) :
    run x Tn (is ++ js) st = run x Tn is (run x Tn js st) := by
  simp [run, List.foldr_append]

variable {x T}

theorem den_mem (hT : Env.Mem x.length T) {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) {ρ : HO.Env Γ}
    (hρ : ρ ∈ envs x.length Γ) : den x t T ρ ∈ elems x.length τ :=
  (den_mono x t hT hT (Env.le_refl T) (envs_mem _ hρ) (envs_mem _ hρ) (Env.le_refl ρ)).1

theorem flatMap_eq_flatten {α β : Type} (f : α → List β) : ∀ l : List α, l.flatMap f = (l.map f).flatten
  | [] => rfl
  | a :: l => by simp [flatMap_eq_flatten f l]

theorem replicate_eq_map {α β : Type} (b : β) (l : List α) : List.replicate l.length b = l.map (fun _ => b) := by
  induction l <;> simp_all [List.replicate_succ]

/-- **The evaluator computes the vector of a term**, given the numbers of the rule values. -/
theorem run_items (hT : Env.Mem x.length T) {Tn : List Nat}
    (hTn : ∀ (i : Nat) {τ : HO.Ty} (h : R[i]? = some τ), Tn.getD i 0 = vIdx x.length τ (Env.get T i h)) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) (st : List (List Nat)), run x Tn (items t) st = vec x T t :: st := by
  intro Γ τ t
  induction t with
  | eps | any | chr | range | lit =>
    intro st
    simp only [items, run, List.foldr_cons, List.foldr_nil, step, vec, den]
    rw [← envs_length, replicate_eq_map]
    congr 1
    apply List.map_congr_left
    intro ρ _
    exact pNum_eq x (baseVec_mem (fun _ _ => leafRes_mem _))
  | seq a b iha ihb | alt a b iha ihb =>
    intro st
    simp only [items]
    rw [run, List.foldr_cons, ← run, run_append, ihb, iha]
    simp only [step, vec, zipWith_map_map]
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    simp only [seqNum, altNum, pVal_vIdx x (den_mem hT _ hρ)]
    first
      | exact pNum_eq x (den_mem hT (.seq a b) hρ)
      | exact pNum_eq x (den_mem hT (.alt a b) hρ)
  | star a ih | notP a ih =>
    intro st
    simp only [items]
    rw [run, List.foldr_cons, ← run, ih]
    simp only [step, vec, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    simp only [Function.comp_apply, starNum, notNum, pVal_vIdx x (den_mem hT _ hρ)]
    first
      | exact pNum_eq x (den_mem hT (.star a) hρ)
      | exact pNum_eq x (den_mem hT (.notP a) hρ)
  | var i h =>
    intro st
    simp only [items, run, List.foldr_cons, List.foldr_nil, step, vec, den]
    rw [varVec_eq _ _ i h]
  | rule i h =>
    intro st
    simp only [items, run, List.foldr_cons, List.foldr_nil, step, vec, den]
    rw [← envs_length, replicate_eq_map, hTn i h]
  | lam body ih =>
    rename_i Γ a σ
    intro st
    simp only [items]
    rw [run, List.foldr_cons, ← run, ih]
    simp only [step, vec, envs, List.map_flatMap, List.map_map]
    have hblocks : (envs x.length Γ).flatMap (fun ρ => (elems x.length a).map
        ((fun ρ' => vIdx x.length σ (den x body T ρ')) ∘ fun d => (d, ρ))) =
        ((envs x.length Γ).map (fun ρ => row x.length (a ⇒ σ) (den x (.lam body) T ρ))).flatten := by
      rw [flatMap_eq_flatten]
      congr 1
      apply List.map_congr_left
      intro ρ _
      simp [row, den, Function.comp_def]
    rw [hblocks, ← envs_length, ← List.length_map (f := fun ρ => row x.length (a ⇒ σ) (den x (.lam body) T ρ)),
      chunksN_flatten]
    · rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro ρ hρ
      exact indexIn_rows (den_mem hT _ hρ)
    · intro r hr
      obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 hr
      simp [row, den]
  | app f y ihf ihy =>
    rename_i Γ a b
    intro st
    simp only [items]
    rw [run, List.foldr_cons, ← run, run_append, ihy, ihf]
    simp only [step, vec, zipWith_map_map]
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    have hf := den_mem hT f hρ
    have hy := den_mem hT y hρ
    have hr : (rows x.length (a ⇒ b)).getD (vIdx x.length (a ⇒ b) (den x f T ρ)) [] =
        row x.length (a ⇒ b) (den x f T ρ) := by
      rw [List.getD_eq_getElem?_getD, rows_getElem? hf, Option.getD_some]
    rw [hr, ← vIdx_app hf hy]
    rfl

end Correct

end Shallot.MacroPeg.Flat
