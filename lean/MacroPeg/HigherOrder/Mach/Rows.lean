import MacroPeg.HigherOrder.Flat.Decider
import MacroPeg.HigherOrder.Mach.Tables

/-!
# The tables of values, from the arrow table

The well-formed values of a type, written out (`eRows`), computed from type numbers alone:

* the order on values is the same at every type, position by position on the written-out codes: a code `0` (no
  result) is below everything, otherwise equal codes (`leC`, `leB_flat`);
* the rows of `p` are all code lists of length `N + 1` over `0, …, N + 2`; the rows of `a ⇒ b` are the monotone
  tables over the rows of `a` with entries among the rows of `b`, flattened (`rowsNum`, `rowsNum_eq`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- The order on written-out values. -/
def leC (c c' : List Nat) : Bool := pwB (fun r s => r == 0 || r == s) c c'

/-- A table over the rows `A` with entries `F` is monotone. -/
def monoC (A F : List (List Nat)) : Bool :=
  (A.zip F).all (fun p => (A.zip F).all (fun p' => !leC p.1 p'.1 || leC p.2 p'.2))

/-- The rows of the type with number `k`. -/
def rowsNum (N : Nat) (tt : List (Nat × Nat)) (k : Nat) : List (List Nat) :=
  match k with
  | 0 => allVecs (List.range (N + 3)) (N + 1)
  | k + 1 =>
    match tt[k]? with
    | some (a, b) =>
      if a ≤ k ∧ b ≤ k then
        ((allVecs (rowsNum N tt b) (rowsNum N tt a).length).filter (monoC (rowsNum N tt a))).map List.flatten
      else []
    | none => []
termination_by k
decreasing_by all_goals omega

/-! ## Lists of lists -/

theorem allVecs_map {α β : Type} (g : α → β) (xs : List α) :
    ∀ m, allVecs (xs.map g) m = (allVecs xs m).map (List.map g)
  | 0 => rfl
  | m + 1 => by
    simp only [allVecs, List.flatMap_map, allVecs_map g xs m, List.map_map, List.map_flatMap]
    rfl

theorem pwB_map {α β : Type} (f : β → β → Bool) (g : α → β) :
    ∀ l l' : List α, pwB f (l.map g) (l'.map g) = pwB (fun a b => f (g a) (g b)) l l'
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: l' => by simp only [List.map_cons, pwB, pwB_map f g l l']

theorem pwB_flatMap {α : Type} (f : α → α → Bool) (n : Nat) :
    ∀ L L' : List (List α), (∀ c ∈ L, c.length = n) → (∀ c ∈ L', c.length = n) → L.length = L'.length →
      pwB f L.flatten L'.flatten = pwB (pwB f) L L'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: L, c' :: L', hL, hL', h => by
    simp only [List.flatten_cons, pwB]
    rw [← pwB_flatMap f n L L' (fun d hd => hL d (List.mem_cons_of_mem _ hd))
      (fun d hd => hL' d (List.mem_cons_of_mem _ hd)) (by simpa using h)]
    exact pwB_append f c c' _ _ (by rw [hL c List.mem_cons_self, hL' c' List.mem_cons_self])
where
  pwB_append (f : α → α → Bool) : ∀ (c c' l l' : List α), c.length = c'.length →
      pwB f (c ++ l) (c' ++ l') = (pwB f c c' && pwB f l l')
    | [], [], _, _, _ => by simp [pwB]
    | [], _ :: _, _, _, h => by simp at h
    | _ :: _, [], _, _, h => by simp at h
    | a :: c, b :: c', l, l', h => by
      simp only [List.cons_append, pwB, Bool.and_assoc]
      rw [pwB_append f c c' l l' (by simpa using h)]

theorem pwB_congr {α : Type} {f g : α → α → Bool} :
    ∀ (l l' : List α), (∀ a ∈ l, ∀ b ∈ l', f a b = g a b) → pwB f l l' = pwB g l l'
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [pwB]
    rw [h a List.mem_cons_self b List.mem_cons_self,
      pwB_congr l l' (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]

theorem all_congr_mem {α : Type} {P Q : α → Bool} : ∀ (l : List α), (∀ a ∈ l, P a = Q a) → l.all P = l.all Q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, all_congr_mem l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## The order on written-out values -/

theorem resLe_code (r s : Res) : (r == none || r == s) = (resCode r == 0 || resCode r == resCode s) := by
  rcases r with _ | _ | r <;> rcases s with _ | _ | s <;> simp [resCode]

theorem mem_elems_arr' {N : Nat} {a b : HO.Ty} {f : Dom (a ⇒ b)} (hf : f ∈ elems N (a ⇒ b)) :
    (show List (Dom b) from f).length = (elems N a).length ∧ ∀ d ∈ (show List (Dom b) from f), d ∈ elems N b :=
  (mem_allVecs _ _ _).1 (mem_elems_arr.1 hf).1

/-- The order on values is the order on their written-out codes. -/
theorem leB_flat {N : Nat} : ∀ (τ : HO.Ty) (d d' : Dom τ), d ∈ elems N τ → d' ∈ elems N τ →
    Dom.leB τ d d' = leC (flatVal N τ d) (flatVal N τ d')
  | .p, d, d', _, _ => by
    simp only [Dom.leB, leC, flatVal, pwB_map]
    exact pwB_congr _ _ (fun r _ s _ => resLe_code r s)
  | .arr a b, f, f', hf, hf' => by
    obtain ⟨hl, hm⟩ := mem_elems_arr' hf
    obtain ⟨hl', hm'⟩ := mem_elems_arr' hf'
    simp only [Dom.leB, leC, flatVal]
    rw [List.flatMap_def, List.flatMap_def]
    rw [pwB_flatMap _ (valSize N b) _ _ (by simp only [List.mem_map]; rintro c ⟨d, hd, rfl⟩; exact length_flatVal b (hm d hd))
      (by simp only [List.mem_map]; rintro c ⟨d, hd, rfl⟩; exact length_flatVal b (hm' d hd)) (by simp [hl, hl'])]
    rw [pwB_map]
    exact pwB_congr _ _ (fun d hd d' hd' => leB_flat b d d' (hm d hd) (hm' d' hd'))

/-- Monotonicity of a table, on written-out values. -/
theorem monoC_eq {N : Nat} {a b : HO.Ty} (f : List (Dom b)) (hm : ∀ d ∈ f, d ∈ elems N b) :
    tabMonoB (a := a) (b := b) (elems N a) f = monoC (eRows N a) (f.map (flatVal N b)) := by
  unfold tabMonoB monoC eRows
  rw [List.zip_map, List.all_map]
  refine all_congr_mem _ (fun p hp => ?_)
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd]
  rw [List.all_map]
  refine all_congr_mem _ (fun p' hp' => ?_)
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd]
  rw [leB_flat a _ _ (List.of_mem_zip hp).1 (List.of_mem_zip hp').1,
    leB_flat b _ _ (hm _ (List.of_mem_zip hp).2) (hm _ (List.of_mem_zip hp').2)]

theorem resElems_codes (N : Nat) : (resElems N).map resCode = List.range (N + 3) := by
  apply List.ext_getElem
  · simp [resElems]
  · intro i h₁ h₂
    rcases i with _ | _ | i <;> simp [resElems, resCode]

theorem filter_map_congr {α β : Type} (g : α → β) (P : β → Bool) (Q : α → Bool) :
    ∀ (L : List α), (∀ x ∈ L, P (g x) = Q x) → (L.map g).filter P = (L.filter Q).map g
  | [], _ => rfl
  | x :: L, h => by
    simp only [List.map_cons, List.filter_cons]
    rw [h x List.mem_cons_self, filter_map_congr g P Q L (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    split <;> rfl

/-- **The rows of a type number are the rows of the type.** -/
theorem rowsNum_eq (N : Nat) {tt : List (Nat × Nat)} :
    ∀ (k : Nat) {τ : HO.Ty}, tyOf tt k = some τ → rowsNum N tt k = eRows N τ
  | 0, τ, h => by
    rw [tyOf] at h; cases h
    rw [rowsNum, eRows, elems]
    show _ = (allVecs (resElems N) (N + 1)).map (List.map resCode)
    rw [← allVecs_map, resElems_codes]
  | k + 1, τ, h => by
    rw [tyOf] at h
    split at h
    · rename_i a b hk
      split at h
      · rename_i hab
        split at h
        · rename_i σ ρ hσ hρ
          cases h
          rw [rowsNum]; simp only [hk]
          rw [if_pos hab, rowsNum_eq N a hσ, rowsNum_eq N b hρ]
          unfold eRows
          rw [allVecs_map, List.length_map, elems]
          rw [filter_map_congr (List.map (flatVal N ρ)) (monoC ((elems N σ).map (flatVal N σ)))
            (tabMonoB (elems N σ)) _ (fun f hf => (monoC_eq f ((mem_allVecs _ _ _).1 hf).2).symm)]
          simp only [List.map_map, Function.comp_def, flatVal, List.flatMap_def]
          rfl
        · cases h
      · cases h
    · cases h
termination_by k => k
decreasing_by all_goals omega

end Shallot.MacroPeg.Mach
