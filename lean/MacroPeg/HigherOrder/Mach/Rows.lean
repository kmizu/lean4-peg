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

end Shallot.MacroPeg.Mach
