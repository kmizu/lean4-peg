import MacroPeg.HigherOrder.Decide

/-!
# Values as numbers

The decision procedure computes with numbers instead of values: a value `d` of type `τ` is its position
`vIdx N τ d` in `elems N τ`. A value is described by its *row*: for a parser, the codes of its results (`resCode`:
`none ↦ 0`, failure `↦ 1`, success leaving `j` symbols `↦ j + 2`); for a function, the numbers of its results.

* `row_inj`: different well-formed values have different rows, so a value is found by searching its row in the table
  `rows N τ` (`indexIn_rows`).
* `vIdx_app`: applying a table is looking up an entry of its row.
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

/-! ## Results as codes -/

def resCode : Res → Nat
  | none => 0
  | some none => 1
  | some (some j) => j + 2

def resOf : Nat → Res
  | 0 => none
  | 1 => some none
  | j + 2 => some (some j)

theorem resOf_resCode : ∀ r : Res, resOf (resCode r) = r
  | none => rfl
  | some none => rfl
  | some (some _) => rfl

/-! ## Positions in a list -/

theorem indexIn_lt {α : Type} [DecidableEq α] (a : α) : ∀ l : List α, a ∈ l → indexIn a l < l.length
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [indexIn, List.length_cons]
    split
    · omega
    · have : a ∈ bs := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm (by assumption)
        · exact e
      have := indexIn_lt a bs this; omega

theorem indexIn_inj {α : Type} [DecidableEq α] {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l)
    (h : indexIn a l = indexIn b l) : a = b := by
  have h₁ := getElem?_indexIn a l ha
  have h₂ := getElem?_indexIn b l hb
  rw [h] at h₁; rw [h₁] at h₂; exact Option.some.inj h₂

/-- An injective map preserves positions. -/
theorem indexIn_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ (l : List α) {a : α}, (∀ x ∈ l, f x = f a → x = a) → indexIn (f a) (l.map f) = indexIn a l
  | [], _, _ => rfl
  | b :: bs, a, h => by
    simp only [List.map_cons, indexIn]
    by_cases hb : b = a
    · subst hb; simp
    · have : f b ≠ f a := fun e => hb (h b List.mem_cons_self e)
      simp only [this, if_false, hb]
      rw [indexIn_map f bs (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Two lists of members of `l` with the same positions are equal. -/
theorem map_indexIn_inj {α : Type} [DecidableEq α] {l : List α} :
    ∀ {u v : List α}, (∀ x ∈ u, x ∈ l) → (∀ x ∈ v, x ∈ l) → u.map (indexIn · l) = v.map (indexIn · l) → u = v
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: u, b :: v, hu, hv, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [indexIn_inj (hu a List.mem_cons_self) (hv b List.mem_cons_self) h.1,
      map_indexIn_inj (fun x hx => hu x (List.mem_cons_of_mem _ hx)) (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h.2]

/-! ## Values, rows and tables -/

/-- The number of a value: its position among the well-formed values. -/
def vIdx (N : Nat) (τ : HO.Ty) (d : Dom τ) : Nat := indexIn d (elems N τ)

/-- The row of a value. -/
def row (N : Nat) : (τ : HO.Ty) → Dom τ → List Nat
  | .p, d => (d : List Res).map resCode
  | .arr _ b, f => (f : List (Dom b)).map (vIdx N b)

/-- The table of type `τ`: the rows of its well-formed values, in order. -/
def rows (N : Nat) (τ : HO.Ty) : List (List Nat) := (elems N τ).map (row N τ)

theorem vIdx_lt {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) : vIdx N τ d < (elems N τ).length :=
  indexIn_lt d _ hd

theorem row_inj {N : Nat} : ∀ (τ : HO.Ty) {d d' : Dom τ}, d ∈ elems N τ → d' ∈ elems N τ → row N τ d = row N τ d' → d = d'
  | .p, d, d', _, _, h => by
    have h' := congrArg (List.map resOf) h
    simp only [row, List.map_map] at h'
    have e : ∀ l : List Res, l.map (resOf ∘ resCode) = l := fun l => by
      simp [Function.comp_def, resOf_resCode]
    rw [e, e] at h'; exact h'
  | .arr a b, f, f', hf, hf', h => by
    have hm := ((mem_allVecs _ _ _).1 (mem_elems_arr.1 hf).1).2
    have hm' := ((mem_allVecs _ _ _).1 (mem_elems_arr.1 hf').1).2
    exact map_indexIn_inj hm hm' h

/-- **A value is found by its row.** -/
theorem indexIn_rows {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) :
    indexIn (row N τ d) (rows N τ) = vIdx N τ d :=
  indexIn_map (row N τ) (elems N τ) (fun _ hx e => row_inj τ hx hd e)

/-- The row with number `i`. -/
theorem rows_getElem? {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) :
    (rows N τ)[vIdx N τ d]? = some (row N τ d) := by
  simp only [rows, List.getElem?_map, vIdx, getElem?_indexIn d _ hd, Option.map_some]

theorem getD_map_lt {α β : Type} (g : α → β) (c : α) (z : β) :
    ∀ (l : List α) {i : Nat}, i < l.length → (l.map g).getD i z = g (l.getD i c)
  | [], _, h => by simp at h
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => getD_map_lt g c z l (by simp at h; omega)

/-- **Application is a lookup**: the number of `f d` is entry `vIdx d` of the row of `f`. -/
theorem vIdx_app {N : Nat} {a b : HO.Ty} {f : Dom (a ⇒ b)} (hf : f ∈ elems N (a ⇒ b)) {d : Dom a}
    (hd : d ∈ elems N a) : vIdx N b (Dom.app (N := N) f d) = (row N (a ⇒ b) f).getD (vIdx N a d) 0 := by
  have hl := ((mem_allVecs _ _ _).1 (mem_elems_arr.1 hf).1).1
  have hlt : vIdx N a d < (f : List (Dom b)).length := by rw [hl]; exact vIdx_lt hd
  show vIdx N b ((f : List (Dom b)).getD (vIdx N a d) (bot N b)) = ((f : List (Dom b)).map (vIdx N b)).getD _ 0
  rw [getD_map_lt (vIdx N b) (bot N b) 0 _ hlt]

end Shallot.MacroPeg.Flat
