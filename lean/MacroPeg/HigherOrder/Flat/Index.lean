import MacroPeg.HigherOrder.Decide
import MacroPeg.HigherOrder.Cost

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

/-! ## Values as flat lists of codes -/

/-- The number of a value: its position among the well-formed values (used for argument and binder types, whose
values are enumerated). -/
def vIdx (N : Nat) (τ : HO.Ty) (d : Dom τ) : Nat := indexIn d (elems N τ)

/-- A value written out: a parser as the codes of its results, a function as its entries one after another. -/
def flatVal (N : Nat) : (τ : HO.Ty) → Dom τ → List Nat
  | .p, d => (d : List Res).map resCode
  | .arr _ b, f => (f : List (Dom b)).flatMap (flatVal N b)

/-- The table of type `τ`: its well-formed values written out, in order. -/
def eRows (N : Nat) (τ : HO.Ty) : List (List Nat) := (elems N τ).map (flatVal N τ)

theorem vIdx_lt {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) : vIdx N τ d < (elems N τ).length :=
  indexIn_lt d _ hd

theorem length_flatMap_eq {α : Type} (f : α → List Nat) (k : Nat) :
    ∀ l : List α, (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      length_flatMap_eq f k l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp [Nat.succ_mul, Nat.add_comm]

theorem mem_elems_arr_entries {N : Nat} {a b : HO.Ty} {f : Dom (a ⇒ b)} (hf : f ∈ elems N (a ⇒ b)) :
    (show List (Dom b) from f).length = (elems N a).length ∧ ∀ d ∈ (show List (Dom b) from f), d ∈ elems N b :=
  (mem_allVecs _ _ _).1 (mem_elems_arr.1 hf).1

/-- Written-out values have the length `valSize`. -/
theorem length_flatVal {N : Nat} : ∀ (τ : HO.Ty) {d : Dom τ}, d ∈ elems N τ → (flatVal N τ d).length = valSize N τ
  | .p, d, hd => by simp [flatVal, valSize, ((mem_allVecs _ _ _).1 hd).1]
  | .arr a b, f, hf => by
    have ⟨hl, hm⟩ := mem_elems_arr_entries hf
    simp only [flatVal, valSize]
    rw [length_flatMap_eq _ (valSize N b) _ (fun d hd => length_flatVal b (hm d hd)), hl]

/-- Different well-formed values are written out differently. -/
theorem flatVal_inj {N : Nat} : ∀ (τ : HO.Ty) {d d' : Dom τ}, d ∈ elems N τ → d' ∈ elems N τ →
    flatVal N τ d = flatVal N τ d' → d = d'
  | .p, d, d', _, _, h => by
    have h' := congrArg (List.map resOf) h
    simp only [flatVal, List.map_map] at h'
    have e : ∀ l : List Res, l.map (resOf ∘ resCode) = l := fun l => by
      simp [Function.comp_def, resOf_resCode]
    rw [e, e] at h'; exact h'
  | .arr a b, f, f', hf, hf', h => by
    have ⟨hl, hm⟩ := mem_elems_arr_entries hf
    have ⟨hl', hm'⟩ := mem_elems_arr_entries hf'
    have key : ∀ (u v : List (Dom b)), (∀ x ∈ u, x ∈ elems N b) → (∀ x ∈ v, x ∈ elems N b) →
        u.length = v.length → u.flatMap (flatVal N b) = v.flatMap (flatVal N b) → u = v := by
      intro u
      induction u with
      | nil => intro v _ _ hl _; cases v; rfl; simp at hl
      | cons x u ih =>
        intro v hu hv hl he
        cases v with
        | nil => simp at hl
        | cons y v =>
          simp only [List.flatMap_cons] at he
          have hx := length_flatVal b (hu x List.mem_cons_self)
          have hy := length_flatVal b (hv y List.mem_cons_self)
          have e₁ : flatVal N b x = flatVal N b y := by
            have := congrArg (List.take (valSize N b)) he
            rwa [List.take_left' hx, List.take_left' hy] at this
          have e₂ : u.flatMap (flatVal N b) = v.flatMap (flatVal N b) := by
            have := congrArg (List.drop (valSize N b)) he
            rwa [List.drop_left' hx, List.drop_left' hy] at this
          rw [flatVal_inj b (hu x List.mem_cons_self) (hv y List.mem_cons_self) e₁,
            ih v (fun z hz => hu z (List.mem_cons_of_mem _ hz)) (fun z hz => hv z (List.mem_cons_of_mem _ hz))
              (by simpa using hl) e₂]
    exact key _ _ hm hm' (by rw [hl, hl']) h

/-- **A value is found by its written-out form** in the table of its type. -/
theorem indexIn_eRows {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) :
    indexIn (flatVal N τ d) (eRows N τ) = vIdx N τ d :=
  indexIn_map (flatVal N τ) (elems N τ) (fun _ hx e => flatVal_inj τ hx hd e)

theorem eRows_getD {N : Nat} {τ : HO.Ty} {d : Dom τ} (hd : d ∈ elems N τ) :
    (eRows N τ).getD (vIdx N τ d) [] = flatVal N τ d := by
  simp only [eRows, List.getD_eq_getElem?_getD, List.getElem?_map, vIdx, getElem?_indexIn d _ hd,
    Option.map_some, Option.getD_some]

theorem getD_map_lt {α β : Type} (g : α → β) (c : α) (z : β) :
    ∀ (l : List α) {i : Nat}, i < l.length → (l.map g).getD i z = g (l.getD i c)
  | [], _, h => by simp at h
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => getD_map_lt g c z l (by simp at h; omega)

/-- Block `k` of a concatenation of blocks of length `m`. -/
theorem block_flatMap {α : Type} (g : α → List Nat) (m : Nat) :
    ∀ (l : List α) (c : α) {k : Nat}, (∀ x ∈ l, (g x).length = m) → k < l.length →
      ((l.flatMap g).drop (k * m)).take m = g (l.getD k c)
  | [], _, _, _, h => by simp at h
  | x :: l, c, 0, hl, _ => by
    simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getD_cons_zero]
    exact List.take_left' (hl x List.mem_cons_self)
  | x :: l, c, k + 1, hl, hk => by
    simp only [List.flatMap_cons, List.getD_cons_succ]
    rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (hl x List.mem_cons_self)]
    exact block_flatMap g m l c (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by simp at hk; omega)

/-- **Application is taking a block**: `f d` is block `vIdx d` of `f` written out. -/
theorem flatVal_app {N : Nat} {a b : HO.Ty} {f : Dom (a ⇒ b)} (hf : f ∈ elems N (a ⇒ b)) {d : Dom a}
    (hd : d ∈ elems N a) :
    flatVal N b (Dom.app (N := N) f d) =
      ((flatVal N (a ⇒ b) f).drop (vIdx N a d * valSize N b)).take (valSize N b) := by
  have ⟨hl, hm⟩ := mem_elems_arr_entries hf
  have hlt : vIdx N a d < (f : List (Dom b)).length := by rw [hl]; exact vIdx_lt hd
  show flatVal N b ((f : List (Dom b)).getD (vIdx N a d) (bot N b)) = _
  simp only [flatVal]
  rw [block_flatMap (flatVal N b) (valSize N b) _ (bot N b) (fun x hx => length_flatVal b (hm x hx)) hlt]

end Shallot.MacroPeg.Flat
