import PalPeg.LocalState

/-!
# The cells of an input view

A view stores `Option (Fin 2)` cells, and `none` is a cell: the sentinel left of the input.  On a
tape `none` is the blank symbol, so whether the `back` or the `near` stack of a view is empty
cannot be read from symbols alone.  The content of a view has a shape that makes it readable: the
only `none` is the cell at position `0` (arrivals append letters, the first focus is the
sentinel).  Hence the head is at the left end exactly when the focus is `none`, and the `near`
stack holds letters only.
-/

set_option autoImplicit false

namespace PalPeg.LocalViewCells

open PalPeg.LocalInputView

/-- The content of a view is the sentinel followed by letters. -/
def ViewCells (v : InputView) : Prop :=
  ∃ letters : List (Fin 2), cells v = none :: letters.map some

theorem viewCells_arrive {v : InputView} (hwf : WF v) (hcells : ViewCells v) (a : Fin 2) :
    ViewCells (arrive a v) := by
  obtain ⟨letters, hletters⟩ := hcells
  refine ⟨letters ++ [a], ?_⟩
  rw [cells_arrive hwf, hletters]
  simp

theorem viewCells_stepRight {v : InputView} (hwf : WF v) (hcells : ViewCells v) :
    ViewCells (stepRight v) := by
  obtain ⟨letters, hletters⟩ := hcells
  exact ⟨letters, by rw [cells_stepRight hwf, hletters]⟩

theorem viewCells_stepLeft {v : InputView} (hcells : ViewCells v) : ViewCells (stepLeft v) := by
  obtain ⟨letters, hletters⟩ := hcells
  exact ⟨letters, by rw [cells_stepLeft, hletters]⟩

theorem viewCells_moveRight {v : InputView} (hwf : WF v) (hcells : ViewCells v) :
    ViewCells (moveRight v) := by
  unfold moveRight
  split
  · obtain ⟨letters, hletters⟩ := viewCells_stepRight hwf hcells
    exact ⟨letters, hletters⟩
  · obtain ⟨letters, hletters⟩ := hcells
    exact ⟨letters, hletters⟩

theorem viewCells_moveLeft {v : InputView} (hcells : ViewCells v) : ViewCells (moveLeftV v) := by
  unfold moveLeftV
  split
  · obtain ⟨letters, hletters⟩ := hcells
    exact ⟨letters, hletters⟩
  · obtain ⟨letters, hletters⟩ := viewCells_stepLeft hcells
    exact ⟨letters, hletters⟩

theorem viewCells_emptyView : ViewCells emptyView := ⟨[], rfl⟩

theorem viewCells_repositionStep {v : InputView} (hwf : WF v) (hcells : ViewCells v)
    (target : ℕ) : ViewCells (repositionStep target v) := by
  unfold repositionStep
  split
  · exact viewCells_stepRight hwf hcells
  · split
    · exact viewCells_stepLeft hcells
    · exact hcells

/-- **Every view action of the local machine keeps the shape of the content.** -/
theorem viewCells_viewLocal {v v' : InputView} (hwf : WF v) (hcells : ViewCells v)
    (hlocal : PalPeg.LocalState.ViewLocal v v') : ViewCells v' := by
  rcases hlocal with hsame | ⟨a, harrive⟩ | hright | hleft | ⟨target, hreposition⟩
  · rw [hsame]; exact hcells
  · rw [harrive]; exact viewCells_arrive hwf hcells a
  · rw [hright]; exact viewCells_moveRight hwf hcells
  · rw [hleft]; exact viewCells_moveLeft hcells
  · rw [hreposition]; exact viewCells_repositionStep hwf hcells target

/-- **The head is at the left end exactly when the focus is the sentinel.** -/
theorem back_nil_iff_focus_none {v : InputView} (hcells : ViewCells v) :
    v.back = [] ↔ v.focus = none := by
  obtain ⟨letters, hletters⟩ := hcells
  unfold cells at hletters
  constructor
  · intro hback
    rw [hback] at hletters
    simp only [List.reverse_nil, List.nil_append, List.cons.injEq] at hletters
    exact hletters.1
  · intro hfocus
    by_contra hback
    -- a non-empty `back` puts the focus at a position `≥ 1`, where cells are letters
    have hlength : 1 ≤ v.back.reverse.length := by
      rw [List.length_reverse]
      cases hb : v.back with
      | nil => exact absurd hb hback
      | cons c rest => simp
    have hget := congrArg (fun l => l[v.back.reverse.length]?) hletters
    simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero] at hget
    obtain ⟨n, hn⟩ : ∃ n, v.back.reverse.length = n + 1 := ⟨v.back.reverse.length - 1, by omega⟩
    rw [hn, List.getElem?_cons_succ, List.getElem?_map, hfocus] at hget
    cases hl : letters[n]? with
    | none => rw [hl] at hget; cases hget
    | some a => rw [hl] at hget; cases hget

/-- **The `near` stack holds letters only.** -/
theorem near_letters {v : InputView} (hcells : ViewCells v) :
    ∃ nearLetters : List (Fin 2), v.near = nearLetters.map some := by
  obtain ⟨letters, hletters⟩ := hcells
  unfold cells absRight at hletters
  -- `near` sits after the focus, i.e. at positions `≥ 1`
  have hsplit : v.back.reverse ++ v.focus :: (v.near ++ farList v)
      = (v.back.reverse ++ [v.focus]) ++ v.near ++ farList v := by simp
  rw [hsplit] at hletters
  have hall : ∀ c ∈ v.near, ∃ a : Fin 2, c = some a := by
    intro c hc
    obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
    have hget := congrArg (fun l => l[(v.back.reverse ++ [v.focus]).length + i]?) hletters
    have hleft : ((v.back.reverse ++ [v.focus]) ++ v.near ++ farList v)[
        (v.back.reverse ++ [v.focus]).length + i]? = some c := by
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hci]
    beta_reduce at hget
    rw [hleft] at hget
    have hpositive : (v.back.reverse ++ [v.focus]).length + i
        = ((v.back.reverse ++ [v.focus]).length + i - 1) + 1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hpositive, List.getElem?_cons_succ, List.getElem?_map] at hget
    cases hl : letters[(v.back.reverse ++ [v.focus]).length + i - 1]? with
    | none => rw [hl] at hget; cases hget
    | some a => rw [hl] at hget; exact ⟨a, by simpa using hget⟩
  clear hletters hsplit
  generalize v.near = near at hall
  induction near with
  | nil => exact ⟨[], rfl⟩
  | cons c rest ih =>
    obtain ⟨a, ha⟩ := hall c (List.mem_cons_self ..)
    obtain ⟨restLetters, hrest⟩ := ih (fun d hd => hall d (List.mem_cons_of_mem _ hd))
    exact ⟨a :: restLetters, by rw [ha, hrest]; rfl⟩

#print axioms back_nil_iff_focus_none
#print axioms near_letters

end PalPeg.LocalViewCells
