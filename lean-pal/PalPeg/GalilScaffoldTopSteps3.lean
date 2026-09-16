import PalPeg.GalilScaffoldTopSteps2

/-!
# MarkEnd runs on the merged frame

`marksFrame` exits to `choose`, where its `choose_step` (MARKS back one cell,
toggle `odd`) is still possible. Those ticks also transfer to `galilFrame`
(`markBack`/`markSet` are the same MARKS readings through the fpp and rewind
lenses), and from `choose` the frame never leaves `choose`, so the generic
transfer works with a closed exit set.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

theorem steps_transfer_generic' {σ' : Type} (L : Lens GalilVM σ') (F' : Frame σ') (G : Frame GalilVM)
    (delay : ℕ) (M E : Mode → Prop) (Inv : GalilVM → Prop)
    (hinv : ∀ {c c' : Control} {s t : GalilVM}, Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Inv s → Inv t)
    (hstep : ∀ {c c' : Control} {s t : GalilVM}, M c.mode →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → M c'.mode ∨ E c'.mode)
    (hstepE : ∀ {c c' : Control} {s t : GalilVM}, E c.mode →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → E c'.mode)
    (htr : ∀ {c c' : Control} {s t : GalilVM}, M c.mode ∨ E c.mode → Inv s →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Tick G delay ⟨c, s⟩ ⟨c', t⟩)
    (n : ℕ) : ∀ {c c' : Control} {s t : GalilVM}, M c.mode ∨ E c.mode → Inv s →
      Steps (Frame.pull L F') delay n ⟨c, s⟩ ⟨c', t⟩ → Steps G delay n ⟨c, s⟩ ⟨c', t⟩ ∧ Inv t := by
  induction n with
  | zero =>
    intro c c' s t _ hi h
    cases h
    exact ⟨.zero _, hi⟩
  | succ n ih =>
    intro c c' s t hm hi h
    cases h with
    | succ ht hr =>
      rename_i y
      obtain ⟨c1, s1⟩ := y
      have hg := htr hm hi ht
      have hi1 := hinv ht hi
      have hm1 : M c1.mode ∨ E c1.mode := by
        rcases hm with hm | hm
        · exact hstep hm ht
        · exact Or.inr (hstepE hm ht)
      obtain ⟨hr', hi'⟩ := ih hm1 hi1 hr
      exact ⟨.succ hg hr', hi'⟩

/-- Choose-mode ticks of the marks frame transfer: only `choose_step`. -/
theorem marks_choose_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (f g : FppControl.State → Prop)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .choose)
    (h : Tick (Frame.pull fppLens (marksFrame first f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case choose_select =>
    rename_i ho hs h1
    exact h1.1.elim
  case choose_step =>
    rename_i hs h1
    obtain ⟨⟨hl, hy⟩, ht⟩ := h1
    have hy' : t.fpp = markStep s.fpp GalilScaffoldTape.moveLeft := hy
    have ht' : t = {s with fpp := t.fpp} := ht
    have hteq : t = {s with fpp := markStep s.fpp GalilScaffoldTape.moveLeft} := by
      rw [ht', hy']
    subst hteq
    refine .choose_step c s _ hm ?_ ⟨⟨hl, rfl⟩, rfl⟩
    rcases hs with hs | hs
    · exact Or.inl hs
    · right; exact hs

theorem step_markEnd {σ : Type} (F : Frame σ) (delay : ℕ) {c c' : Control} {s t : σ}
    (hm : c.mode = .markEnd) (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode = .markEnd ∨ c'.mode = .choose := by
  rcases exit_of_tick F delay h with h1 | h1
  · rw [h1]; exact Or.inl hm
  · generalize c.mode = a at *
    generalize c'.mode = b at *
    cases h1 <;> simp_all

/-- In the marks frame, choose mode is closed: `choose_select` needs the empty
`choose` relation. -/
theorem step_marks_choose (first : Fin 9) (f g : FppControl.State → Prop) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .choose)
    (h : Tick (Frame.pull fppLens (marksFrame first f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode = .choose := by
  cases h <;> try wrong_mode
  case choose_select =>
    rename_i ho hs h1
    exact h1.1.elim
  case choose_step =>
    exact hm

theorem steps_transfer_markEnd (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .markEnd) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (marksFrame first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic' fppLens _ _ delay (fun m => m = .markEnd) (fun m => m = .choose) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_markEnd _ delay hm' ht)
    (fun hm' ht => step_marks_choose first _ _ delay hm' ht)
    (fun hm' _ ht => by
      rcases hm' with hm' | hm'
      · exact markEnd_transfer P q first delay _ _ hm' ht
      · exact marks_choose_transfer P q first delay _ _ hm' ht)
    n (Or.inl hm) hi h

#print axioms steps_transfer_markEnd

end PalPeg.GalilScaffoldChainInputSupply
