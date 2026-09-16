import PalPeg.GalilScaffoldTopSteps

/-!
# Generic steps transfer and the remaining modes

A per-mode frame whose exit mode admits no tick at all transfers whole
`Steps` runs to `galilFrame` as long as the run starts in one of its modes:
after the tick that leaves, no further tick exists, so the run has ended.
This covers copy/home (`fallbackFrame`, exit `fpp`), fpp (`fppFrame`, exit
`markEnd`), and choose/rewind (`rewindFrame`, exit `replayStart`).
`marksFrame` exits to `choose`, where its `choose_step` remains possible;
its walk is transferred with the constant-controller shape of `markEnd_walk`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

theorem steps_transfer_generic {σ' : Type} (L : Lens GalilVM σ') (F' : Frame σ') (G : Frame GalilVM)
    (delay : ℕ) (M E : Mode → Prop) (Inv : GalilVM → Prop)
    (hinv : ∀ {c c' : Control} {s t : GalilVM}, Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Inv s → Inv t)
    (hstep : ∀ {c c' : Control} {s t : GalilVM}, M c.mode →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → M c'.mode ∨ E c'.mode)
    (hexit : ∀ {c c' : Control} {s t : GalilVM}, E c.mode → ¬ Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩)
    (htr : ∀ {c c' : Control} {s t : GalilVM}, M c.mode → Inv s →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Tick G delay ⟨c, s⟩ ⟨c', t⟩)
    (n : ℕ) : ∀ {c c' : Control} {s t : GalilVM}, M c.mode → Inv s →
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
      rcases hstep hm ht with hm1 | hm1
      · obtain ⟨hr', hi'⟩ := ih hm1 hi1 hr
        exact ⟨.succ hg hr', hi'⟩
      · cases hr with
        | zero => exact ⟨.succ hg (.zero _), hi1⟩
        | succ ht2 _ => exact (hexit hm1 ht2).elim

/-- The mode after a tick from a mode in `M` is in `M` or in the exit set. -/
theorem exit_of_tick {σ : Type} (F : Frame σ) (delay : ℕ) {c c' : Control} {s t : σ}
    (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode = c.mode ∨ ModeStep c.mode c'.mode := tick_mode F delay h

/-- Elimination of a tick whose frame relation is empty: try each position of
the relation among the trailing hypotheses. -/
macro "empty_rel" : tactic => `(tactic| first
  | wrong_mode
  | (rename_i h1; exact h1.1.elim)
  | (rename_i h1 _; exact h1.1.elim)
  | (rename_i h1 _ _; exact h1.1.elim)
  | (rename_i h1 _ _ _; exact h1.1.elim)
  | (rename_i h1 _ _ _ _; exact h1.1.elim)
  | (rename_i h1 _ _ _ _ _; exact h1.1.elim)
  | (rename_i h1; exact h1.elim)
  | (rename_i h1 _; exact h1.elim)
  | (rename_i h1 _ _; exact h1.elim))

theorem no_tick_fallback (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hm : c.mode = .fpp)
    (h : Tick (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))) delay ⟨c, s⟩ ⟨c', t⟩) :
    False := by
  cases h <;> empty_rel

theorem no_tick_fpp (q : ℕ) (first : Fin 9) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hm : c.mode = .markEnd)
    (h : Tick (Frame.pull fppLens (fppFrame q first (fun _ => True) (fun _ => True))) delay ⟨c, s⟩ ⟨c', t⟩) :
    False := by
  cases h <;> empty_rel

theorem no_tick_rewind (first : Fin 9) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hm : c.mode = .replayStart)
    (h : Tick (Frame.pull rewindLens (rewindFrame first (fun _ => True) (fun _ => True))) delay ⟨c, s⟩ ⟨c', t⟩) :
    False := by
  cases h <;> empty_rel

/-- Mode bookkeeping for the three instances. -/
theorem step_fallback {σ : Type} (F : Frame σ) (delay : ℕ) {c c' : Control} {s t : σ}
    (hm : c.mode = .copy ∨ c.mode = .home) (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    (c'.mode = .copy ∨ c'.mode = .home) ∨ c'.mode = .fpp := by
  rcases exit_of_tick F delay h with h1 | h1
  · rw [h1]; exact Or.inl hm
  · generalize c.mode = a at *
    generalize c'.mode = b at *
    cases h1 <;> simp_all

theorem step_fpp {σ : Type} (F : Frame σ) (delay : ℕ) {c c' : Control} {s t : σ}
    (hm : c.mode = .fpp) (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode = .fpp ∨ c'.mode = .markEnd := by
  rcases exit_of_tick F delay h with h1 | h1
  · rw [h1]; exact Or.inl hm
  · generalize c.mode = a at *
    generalize c'.mode = b at *
    cases h1 <;> simp_all

theorem step_rewind {σ : Type} (F : Frame σ) (delay : ℕ) {c c' : Control} {s t : σ}
    (hm : c.mode = .choose ∨ c.mode = .rewind) (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    (c'.mode = .choose ∨ c'.mode = .rewind) ∨ c'.mode = .replayStart := by
  rcases exit_of_tick F delay h with h1 | h1
  · rw [h1]; exact Or.inl hm
  · generalize c.mode = a at *
    generalize c'.mode = b at *
    cases h1 <;> simp_all

/-- Copy/home runs transfer, preserving `ShiftIdle`. -/
theorem steps_transfer_fallback (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .copy ∨ c.mode = .home) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t := by
  exact steps_transfer_generic fppLens _ _ delay (fun m => m = .copy ∨ m = .home) (fun m => m = .fpp) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_fallback _ delay hm' ht)
    (fun hm' ht => no_tick_fallback delay hm' ht)
    (fun hm' hi' ht => fallback_transfer P q first delay _ _ hm' hi' ht) n hm hi h

/-- Fpp runs transfer. -/
theorem steps_transfer_fpp (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .fpp) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (fppFrame q first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic fppLens _ _ delay (fun m => m = .fpp) (fun m => m = .markEnd) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_fpp _ delay hm' ht)
    (fun hm' ht => no_tick_fpp q first delay hm' ht)
    (fun hm' _ ht => fpp_transfer P q first delay _ _ hm' ht) n hm hi h

/-- Choose/rewind runs transfer. -/
theorem steps_transfer_rewind (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .choose ∨ c.mode = .rewind) (hi : ShiftIdle s)
    (h : Steps (Frame.pull rewindLens (rewindFrame first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic rewindLens _ _ delay (fun m => m = .choose ∨ m = .rewind) (fun m => m = .replayStart) ShiftIdle
    (fun ht hi => shiftIdle_rewind delay _ ht hi) (fun hm' ht => step_rewind _ delay hm' ht)
    (fun hm' ht => no_tick_rewind first delay hm' ht)
    (fun hm' _ ht => rewind_transfer P q first delay _ _ hm' ht) n hm hi h

#print axioms steps_transfer_fallback
#print axioms steps_transfer_fpp
#print axioms steps_transfer_rewind

end PalPeg.GalilScaffoldChainInputSupply
