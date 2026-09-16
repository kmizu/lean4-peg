import PalPeg.GalilScaffoldTopMerge

/-!
# Phase theorems on the merged frame

The per-mode phase theorems live on the pulled-back per-mode frames. This
module transfers whole `Steps` runs to `galilFrame`, carrying the two
cross-mode invariants: outside copy mode the FPP copy counter is exhausted
(`CopyIdle`), outside shift mode the shift counter is non-positive
(`ShiftIdle`). Ticks along a lens preserve the components outside that lens.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

def CopyIdle (s : GalilVM) : Prop :=
  ¬ (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))).remainingPos s

def ShiftIdle (s : GalilVM) : Prop :=
  ¬ (Frame.pull shiftLens (shiftFrame (fun _ => True) (fun _ => True))).remainingPos s

theorem copyIdle_iff (s : GalilVM) : CopyIdle s ↔
    (GalilScaffoldPlace.read s.fpp.walker = none ∨ GalilScaffoldCounter.zero s.fpp.work = true) := by
  unfold CopyIdle Frame.pull fallbackFrame fppLens
  simp only [not_not]

theorem shiftIdle_iff (s : GalilVM) : ShiftIdle s ↔
    GalilScaffoldCounter.positive s.remaining = false := by
  unfold ShiftIdle Frame.pull shiftFrame shiftLens
  simp only
  constructor
  · intro h; cases hp : GalilScaffoldCounter.positive s.remaining
    · rfl
    · exact absurd hp h
  · intro h hp; rw [h] at hp; cases hp

/-- A tick along a lens leaves the state outside the lens unchanged: the
target is `L.set s v` or `s` itself. -/
theorem tick_pull_shape {σ σ' : Type} (L : Lens σ σ') (F : Frame σ') (delay : ℕ)
    {c c' : Control} {s t : σ} (h : Tick (Frame.pull L F) delay ⟨c, s⟩ ⟨c', t⟩) :
    ∃ v, t = L.set s v := by
  cases h <;> first
    | exact ⟨L.get s, (L.set_get s).symm⟩
    | (obtain ⟨_, ht⟩ := ‹_ ∧ _ = L.set _ _›
       first
         | exact ⟨_, ht⟩
         | (obtain ⟨_, hs'⟩ := ‹_ ∧ _ = L.set s _›
            rw [hs'] at ht
            exact ⟨_, ht.trans (L.set_set _ _ _)⟩))

theorem shift_set_fpp (s : GalilVM) (v : ShiftVM) : (shiftLens.set s v).fpp = s.fpp := rfl
theorem fpp_set_remaining (s : GalilVM) (v : FppControl.State) : (fppLens.set s v).remaining = s.remaining := rfl
theorem rewind_set_remaining (s : GalilVM) (v : RewindVM) : (rewindLens.set s v).remaining = s.remaining := rfl

theorem copyIdle_shift {c c' : Control} {s t : GalilVM} (delay : ℕ) (F : Frame ShiftVM)
    (h : Tick (Frame.pull shiftLens F) delay ⟨c, s⟩ ⟨c', t⟩) (hi : CopyIdle s) : CopyIdle t := by
  obtain ⟨v, rfl⟩ := tick_pull_shape shiftLens F delay h
  rw [copyIdle_iff] at hi ⊢
  exact hi

theorem shiftIdle_fpp {c c' : Control} {s t : GalilVM} (delay : ℕ) (F : Frame FppControl.State)
    (h : Tick (Frame.pull fppLens F) delay ⟨c, s⟩ ⟨c', t⟩) (hi : ShiftIdle s) : ShiftIdle t := by
  obtain ⟨v, rfl⟩ := tick_pull_shape fppLens F delay h
  rw [shiftIdle_iff] at hi ⊢
  exact hi

theorem shiftIdle_rewind {c c' : Control} {s t : GalilVM} (delay : ℕ) (F : Frame RewindVM)
    (h : Tick (Frame.pull rewindLens F) delay ⟨c, s⟩ ⟨c', t⟩) (hi : ShiftIdle s) : ShiftIdle t := by
  obtain ⟨v, rfl⟩ := tick_pull_shape rewindLens F delay h
  rw [shiftIdle_iff] at hi ⊢
  exact hi

/-- In the shift frame no tick leaves scan mode: every scan constructor
needs a `background`/`compare` relation, which is empty there. -/
theorem no_scan_tick_shift (f g : ShiftVM → Prop) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hm : c.mode = .scan)
    (h : Tick (Frame.pull shiftLens (shiftFrame f g)) delay ⟨c, s⟩ ⟨c', t⟩) : False := by
  cases h <;> first
    | wrong_mode
    | (rename_i h1; exact h1.1.elim)
    | (rename_i h1 _ _ _; exact h1.1.elim)
    | (rename_i h1 _ _ _ _; exact h1.1.elim)

theorem shift_frame_reparam (P : Shared) (s : GalilVM) (v0 : ShiftVM) :
    shiftFrame (fun v => P.onLetter (shiftLens.set (shiftLens.set s v0) v))
        (fun v => P.leftFirst (shiftLens.set (shiftLens.set s v0) v)) =
      shiftFrame (fun v => P.onLetter (shiftLens.set s v))
        (fun v => P.leftFirst (shiftLens.set s v)) := by
  simp only [shiftLens.set_set]

/-- Shift-mode runs transfer to `galilFrame`, preserving `CopyIdle`. -/
theorem steps_transfer_shift (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ) :
    ∀ {c c' : Control} {s0 s t : GalilVM} {v0 : ShiftVM}, s = shiftLens.set s0 v0 →
      c.mode = .shift → CopyIdle s →
      Steps (Frame.pull shiftLens (shiftFrame (fun v => P.onLetter (shiftLens.set s0 v))
        (fun v => P.leftFirst (shiftLens.set s0 v)))) delay n ⟨c, s⟩ ⟨c', t⟩ →
      Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ CopyIdle t := by
  induction n with
  | zero =>
    intro c c' s0 s t v0 _ _ hi h
    cases h
    exact ⟨.zero _, hi⟩
  | succ n ih =>
    intro c c' s0 s t v0 hs hm hi h
    cases h with
    | succ ht hr =>
      rename_i y
      obtain ⟨c1, s1⟩ := y
      -- reparametrise the frame at the current state
      have hfr : (fun v => P.onLetter (shiftLens.set s0 v)) = (fun v => P.onLetter (shiftLens.set s v)) := by
        subst hs; funext v; rw [shiftLens.set_set]
      have hfr' : (fun v => P.leftFirst (shiftLens.set s0 v)) = (fun v => P.leftFirst (shiftLens.set s v)) := by
        subst hs; funext v; rw [shiftLens.set_set]
      have ht' := ht
      rw [hfr, hfr'] at ht'
      have hg := shift_transfer P q first delay hm hi ht'
      have hi1 := copyIdle_shift delay _ ht hi
      obtain ⟨v1, hv1⟩ := tick_pull_shape shiftLens _ delay ht
      rcases tick_mode _ delay ht with hm1 | hm1
      · -- still in shift mode
        have hs1 : s1 = shiftLens.set s0 (shiftLens.get s1) := by
          rw [hv1, hs, shiftLens.set_set, shiftLens.get_set]
        obtain ⟨hr', hi'⟩ := ih hs1 (by simp only [] at hm1; rw [hm1]; exact hm) hi1 hr
        exact ⟨.succ hg hr', hi'⟩
      · -- left to scan: no further shift-frame tick is possible
        simp only [] at hm1
        rw [hm] at hm1
        have hm1' : c1.mode = .scan := by
          generalize hmm : c1.mode = m at hm1
          cases hm1; rfl
        cases hr with
        | zero => exact ⟨.succ hg (.zero _), hi1⟩
        | succ ht2 _ =>
          exact (no_scan_tick_shift _ _ delay hm1' ht2).elim

#print axioms steps_transfer_shift

end PalPeg.GalilScaffoldChainInputSupply
