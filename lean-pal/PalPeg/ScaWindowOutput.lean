import PalPeg.ScaWindowSchedule
import PalPeg.Assembly

/-!
# The window controller's output

`small` counts the letters up to four and `first` remembers the first letter; from four letters on
the output is the answering stage's `middle` and its matcher's output.
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowOutput
open PalPeg.ScaWindowPal PalPeg.ScaWindowSchedule

section
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

@[simp] theorem stageRound_small (a : Fin 2) (i : Fin 2) (s : PalState Wm Wf) :
    (stageRound mOps fOps a i s).small = s.small := rfl

@[simp] theorem stageRound_first (a : Fin 2) (i : Fin 2) (s : PalState Wm Wf) :
    (stageRound mOps fOps a i s).first = s.first := rfl

theorem tick_small (a : Fin 2) (s : PalState Wm Wf) :
    (tick mOps fOps s a).small = incSmall s.small ∧
    (tick mOps fOps s a).first = (if s.small.val == 0 then (a == 1) else s.first) := by
  constructor <;> simp [tick]

theorem small_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) :
    (run mOps fOps m0 f0 w).small.val = min 4 w.length := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [run_append, (tick_small mOps fOps a _).1, List.length_append, List.length_singleton]
    simp only [incSmall, ih]
    omega

theorem first_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (hw : 1 ≤ w.length) :
    (run mOps fOps m0 f0 w).first = (w[0]? == some 1) := by
  induction w using List.reverseRecOn with
  | nil => simp at hw
  | append_singleton w a ih =>
    rw [run_append, (tick_small mOps fOps a _).2, small_run]
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · rw [List.length_eq_zero_iff.mp h0]
      cases a using Fin.cases with
      | zero => rfl
      | succ j => fin_cases j; rfl
    · have hmin : (min 4 w.length == 0) = false := by
        rw [beq_eq_false_iff_ne]; omega
      rw [hmin, ih hpos, List.getElem?_append_left hpos]
      rfl

theorem tick_output (a : Fin 2) (s : PalState Wm Wf) :
    (tick mOps fOps s a).output =
      if (incSmall s.small).val == 4 then
        ((answering ((tick mOps fOps s a).stages 0) && ((tick mOps fOps s a).stages 0).middle &&
            mOps.output ((tick mOps fOps s a).matchers 0)) ||
          (answering ((tick mOps fOps s a).stages 1) && ((tick mOps fOps s a).stages 1).middle &&
            mOps.output ((tick mOps fOps s a).matchers 1)))
      else ((incSmall s.small).val == 1 ||
        (((incSmall s.small).val == 2 || (incSmall s.small).val == 3) &&
          (if a == 1 then (tick mOps fOps s a).first else !(tick mOps fOps s a).first))) := rfl

theorem idx_pred_ne {k : ℕ} (hk : 1 ≤ k) : idx (k - 1) ≠ idx k := by
  have := idx_succ_ne (k - 1)
  rwa [Nat.sub_add_cancel hk] at this

/-- **From four letters on**: the output is the answering stage's `middle` and its matcher. -/
theorem output_long (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    (run mOps fOps m0 f0 w).output =
      (((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))).middle &&
        mOps.output ((run mOps fOps m0 f0 w).matchers (idx (Nat.log 2 w.length)))) := by
  obtain ⟨hk2, hans, hnot, -⟩ := answering_run mOps fOps m0 f0 w hw
  obtain ⟨w', a, rfl⟩ : ∃ w' a, w = w' ++ [a] :=
    ⟨w.dropLast, w.getLast (by rintro rfl; simp at hw), (List.dropLast_append_getLast _).symm⟩
  have hsmall := small_run mOps fOps m0 f0 w'
  simp only [List.length_append, List.length_singleton] at hw hans hnot hk2 ⊢
  rw [run_append] at hans hnot ⊢
  rw [tick_output]
  have hfour : ((incSmall (run mOps fOps m0 f0 w').small).val == 4) = true := by
    simp only [incSmall, hsmall, beq_iff_eq]; omega
  rw [if_pos hfour]
  have hne := idx_pred_ne (k := Nat.log 2 (w'.length + 1)) (by omega)
  generalize idx (Nat.log 2 (w'.length + 1)) = i at hans hnot hne ⊢
  generalize idx (Nat.log 2 (w'.length + 1) - 1) = j at hans hnot hne
  fin_cases i <;> fin_cases j <;> simp_all

/-- **Up to three letters**: the output compares the first and the last letter. -/
theorem output_short (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (h1 : 1 ≤ w.length)
    (h3 : w.length ≤ 3) : (run mOps fOps m0 f0 w).output = true ↔ IsPal w := by
  have hfirst := first_run mOps fOps m0 f0 w h1
  obtain ⟨w', a, rfl⟩ : ∃ w' a, w = w' ++ [a] :=
    ⟨w.dropLast, w.getLast (by rintro rfl; simp at h1), (List.dropLast_append_getLast _).symm⟩
  have hsmall := small_run mOps fOps m0 f0 w'
  simp only [List.length_append, List.length_singleton] at h1 h3
  rw [run_append] at hfirst ⊢
  rw [tick_output, hfirst]
  have hsm : (incSmall (run mOps fOps m0 f0 w').small).val = w'.length + 1 := by
    simp only [incSmall, hsmall]; omega
  simp only [hsm]
  have hpal : IsPal (w' ++ [a]) ↔ (w' ++ [a])[0]? = (w' ++ [a])[w'.length + 1 - 1]? := by
    rcases Nat.lt_or_ge (w'.length + 1) 2 with hlt | hge
    · have : w'.length = 0 := by omega
      rw [List.length_eq_zero_iff.mp this]
      simp [IsPal]
    · have := pal_take_two_three (w := w' ++ [a]) (n := w'.length + 1) hge (by omega)
        (by simp)
      rwa [show (w' ++ [a]).take (w'.length + 1) = w' ++ [a] by simp] at this
  rw [hpal, show w'.length + 1 - 1 = w'.length by omega, List.getElem?_append_right le_rfl,
    Nat.sub_self]
  simp only [List.getElem?_singleton]
  rcases Nat.eq_zero_or_pos w'.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    fin_cases a <;> simp
  · rw [List.getElem?_append_left hpos]
    obtain ⟨b, hb⟩ : ∃ b, w'[0]? = some b := ⟨w'[0], List.getElem?_eq_getElem hpos⟩
    rw [hb]
    have hne1 : w'.length + 1 ≠ 1 := by omega
    have h4 : w'.length ≠ 3 := by omega
    fin_cases a <;> fin_cases b <;> simp [h4, ← List.length_eq_zero_iff] <;> omega

/-- **The window controller recognizes `PAL`**, given its two workers: the answering stage's
matcher reports the reversed-pattern occurrence and its `middle` reports the middle palindrome,
and nothing faults. -/
theorem window_correct (m0 : Wm) (f0 : Wf)
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (mOps.output ((run mOps fOps m0 f0 w).matchers (idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hmiddle : ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))))
    (hfault : ∀ w : List (Fin 2), globalFault mOps fOps (run mOps fOps m0 f0 w) = false)
    (w : List (Fin 2)) : Accepts mOps fOps m0 f0 w ↔ w ∈ PalPeg.PAL := by
  show accepts mOps fOps m0 f0 w = true ↔ w.reverse = w
  change _ ↔ IsPal w
  unfold accepts
  cases hw : w.isEmpty
  · have h1 : 1 ≤ w.length := by
      rcases w with _ | ⟨x, xs⟩
      · simp at hw
      · simp
    simp only [Bool.false_eq_true, if_false, hfault w, Bool.not_false, Bool.and_true]
    rcases Nat.lt_or_ge w.length 4 with hlt | hge
    · exact output_short mOps fOps m0 f0 w h1 (by omega)
    · rw [output_long mOps fOps m0 f0 w hge, Bool.and_eq_true, hmiddle w hge, hmatch w hge]
      have hW := stageOf_spec (n := w.length) (by omega)
      have := pal_prefix_iff_stage (w := w) (n := w.length) (W := stageOf w.length) hW.1 le_rfl
      rw [List.take_length] at this
      rw [this, and_comm]
  · rw [List.isEmpty_iff.mp hw]
    simp [IsPal]

end
end PalPeg.ScaWindowOutput
