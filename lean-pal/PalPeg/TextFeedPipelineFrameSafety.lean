import PalPeg.TextFeedPipelineFrames

/-! Every Q1 supply selected by a residual verifier frame targets a blank
cell. Unlike prefix alignment, these frames never overwrite supplied text. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrameSafety
open PalPeg.ProgLang PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames
open PalPeg.TextFeedPipelineBranch
variable {k : ℕ}

theorem preWait_feed1 (ev : TaskCond k → Bool) (a : A)
    (h : preWait ev a = some .feed1) : ev (.inr (.inl .blankText)) = true := by
  cases a with
  | inr up => simp [preWait] at h
  | inl a =>
    simp only [preWait] at h
    split_ifs at h <;> simp_all

theorem postWait_feed1 (ev : TaskCond k → Bool) (a : A)
    (h : postWait ev a = true) : ev (.inr (.inl .blankText)) = true := by
  cases a with
  | inr up => simp [postWait] at h
  | inl a =>
    simp only [postWait, Bool.and_eq_true] at h
    exact h.2

theorem condEvent_feed1 (ev : TaskCond k → Bool) (c : C)
    (h : Waiting ev c = true) (he : condEvent c = .feed1) :
    ev (.inr (.inr (.inr .scanWait))) = true := by
  cases c with
  | inr c => cases c <;> simp [Waiting] at h
  | inl c => cases c <;> simp_all [Waiting, condEvent]

theorem next_feed1_guard (ev : TaskCond k → Bool)
    (coherent : ev (.inr (.inr (.inr .scanWait))) = true → ev (.inr (.inl .blankText)) = true)
    (fs : List Frame) (h : (next ev fs).2 = .feed1) : ev (.inr (.inl .blankText)) = true := by
  induction fs using next.induct (ev := ev) <;> simp_all [next]
  case case8 a fs w hp => exact preWait_feed1 ev a hp
  case case10 a fs hp => exact postWait_feed1 ev a hp
  case case12 c p q fs hw => exact coherent (condEvent_feed1 ev c hw h)
  case case14 c a b fs hw => exact coherent (condEvent_feed1 ev c hw h)

theorem next_feed1_blank (e : PalPeg.TextFeedControl.Env k) (σ : Fin 39 → Fin k)
    (fs : List Frame) (h : (next (taskEval e σ) fs).2 = .feed1) : σ 12 = e.blank := by
  have hc : taskEval e σ (.inr (.inr (.inr .scanWait))) = true →
      taskEval e σ (.inr (.inl .blankText)) = true := by
    intro hw
    change decide (σ 12 = e.blank) = true
    exact decide_eq_true (scan_wait_blank e σ hw)
  exact of_decide_eq_true (next_feed1_guard (taskEval e σ) hc fs h)

theorem preWait_feed2 (ev : TaskCond k → Bool) (a : A)
    (h : preWait ev a = some .feed2) : ev (.inr (.inr (.inr .blankX))) = true := by
  cases a with
  | inr up => simp [preWait] at h
  | inl a =>
    simp only [preWait] at h
    split_ifs at h <;> simp_all

theorem condEvent_feed2 (ev : TaskCond k → Bool) (c : C)
    (h : Waiting ev c = true) (he : condEvent c = .feed2) :
    ev (.inr (.inr (.inr .verifyWait))) = true := by
  cases c with
  | inr c => cases c <;> simp [Waiting] at h
  | inl c => cases c <;> simp_all [Waiting, condEvent]

theorem next_feed2_guard (ev : TaskCond k → Bool)
    (coherent : ev (.inr (.inr (.inr .verifyWait))) = true →
      ev (.inr (.inr (.inr .blankX))) = true)
    (fs : List Frame) (h : (next ev fs).2 = .feed2) : ev (.inr (.inr (.inr .blankX))) = true := by
  induction fs using next.induct (ev := ev) <;> simp_all [next]
  case case8 a fs w hp => exact preWait_feed2 ev a hp
  case case12 c p q fs hw => exact coherent (condEvent_feed2 ev c hw h)
  case case14 c a b fs hw => exact coherent (condEvent_feed2 ev c hw h)

theorem next_feed2_blank (e : PalPeg.TextFeedControl.Env k) (σ : Fin 39 → Fin k)
    (fs : List Frame) (h : (next (taskEval e σ) fs).2 = .feed2) : σ 20 = e.blank := by
  have hc : taskEval e σ (.inr (.inr (.inr .verifyWait))) = true →
      taskEval e σ (.inr (.inr (.inr .blankX))) = true := by
    intro hw
    change decide (σ 20 = e.blank) = true
    exact decide_eq_true (comp_wait_blank e σ hw)
  exact of_decide_eq_true (next_feed2_guard (taskEval e σ) hc fs h)

/-- info: 'PalPeg.TextFeedPipelineFrameSafety.next_feed1_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_feed1_blank

end PalPeg.TextFeedPipelineFrameSafety
