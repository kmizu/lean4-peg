import PalPeg.TextFeedPipelineFrames

/-! A loop-commit idle creates a mandatory pending instruction. Until
that instruction executes, no second loop commit can be emitted. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrameCost
open PalPeg.ProgLang PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames
open PalPeg.TextFeedPipelineBranch
variable {k : ℕ}

def debt : List Frame → ℕ
  | .pending _ :: _ | .body _ _ _ :: _ => 1
  | .skip :: fs => debt fs
  | _ => 0

theorem debt_le (fs : List Frame) : debt fs ≤ 1 := by
  induction fs with
  | nil => decide
  | cons f fs ih => cases f <;> simp_all [debt]

theorem preWait_not_idle (ev : TaskCond k → Bool) (a : A) {w : Event}
    (h : preWait ev a = some w) : w ≠ .idle := by
  cases a with
  | inr up => simp [preWait] at h
  | inl a =>
    simp only [preWait] at h
    split_ifs at h <;> cases h <;> intro he <;> cases he

theorem waiting_not_idle (ev : TaskCond k → Bool) (c : C)
    (h : Waiting ev c = true) : condEvent c ≠ .idle := by
  cases c with
  | inl c => cases c <;> simp_all [Waiting, condEvent]
  | inr c => cases c <;> simp [Waiting] at h

theorem idle_debt (ev : TaskCond k → Bool) (fs : List Frame)
    (h : (next ev fs).2 = .idle) : debt (next ev fs).1 = 1 := by
  induction fs using next.induct (ev := ev) with
  | case1 => rw [next] at h; cases h
  | case2 fs ih => rw [next] at h ⊢; exact ih h
  | case3 fs ih => rw [next] at h ⊢; exact ih h
  | case4 a fs ih => rw [next] at h ⊢; exact ih h
  | case5 p q fs ih => rw [next] at h ⊢; exact ih h
  | case6 c p q fs ih => rw [next] at h ⊢; exact ih h
  | case7 c a b fs ih => rw [next] at h ⊢; exact ih h
  | case8 a fs w hw =>
    simp only [next, hw] at h
    exact False.elim (preWait_not_idle ev a hw h)
  | case9 a fs hw => simp only [next, hw] at h; cases h
  | case10 a fs hw => simp only [next, hw, ↓reduceIte] at h; cases h
  | case11 a fs hw ih => rw [next, if_neg hw] at h ⊢; exact ih h
  | case12 c p q fs hw =>
    simp only [next, hw, ↓reduceIte] at h
    exact False.elim (waiting_not_idle ev c hw h)
  | case13 c p q fs hw ih =>
    rw [next, if_neg hw] at h ⊢
    exact ih h
  | case14 c a b fs hw =>
    simp only [next, hw, ↓reduceIte] at h
    exact False.elim (waiting_not_idle ev c hw h)
  | case15 c a b fs hw hc => rw [next, if_neg hw, if_pos hc]; rfl
  | case16 c a b fs hw hc ih =>
    rw [next, if_neg hw, if_neg hc] at h ⊢
    exact ih h
  | case17 c a b fs ih => rw [next] at h ⊢; exact ih h
  | case18 c a b fs ih => rw [next] at h ⊢; exact ih h

theorem pending_progress (ev : TaskCond k → Bool) (a : A) (fs : List Frame) :
    (∃ b, (next ev (.pending a :: fs)).2 = .instruction b) ∨
      (debt (next ev (.pending a :: fs)).1 = 1 ∧ (next ev (.pending a :: fs)).2 ≠ .idle) := by
  cases hw : preWait ev a with
  | none => simp only [next, hw]; exact Or.inl ⟨a, rfl⟩
  | some w =>
    simp only [next, hw]
    exact Or.inr ⟨rfl, preWait_not_idle ev a hw⟩

theorem debt_progress (ev : TaskCond k → Bool) (fs : List Frame) (h : debt fs = 1) :
    (∃ a, (next ev fs).2 = .instruction a) ∨
      (debt (next ev fs).1 = 1 ∧ (next ev fs).2 ≠ .idle) := by
  induction fs with
  | nil => simp [debt] at h
  | cons f fs ih =>
    cases f with
    | pending a => exact pending_progress ev a fs
    | body c a b => rw [next, next]; exact pending_progress ev a (.bodyRest c a b :: fs)
    | skip => rw [next]; exact ih h
    | code | after | test | cycle | bodyRest => simp [debt] at h

def instructions : Event → ℕ
  | .instruction _ => 1
  | _ => 0

def idles : Event → ℕ
  | .idle => 1
  | _ => 0

/-- A right-move postlude can attempt a supply without waiting for it.
Each such residual frame is created by a real instruction. -/
def afterDebt : List Frame → ℕ
  | [] => 0
  | .after _ :: fs => 1 + afterDebt fs
  | _ :: fs => afterDebt fs

theorem after_charge (ev : TaskCond k → Bool) {fs gs : List Frame} {w : Event}
    (h : next ev fs = (gs, w)) : afterDebt gs ≤ instructions w + afterDebt fs := by
  have hh : afterDebt (next ev fs).1 ≤ instructions (next ev fs).2 + afterDebt fs := by
    clear h
    induction fs using next.induct (ev := ev) with
    | case1 => simp only [next, afterDebt, instructions]; omega
    | case2 fs ih => rw [next]; simpa only [afterDebt] using ih
    | case3 fs ih => rw [next]; simpa only [afterDebt] using ih
    | case4 a fs ih => rw [next]; simpa only [afterDebt] using ih
    | case5 p q fs ih => rw [next]; simpa only [afterDebt] using ih
    | case6 c p q fs ih => rw [next]; simpa only [afterDebt] using ih
    | case7 c a b fs ih => rw [next]; simpa only [afterDebt] using ih
    | case8 a fs w hw => rw [next, hw]; simp only [afterDebt]; omega
    | case9 a fs hw => rw [next, hw]; simp only [afterDebt, instructions]; omega
    | case10 a fs hw => rw [next, if_pos hw]; simp only [afterDebt, instructions]; omega
    | case11 a fs hw ih => rw [next, if_neg hw]; simp only [afterDebt]; omega
    | case12 c p q fs hw => rw [next, if_pos hw]; simp only [afterDebt]; omega
    | case13 c p q fs hw ih =>
      rw [next, if_neg hw]
      split at ih <;> simpa only [*, afterDebt, Bool.false_eq_true, ↓reduceIte] using ih
    | case14 c a b fs hw => rw [next, if_pos hw]; simp only [afterDebt]; omega
    | case15 c a b fs hw hc =>
      rw [next, if_neg hw, if_pos hc]; simp only [afterDebt, instructions]; omega
    | case16 c a b fs hw hc ih => rw [next, if_neg hw, if_neg hc]; simpa only [afterDebt] using ih
    | case17 c a b fs ih => rw [next]; simpa only [afterDebt] using ih
    | case18 c a b fs ih => rw [next]; simpa only [afterDebt] using ih
  simpa only [h] using hh

theorem idle_charge (ev : TaskCond k → Bool) {fs gs : List Frame} {w : Event}
    (h : next ev fs = (gs, w)) : idles w + debt fs ≤ instructions w + debt gs := by
  by_cases hd : debt fs = 1
  · have hp := debt_progress ev fs hd
    rw [h] at hp
    rcases hp with ⟨a, ha⟩ | ⟨hg, hw⟩
    · cases ha
      simp only [idles, instructions, hd]
      omega
    · cases w <;> simp_all [idles, instructions]
  · have hz : debt fs = 0 := by have hh := debt_le fs; omega
    cases w with
    | idle =>
      have hh := idle_debt ev fs (by rw [h])
      rw [h] at hh
      simp only [idles, instructions, hz, hh]
      omega
    | instruction | feed1 | feed2 | halt => simp [idles, instructions, hz]

/-- info: 'PalPeg.TextFeedPipelineFrameCost.idle_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_charge

end PalPeg.TextFeedPipelineFrameCost
