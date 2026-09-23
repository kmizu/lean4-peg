import PalPeg.ScaWindowOutput

/-!
# The window controller's own faults

A tick adds to the controller's fault the two stages' `advance` violations (a release while a
batch is still pending), the two stages' `consume` violations (answering with an empty result
stack), and the check that exactly one stage answers from four letters on. The last never fires,
by the schedule. The first two are timing facts about the flag workers and are named `ctlViolation`.
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowFault
open PalPeg.ScaWindowPal PalPeg.ScaWindowSchedule PalPeg.ScaWindowOutput

section
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

/-- The stages after this tick's `advance`, before the workers run. -/
def advanced (s : PalState Wm Wf) (i : Fin 2) : StageState :=
  (advance (s.stages i) (birthOf s && s.slot == i) s.power).1

/-- The violations a tick may add besides the exactly-one check: `advance` and `consume`. -/
def ctlViolation (s : PalState Wm Wf) : Bool :=
  (advance (s.stages 0) (birthOf s && s.slot == 0) s.power).2 ||
  (advance (s.stages 1) (birthOf s && s.slot == 1) s.power).2 ||
  (consume (advanced s 0)).2 || (consume (advanced s 1)).2

/-- The exactly-one check of a tick, on the stages the tick leaves. -/
def exactlyOneViolation (s t : PalState Wm Wf) : Bool :=
  (incSmall s.small).val == 4 &&
    !((answering (t.stages 0) || answering (t.stages 1)) &&
      !(answering (t.stages 0) && answering (t.stages 1)))

theorem birth_eq (s : PalState Wm Wf) :
    (s.powerReady && (if s.powerReady then s.nextBirth.pred else s.nextBirth) == 0) = birthOf s := by
  cases h : s.powerReady <;> simp [birthOf, h]

theorem tick_fault (a : Fin 2) (s : PalState Wm Wf) :
    (tick mOps fOps s a).fault =
      (s.fault || ctlViolation s || exactlyOneViolation s (tick mOps fOps s a)) := by
  simp only [tick, stageRound, ctlViolation, advanced, exactlyOneViolation, birth_eq]
  simp only [Function.update_self, ne_eq, Fin.zero_eq_one_iff, Nat.succ_ne_self,
    not_false_eq_true, Function.update_of_ne, if_true, if_false]
  cases s.fault <;> simp [Bool.or_assoc]

/-- **The exactly-one check never fires along a run.** -/
theorem exactlyOne_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (a : Fin 2) :
    exactlyOneViolation (run mOps fOps m0 f0 w) (run mOps fOps m0 f0 (w ++ [a])) = false := by
  unfold exactlyOneViolation
  have hsmall := small_run mOps fOps m0 f0 w
  rcases Nat.lt_or_ge (w.length + 1) 4 with hlt | hge
  · have : ((incSmall (run mOps fOps m0 f0 w).small).val == 4) = false := by
      simp only [incSmall, hsmall, beq_eq_false_iff_ne]; omega
    rw [this, Bool.false_and]
  · have h4 : 4 ≤ (w ++ [a]).length := by simp; omega
    obtain ⟨-, hans, hnot, -⟩ := answering_run mOps fOps m0 f0 (w ++ [a]) h4
    have hne := idx_pred_ne (k := Nat.log 2 (w ++ [a]).length)
      (by have := (answering_run mOps fOps m0 f0 (w ++ [a]) h4).1; omega)
    generalize idx (Nat.log 2 (w ++ [a]).length) = i at hans hnot hne
    generalize idx (Nat.log 2 (w ++ [a]).length - 1) = j at hans hnot hne
    fin_cases i <;> fin_cases j <;> simp_all

/-- **The controller's fault is exactly the `advance`/`consume` violations along the run.** -/
theorem fault_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2))
    (hclean : ∀ (u : List (Fin 2)) (a : Fin 2), u ++ [a] <+: w →
      ctlViolation (run mOps fOps m0 f0 u) = false) :
    (run mOps fOps m0 f0 w).fault = false := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [run_append, tick_fault, ih (fun u b h => hclean u b (h.trans (List.prefix_append _ _))),
      hclean w a (List.prefix_refl _), ← run_append, exactlyOne_run]
    rfl

end
end PalPeg.ScaWindowFault
