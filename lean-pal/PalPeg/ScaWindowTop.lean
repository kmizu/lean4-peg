import PalPeg.ScaWindowFault
import PalPeg.ScaTyped

/-!
# `PAL ∈ PEG` through the window controller

The whole route with its remaining obligations as hypotheses:
* the answering stage's matcher reports the reversed-pattern occurrence (`hmatch`),
* its `middle` flag reports the middle palindrome (`hmiddle`),
* the controller's `advance`/`consume` checks never fire (`hclean`),
* the workers never fault (`hworkers`),
* a scaffold automaton over finite types accepts what the controller accepts (`hencode`).
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowTop
open PalPeg.ScaWindowPal PalPeg.ScaWindowSchedule PalPeg.ScaWindowOutput PalPeg.ScaWindowFault

section
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

theorem globalFault_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2))
    (hclean : ∀ (u : List (Fin 2)) (a : Fin 2), u ++ [a] <+: w →
      ctlViolation (run mOps fOps m0 f0 u) = false)
    (hworkers : ∀ i : Fin 2, mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
      fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false) :
    globalFault mOps fOps (run mOps fOps m0 f0 w) = false := by
  unfold globalFault
  rw [fault_run mOps fOps m0 f0 w hclean, (hworkers 0).1, (hworkers 1).1, (hworkers 0).2,
    (hworkers 1).2]
  rfl

/-- **The window controller recognizes `PAL`**, given the worker and timing obligations. -/
theorem accepts_iff_pal (m0 : Wm) (f0 : Wf)
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (mOps.output ((run mOps fOps m0 f0 w).matchers (idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hmiddle : ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))))
    (hclean : ∀ (u : List (Fin 2)) (a : Fin 2), ctlViolation (run mOps fOps m0 f0 u) = false)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
        fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false)
    (w : List (Fin 2)) : Accepts mOps fOps m0 f0 w ↔ w ∈ PalPeg.PAL :=
  window_correct mOps fOps m0 f0 hmatch hmiddle
    (fun w => globalFault_run mOps fOps m0 f0 w (fun u a _ => hclean u a) (hworkers w)) w

/-- **`PAL ∈ PEG`** from the controller's obligations and a scaffold automaton that accepts what
the controller accepts. -/
theorem pal_in_peg (m0 : Wm) (f0 : Wf)
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (mOps.output ((run mOps fOps m0 f0 w).matchers (idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hmiddle : ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))))
    (hclean : ∀ (u : List (Fin 2)) (a : Fin 2), ctlViolation (run mOps fOps m0 f0 u) = false)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
        fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false)
    {S L : Type} [Fintype S] [Fintype L] {degree radius : ℕ}
    (A : PalPeg.ScaTyped.Typed (Fin 2) S L degree radius)
    (hencode : ∀ w, A.Accepts w ↔ Accepts mOps fOps m0 f0 w) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.ScaTyped.pal_in_peg_of_typed A fun w =>
    (hencode w).trans (accepts_iff_pal mOps fOps m0 f0 hmatch hmiddle hclean hworkers w)

end

/-- info: 'PalPeg.ScaWindowTop.pal_in_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg

end PalPeg.ScaWindowTop
