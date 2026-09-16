import PalPeg.TextFeedPipelineRefinement
import PalPeg.ProgLangControlSteps

/-! Guard barriers retain the actual continuation while waiting and dispatch
the branch on the very observation that releases the barrier. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineBranch
open PalPeg.ProgLang PalPeg.TextFeedPipelineControl

variable {k : ℕ}

def Waiting (ev : TaskCond k → Bool) : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond → Bool
  | .inl .matchOk => ev (.inr (.inr (.inr .scanWait)))
  | .inl .compOk => ev (.inr (.inr (.inr .verifyWait)))
  | _ => false

theorem barrier_return (ev : TaskCond k → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (s : Stack (TaskAct k) (TaskCond k))
    (hw : Waiting ev c = false) :
    stepStack ev (beforeCond c :: s) = stepStack ev s := by
  cases c with
  | inl c => cases c <;> simp_all [Waiting, beforeCond]
  | inr c => cases c <;> simp [beforeCond]

/-- No extra source call separates the release observation and branch selection. -/
theorem branch_dispatch (ev : TaskCond k → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (p q : GSVProgZLoop.DProg)
    (s : Stack (TaskAct k) (TaskCond k)) (hw : Waiting ev c = false) :
    stepStack ev (liftVerify (.ite c p q) :: s) =
      stepStack ev ((if ev (verifyCond c) then liftVerify p else liftVerify q) :: s) := by
  rw [liftVerify, stepStack_seq, barrier_return ev c _ hw, stepStack_ite]

theorem branch_refines (ev : TaskCond k → Bool)
    (ideal : (GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (p q : GSVProgZLoop.DProg)
    (s : Stack (TaskAct k) (TaskCond k)) (hw : Waiting ev c = false)
    (hc : ev (verifyCond c) = ideal c) :
    stepStack ev (liftVerify (.ite c p q) :: s) =
      stepStack ev (liftVerify (if ideal c then p else q) :: s) := by
  rw [branch_dispatch ev c p q s hw, hc]
  cases ideal c <;> rfl

/-- The emitted idle commits the loop choice. Its residual contains the
mandatory action, rather than retesting the guard after an arrival. -/
theorem loop_commit (ev : TaskCond k → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (a : GSVProg.Act10 ⊕ Bool)
    (b : GSVProgZLoop.DProg) (s : Stack (TaskAct k) (TaskCond k))
    (hw : Waiting ev c = false) (hc : ev (verifyCond c) = true) :
    stepStack ev (liftVerify (.loop c a b) :: s) =
      (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c)) ::
        .loop (verifyCond c) (.inr (.inl .idle))
          (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c))) :: s,
        some (.inr (.inl .idle))) := by
  rw [liftVerify, stepStack_seq, barrier_return ev c _ hw, stepStack_loop, hc]
  rfl

theorem loop_exit (ev : TaskCond k → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (a : GSVProg.Act10 ⊕ Bool)
    (b : GSVProgZLoop.DProg) (s : Stack (TaskAct k) (TaskCond k))
    (hw : Waiting ev c = false) (hc : ev (verifyCond c) = false) :
    stepStack ev (liftVerify (.loop c a b) :: s) = stepStack ev s := by
  rw [liftVerify, stepStack_seq, barrier_return ev c _ hw, stepStack_loop, hc]
  rfl

/-- The compiled idle is matched by a pure ideal control transition,
not by prematurely executing the mandatory ideal instruction. -/
theorem loop_commit_refines (ev : TaskCond k → Bool)
    (ideal : (GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (a : GSVProg.Act10 ⊕ Bool)
    (b : GSVProgZLoop.DProg) (s : Stack (TaskAct k) (TaskCond k))
    (r : Stack (GSVProg.Act10 ⊕ Bool) (GSVProg.Cond10 ⊕ GSVProgZLoop.DCond))
    (hw : Waiting ev c = false) (hg : ev (verifyCond c) = ideal c) (hc : ideal c = true) :
    stepStack ev (liftVerify (.loop c a b) :: s) =
      (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c)) ::
        .loop (verifyCond c) (.inr (.inl .idle))
          (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c))) :: s,
        some (.inr (.inl .idle))) ∧
    ProgLangControlSteps.Star ideal (.loop c a b :: r) (.act a :: b :: .loop c a b :: r) :=
  ⟨loop_commit ev c a b s hw (hg.trans hc),
    ProgLangControlSteps.Star.single (.loop_yes c a b r hc)⟩

theorem scan_wait (ev : TaskCond k → Bool) (s : Stack (TaskAct k) (TaskCond k))
    (hw : ev (.inr (.inr (.inr .scanWait))) = true) :
    stepStack ev (beforeCond (.inl .matchOk) :: s) =
      (.skip :: beforeCond (.inl .matchOk) :: s, some (.inr (.inl .supply))) := by
  simp [beforeCond, hw]

theorem comp_wait (ev : TaskCond k → Bool) (s : Stack (TaskAct k) (TaskCond k))
    (hw : ev (.inr (.inr (.inr .verifyWait))) = true) :
    stepStack ev (beforeCond (.inl .compOk) :: s) =
      (.skip :: beforeCond (.inl .compOk) :: s,
        some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
  simp [beforeCond, hw]

/-- Coherence of the real observation, not a premise about arbitrary Boolean
valuations: a scan-barrier supply can only target a blank text cell. -/
theorem scan_wait_blank (e : PalPeg.TextFeedControl.Env k) (σ : Fin 39 → Fin k)
    (hw : taskEval e σ (.inr (.inr (.inr .scanWait))) = true) :
    σ 12 = e.blank := (of_decide_eq_true hw).2

theorem comp_wait_blank (e : PalPeg.TextFeedControl.Env k) (σ : Fin 39 → Fin k)
    (hw : taskEval e σ (.inr (.inr (.inr .verifyWait))) = true) :
    σ 20 = e.blank := (of_decide_eq_true hw).2

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed PalPeg.VerifierFeedRefinement

/-- The real comparison branch selects exactly the ideal GS branch, with
the existing source suffix intact. The ideal tape is only a proof witness. -/
theorem match_dispatch {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (p q : GSVProgZLoop.DProg) (s : Stack (TaskAct k) (TaskCond k))
    (hw : taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (.inr (.inr (.inr .scanWait))) = false) :
    let ev := taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
    stepStack ev (liftVerify (.ite (.inl .matchOk) p q) :: s) =
      stepStack ev (liftVerify (if GSVProg.condOf10 e.endSym e.mark e.startSym .matchOk
        (fun j => (GSVProg.vTS I j).focus) then p else q) :: s) := by
  dsimp only
  apply branch_refines (taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)) (fun _ => GSVProg.condOf10 e.endSym e.mark e.startSym .matchOk
    (fun j => (GSVProg.vTS I j).focus)) (.inl .matchOk) p q s hw
  exact TextFeedPipelineRefinement.match_guard qt₁ m₁ qt₂ m₂ aux old dir h hb hn hw

theorem comp_dispatch {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (p q : GSVProgZLoop.DProg) (s : Stack (TaskAct k) (TaskCond k))
    (hw : taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (.inr (.inr (.inr .verifyWait))) = false) :
    let ev := taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
    stepStack ev (liftVerify (.ite (.inl .compOk) p q) :: s) =
      stepStack ev (liftVerify (if GSVProg.condOf10 e.endSym e.mark e.startSym .compOk
        (fun j => (GSVProg.vTS I j).focus) then p else q) :: s) := by
  dsimp only
  apply branch_refines (taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)) (fun _ => GSVProg.condOf10 e.endSym e.mark e.startSym .compOk
    (fun j => (GSVProg.vTS I j).focus)) (.inl .compOk) p q s hw
  exact TextFeedPipelineRefinement.comp_guard qt₁ m₁ qt₂ m₂ aux old dir h hb hn hw

/-- info: 'PalPeg.TextFeedPipelineBranch.branch_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branch_refines

/-- info: 'PalPeg.TextFeedPipelineBranch.loop_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_commit

end PalPeg.TextFeedPipelineBranch
