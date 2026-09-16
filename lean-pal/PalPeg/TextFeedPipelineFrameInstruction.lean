import PalPeg.TextFeedPipelineGuardAgreement
import PalPeg.TextFeedPipelineSourceSafety

/-! A compiled residual instruction advances both the real tapes and ideal
GS control/state. The actual caller and source-safety certificate survive. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrameInstruction
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier
open PalPeg.VerifierFeed PalPeg.VerifierFeedRawPrimitive PalPeg.VerifierFeedRefinement
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineGuardAgreement
open PalPeg.TextFeedPipelineSourceSafety
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
attribute [local irreducible] ProgLangBank.runChunk

theorem run_instruction {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (fs gs : List Frame) (s : Stack (TaskAct k) (TaskCond k)) (a : GSVProg.Act10)
    (hctrl : x.1.1.2.2.val = render fs ++ s)
    (hnext : next (taskEval e (fun j => (x.2 j).focus)) fs = (gs, .instruction (.inl a)))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs) (.act (.inl a) :: erase gs) ∧
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedPrimitive.effect e a M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = render gs ++ s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      Refines e Text n M' (stepTapes e a I)
        (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) ∧
      SourceSafe e leftSym rate y.1.1.2.2 := by
  have hi := next_erase_physical qt₁ m₁ qt₂ m₂ aux old dir hf hmb hblank hmark hn fs
  dsimp only at hi
  rw [← hx, hnext] at hi
  refine ⟨hi, ?_⟩
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (render gs ++ s, some (.inr (.inr (.inl a)))) := by
    rw [hctrl, next_render_suffix, hnext]
    rfl
  exact TextFeedPipelineSourceSafety.run_instruction hc hmb leftSym R rate x hsource hb hz
    (render gs ++ s) a hs qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf

/-- info: 'PalPeg.TextFeedPipelineFrameInstruction.run_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_instruction

end PalPeg.TextFeedPipelineFrameInstruction
