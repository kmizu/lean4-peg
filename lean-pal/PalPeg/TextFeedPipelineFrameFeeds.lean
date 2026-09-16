import PalPeg.TextFeedPipelineGuardAgreement
import PalPeg.TextFeedPipelineFrameSafety
import PalPeg.TextFeedPipelineSourceSafety

/-! Both actual queue feeds preserve the ideal tape state while advancing
the typed residual control. Q1's blank guard is derived from the source. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrameFeeds
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

theorem run_feed1 {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (fs gs : List Frame) (s : Stack (TaskAct k) (TaskCond k))
    (hctrl : x.1.1.2.2.val = render fs ++ s)
    (hnext : next (taskEval e (fun j => (x.2 j).focus)) fs = (gs, .feed1))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs) (erase gs) ∧
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedRaw.fill1 e.blank e.mark M
    ∃ qt₁' m₁', y.2 = tapes e qt₁' m₁' qt₂ m₂ M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = render gs ++ s ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂ m₂ M'.Q2 ∧
      Refines e Text n M' I i₁ i₂ ∧ SourceSafe e leftSym rate y.1.1.2.2 ∧
      (Tape.read (M'.vt.1 GSTapes.tT) = e.blank ↔ i₁ = n) := by
  have hi := next_erase_physical qt₁ m₁ qt₂ m₂ aux old dir hf hmb hblank hmark hn fs
  dsimp only at hi
  rw [← hx, hnext] at hi
  refine ⟨hi, ?_⟩
  have hcell := TextFeedPipelineFrameSafety.next_feed1_blank e (fun j => (x.2 j).focus) fs
    (congrArg Prod.snd hnext)
  have he : taskEval e (fun j => (x.2 j).focus) (.inr (.inl .blankText)) = true := decide_eq_true hcell
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (feedHead :: (render gs ++ s)) := by
    rw [hctrl, next_render_suffix, hnext]
    simp only [feedHead, stepStack_ite, he, if_true, stepStack_act]
    rfl
  obtain ⟨qt₁', m₁', ht, hb', hctrl', h₁', h₂', hf', hw⟩ :=
    TextFeedPipelineRefinement.run_feed1 (Terminal := Terminal) hc hmb leftSym R rate x hb hz
      (render gs ++ s) hs hcell qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf
  exact ⟨qt₁', m₁', ht, hb', hctrl', h₁', h₂', hf', run_safe e leftSym R rate x hsource, hw⟩

theorem run_feed2 {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (fs gs : List Frame) (s : Stack (TaskAct k) (TaskCond k))
    (hctrl : x.1.1.2.2.val = render fs ++ s)
    (hnext : next (taskEval e (fun j => (x.2 j).focus)) fs = (gs, .feed2))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs) (erase gs) ∧
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = render gs ++ s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      Refines e Text n M' I i₁ i₂ ∧ SourceSafe e leftSym rate y.1.1.2.2 := by
  have hi := next_erase_physical qt₁ m₁ qt₂ m₂ aux old dir hf hmb hblank hmark hn fs
  dsimp only at hi
  rw [← hx, hnext] at hi
  refine ⟨hi, ?_⟩
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (render gs ++ s, some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
    rw [hctrl, next_render_suffix, hnext]
    rfl
  have hr := TextFeedPipelineSourceSafety.run_instruction (Terminal := Terminal) hc hmb leftSym R rate x
    hsource hb hz (render gs ++ s) (GSVProg.tX, true, .stay) hs
    qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf
  simpa only [stepTapes_stay, nextIndex, moveIndex, ite_self] using hr

/-- info: 'PalPeg.TextFeedPipelineFrameFeeds.run_feed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed1

/-- info: 'PalPeg.TextFeedPipelineFrameFeeds.run_feed2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed2

end PalPeg.TextFeedPipelineFrameFeeds
