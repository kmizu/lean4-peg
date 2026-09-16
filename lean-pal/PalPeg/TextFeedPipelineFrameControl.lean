import PalPeg.TextFeedPipelineGuardAgreement
import PalPeg.TextFeedPipelineSourceSafety

/-! Loop-commit idle and direction-write events in the actual pipeline.
Idle may maintain Q1 physically, while preserving its logical contents. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrameControl
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier PalPeg.TextFeedPipelineHandoff
open PalPeg.TextFeedPipelineBank PalPeg.VerifierFeed PalPeg.VerifierFeedRefinement
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

theorem run_idle {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (fs gs : List Frame) (s : Stack (TaskAct k) (TaskCond k))
    (hctrl : x.1.1.2.2.val = render fs ++ s)
    (hnext : next (taskEval e (fun j => (x.2 j).focus)) fs = (gs, .idle))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs) (erase gs) ∧
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁', y.2 = tapes e qt₁' m₁' qt₂ m₂ M aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = render gs ++ s ∧
      Ready e.blank e.mark qt₁' m₁' M.Q1 ∧ Ready e.blank e.mark qt₂ m₂ M.Q2 ∧
      Refines e Text n M I i₁ i₂ ∧ SourceSafe e leftSym rate y.1.1.2.2 := by
  have hi := next_erase_physical qt₁ m₁ qt₂ m₂ aux old dir hf hmb hblank hmark hn fs
  dsimp only at hi
  rw [← hx, hnext] at hi
  refine ⟨hi, ?_⟩
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (render gs ++ s, some (.inr (.inl .idle))) := by
    rw [hctrl, next_render_suffix, hnext]
    rfl
  obtain ⟨ticks, qt₁', m₁', hn', ⟨tr, he, ht, hlen⟩, hr⟩ :=
    TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb .idle (prefixModel M)
      qt₁ m₁ qt₂ m₂ M.vt.2.Txt2 aux old dir h₁
  have he' := exec_prefix he
  change Exec _ _ _ (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) tr at he'
  rw [← hx] at he'
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz (render gs ++ s)
    (.inr (.inl .idle)) hs tr he' (by omega)
  change applyTrace e.blank (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) tr =
    tapes e qt₁' m₁' qt₂ m₂ M aux old dir at ht
  rw [← hx] at ht
  exact ⟨qt₁', m₁', hyt.trans ht, hby, hcy, hr, h₂, hf, run_safe e leftSym R rate x hsource⟩

theorem writeDir_tapes (e : Env k) (up : Bool)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    writeDir e up (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) =
      tapes e qt₁ m₁ qt₂ m₂ M aux old
        (dir.applyAction e.blank (GSVProgZLoop.dirSymbol e.blank e.mark up, .stay)) := by
  funext j
  fin_cases j <;> rfl

theorem run_direction {e : Env k} (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (fs gs : List Frame) (s : Stack (TaskAct k) (TaskCond k)) (up : Bool)
    (hctrl : x.1.1.2.2.val = render fs ++ s)
    (hnext : next (taskEval e (fun j => (x.2 j).focus)) fs = (gs, .instruction (.inr up)))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    ProgLangControlSteps.Star (idealEval e I dir) (erase fs) (.act (.inr up) :: erase gs) ∧
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    y.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old
        (dir.applyAction e.blank (GSVProgZLoop.dirSymbol e.blank e.mark up, .stay)) ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = render gs ++ s ∧
      Refines e Text n M I i₁ i₂ ∧ SourceSafe e leftSym rate y.1.1.2.2 := by
  have hi := next_erase_physical qt₁ m₁ qt₂ m₂ aux old dir hf hmb hblank hmark hn fs
  dsimp only at hi
  rw [← hx, hnext] at hi
  refine ⟨hi, ?_⟩
  have hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (render gs ++ s, some (.inr (.inr (.inr up)))) := by
    rw [hctrl, next_render_suffix, hnext]
    rfl
  obtain ⟨ht, hb', hs', _, _⟩ := TextFeedPipelineVerifier.run_direction (Terminal := Terminal)
    e leftSym R rate x hb hz (render gs ++ s) up hs
  rw [hx, writeDir_tapes] at ht
  exact ⟨ht, hb', hs', hf, run_safe e leftSym R rate x hsource⟩

/-- info: 'PalPeg.TextFeedPipelineFrameControl.run_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_idle

/-- info: 'PalPeg.TextFeedPipelineFrameControl.run_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_direction

end PalPeg.TextFeedPipelineFrameControl
