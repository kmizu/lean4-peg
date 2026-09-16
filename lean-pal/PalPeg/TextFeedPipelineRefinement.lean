import PalPeg.TextFeedPipelineRaw
import PalPeg.VerifierFeedRefinement

/-! Instruction and guard refinement on the genuine pipeline bundle.
Arrival and feeding retain the ideal GS state; verifier calls advance it
by their ordinary ideal instruction. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineRefinement
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed
open PalPeg.VerifierFeedRaw PalPeg.VerifierFeedRawPrimitive PalPeg.VerifierFeedRefinement

variable {k : ℕ} {Terminal : Type}

theorem eval_verifier (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (M : VMachine' k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (c : GSVProg.Cond10) :
    taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus) (.inr (.inr (.inl c))) =
      GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => (GSVProg.vTS M.vt j).focus) := by
  apply congrArg (GSVProg.condOf10 e.endSym e.mark e.startSym c)
  funext j
  fin_cases j <;> rfl

theorem match_guard {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (hw : taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (.inr (.inr (.inr .scanWait))) = false) :
    taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (verifyCond (.inl .matchOk)) =
      GSVProg.condOf10 e.endSym e.mark e.startSym .matchOk (fun j => (GSVProg.vTS I j).focus) := by
  change decide (Tape.read (M.vt.1 GSTapes.tP) ≠ e.endSym ∧
    Tape.read (M.vt.1 GSTapes.tT) = e.blank) = false at hw
  rw [verifyCond, eval_verifier]
  exact h.condition hn .matchOk (match_ready_of_nowait hb hn h.feed (decide_eq_false_iff_not.mp hw))

theorem comp_guard {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {M : VMachine' k} {I : GSVTapes.VTapes' k}
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Refines e Text n M I i₁ i₂) (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (hw : taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (.inr (.inr (.inr .verifyWait))) = false) :
    taskEval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ M aux old dir j).focus)
      (verifyCond (.inl .compOk)) =
      GSVProg.condOf10 e.endSym e.mark e.startSym .compOk (fun j => (GSVProg.vTS I j).focus) := by
  change decide (Tape.read M.vt.2.U ≠ e.endSym ∧ Tape.read M.vt.2.Txt2 = e.blank) = false at hw
  rw [verifyCond, eval_verifier]
  exact h.condition hn .compOk (comp_ready_of_nowait hb hn h.feed (decide_eq_false_iff_not.mp hw))

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
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k)) (a : GSVProg.Act10)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (s, some (.inr (.inr (.inl a)))))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) (hsa : Safe a M i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedPrimitive.effect e a M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      Refines e Text n M' (stepTapes e a I)
        (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  obtain ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, _⟩ :=
    TextFeedPipelineRaw.run_instruction hc hmb leftSym R rate x hb hz s a hs
      qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf.feed hsa
  exact ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hf.effect hmb hblank hmark hn hsa⟩

theorem run_feed1 {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (feedHead :: s))
    (hcell : (x.2 12).focus = e.blank)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : Refines e Text n M I i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedRaw.fill1 e.blank e.mark M
    ∃ qt₁' m₁', y.2 = tapes e qt₁' m₁' qt₂ m₂ M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂ m₂ M'.Q2 ∧
      Refines e Text n M' I i₁ i₂ ∧
      (Tape.read (M'.vt.1 GSTapes.tT) = e.blank ↔ i₁ = n) := by
  obtain ⟨qt₁', m₁', ht, hby, hcy, hr₁, hr₂, _, hw⟩ :=
    TextFeedPipelineRaw.run_feed1 hc hmb leftSym R rate x hb hz s hs hcell
      qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf.feed
  exact ⟨qt₁', m₁', ht, hby, hcy, hr₁, hr₂, hf.fill1 hmb hblank hmark hn, hw⟩

theorem run_arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (a : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux a dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ} {I : GSVTapes.VTapes' k}
    (ham : a ≠ e.mark) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hf : Refines e Text n M I i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := varrive' e.blank e.mark a M
    ∃ qt₁' m₁' qt₂' m₂', y.2 = tapes e qt₁' m₁' qt₂' m₂' M' aux a dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2 = x.1.1.2.2 ∧ y.1.1.2.1 = false ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      Refines e Text (n + 1) M' I i₁ i₂ := by
  obtain ⟨qt₁', m₁', qt₂', m₂', ht, hby, hcy, hfy, hr₁, hr₂, _⟩ :=
    TextFeedPipelineRaw.run_arrival hc hmb leftSym R rate x hb hz hfirst
      qt₁ m₁ qt₂ m₂ M aux a dir hx h₁ h₂ ham hn ha hf.feed
  exact ⟨qt₁', m₁', qt₂', m₂', ht, hby, hcy, hfy, hr₁, hr₂, hf.arrive hmb hn ha⟩

/-- info: 'PalPeg.TextFeedPipelineRefinement.match_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms match_guard

/-- info: 'PalPeg.TextFeedPipelineRefinement.comp_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp_guard

/-- info: 'PalPeg.TextFeedPipelineRefinement.run_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_instruction

/-- info: 'PalPeg.TextFeedPipelineRefinement.run_feed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed1

/-- info: 'PalPeg.TextFeedPipelineRefinement.run_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_arrival

end PalPeg.TextFeedPipelineRefinement
