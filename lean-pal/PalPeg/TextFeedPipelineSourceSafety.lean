import PalPeg.TextFeedPipelineKeep
import PalPeg.TextFeedPipelineRefinement

/-! Safety is derived from the real persistent source, not supplied as
an unproved obligation for each GS instruction. The source invariant is
preserved by every call, including input calls and arbitrary frame contents. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineSourceSafety
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier
open PalPeg.VerifierFeed PalPeg.VerifierFeedRaw PalPeg.VerifierFeedRawPrimitive
open PalPeg.VerifierFeedRefinement

variable {k : ℕ} {Terminal : Type}

def SourceSafe (e : Env k) (leftSym : Fin k) (rate : ℕ) (c : CtrlS (task e leftSym rate)) : Prop :=
  ProgLangGuarded.Invariant (TextFeedPipelineGuarded.Good (k := k)) c.val

theorem start_safe (e : Env k) (leftSym : Fin k) (rate : ℕ) :
    SourceSafe e leftSym rate (startCtrlS (task e leftSym rate)) :=
  ProgLangGuarded.Invariant.of_certified (TextFeedPipelineKeep.task_safe e leftSym rate)

theorem source_step_safe {e : Env k} {leftSym : Fin k} {rate : ℕ}
    {c : CtrlS (task e leftSym rate)} (h : SourceSafe e leftSym rate c) (ev : TaskCond k → Bool) :
    SourceSafe e leftSym rate (stepCtrlS (task e leftSym rate) ev c) :=
  ProgLangGuarded.Invariant.step h ev

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

theorem run_safe (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (h : SourceSafe e leftSym rate x.1.1.2.2) :
    SourceSafe e leftSym rate
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.2.2 := by
  change SourceSafe e leftSym rate (TextFeedPipelineControl.choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).1.2.2
  unfold TextFeedPipelineControl.choose
  split
  · exact h
  · exact source_step_safe h _

theorem run_iterate_safe (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (h : SourceSafe e leftSym rate x.1.1.2.2) :
    SourceSafe e leftSym rate
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.2 := by
  induction N with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact run_safe e leftSym R rate _ ih

/-- The actual input capture changes tape symbols, not the certified
continuation; all calls in the machine's real input frame preserve safety. -/
theorem machine_round_safe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k)) (a : Terminal)
    (h : SourceSafe e leftSym rate c.1.2.2) :
    let y := (machine e leftSym enc R rate).sRound { state := ((c, 0), 0), tape := T } a
    SourceSafe e leftSym rate y.state.1.1.1.2.2 := by
  rw [machine_round]
  exact run_iterate_safe e leftSym R rate (R + 1)
    (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T) h

/-- Safety for the actual finite machine on every finite input word,
starting from its genuine all-blank initial configuration. -/
theorem machine_run_safe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) :
    let y := (machine e leftSym enc R rate).srun word
    y.state.1.2 = 0 ∧ y.state.2 = 0 ∧ SourceSafe e leftSym rate y.state.1.1.1.2.2 := by
  induction word using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, start_safe e leftSym rate⟩
  | append_singleton word a ih =>
    obtain ⟨h₁, h₂, hs⟩ := ih
    let y := (machine e leftSym enc R rate).srun word
    have hy : (machine e leftSym enc R rate).srun word =
        { state := ((y.state.1.1, 0), 0), tape := y.tape } := by
      change y = _
      have he : y.state = ((y.state.1.1, 0), 0) := Prod.ext (Prod.ext rfl h₁) h₂
      rw [← he]
    rw [StructuredMachine.srun_append_singleton, hy, machine_round]
    exact ⟨rfl, rfl, run_iterate_safe e leftSym R rate (R + 1)
      (y.state.1.1, arriveA e.blank (DualQueueShared.capture enc) (some a) y.tape) hs⟩

/-- The text-preservation and nonblank pre-move facts are consequences
of the selected instruction and its reachable persistent continuation. -/
theorem selected_safe {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hc : SourceSafe e leftSym rate x.1.1.2.2) (a : GSVProg.Act10)
    (hs : (stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val).2 =
      some (.inr (.inr (.inl a))))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length) (hf : RawInv e.blank e.mark Text n M i₁ i₂) :
    Safe a M i₁ i₂ := by
  have hg := ProgLangGuarded.Invariant.selected hc (taskEval e (fun j => (x.2 j).focus)) hs
  apply safe_of_reads hblank hn hf hg.1.1 hg.1.2
  · intro ht hr
    have hread := hg.2.1 ht hr
    rw [hx] at hread
    change decide (Tape.read (M.vt.1 GSTapes.tT) = e.blank) = false at hread
    exact decide_eq_false_iff_not.mp hread
  · intro ht hr
    have hread := hg.2.2 ht hr
    rw [hx] at hread
    change decide (Tape.read M.vt.2.Txt2 = e.blank) = false at hread
    exact decide_eq_false_iff_not.mp hread

/-- A real GS call now refines its ideal instruction without a separate
`Safe a M` premise. SourceSafe is established initially and preserved above. -/
theorem run_instruction {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hsource : SourceSafe e leftSym rate x.1.1.2.2)
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
    (hf : Refines e Text n M I i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedPrimitive.effect e a M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      Refines e Text n M' (stepTapes e a I)
        (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) ∧
      SourceSafe e leftSym rate y.1.1.2.2 := by
  have hsa := selected_safe leftSym R rate x hsource a (congrArg Prod.snd hs)
    qt₁ m₁ qt₂ m₂ M aux old dir hx hblank hn hf.feed
  obtain ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hi⟩ :=
    TextFeedPipelineRefinement.run_instruction hc hmb leftSym R rate x hb hz s a hs
      qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf hsa
  exact ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hi, run_safe e leftSym R rate x hsource⟩

/-- info: 'PalPeg.TextFeedPipelineSourceSafety.start_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms start_safe

/-- info: 'PalPeg.TextFeedPipelineSourceSafety.machine_round_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round_safe

/-- info: 'PalPeg.TextFeedPipelineSourceSafety.selected_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_safe

/-- info: 'PalPeg.TextFeedPipelineSourceSafety.machine_run_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_run_safe

/-- info: 'PalPeg.TextFeedPipelineSourceSafety.run_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_instruction

end PalPeg.TextFeedPipelineSourceSafety
