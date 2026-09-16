import PalPeg.TextFeedPipelineObservations

/-! Source observations across genuine input frames, starting at the actual
all-blank machine. The trace records only observations extracted from those
executions, rather than accepting an unconstrained external oracle. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInputObservations
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineObservations PalPeg.ProgLangWait
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

noncomputable def frameObservations (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (word : List Terminal) (a : Terminal) : List (TaskCond k → Bool) :=
  let y := (machine e leftSym enc R rate).srun word
  observations (Terminal := Terminal) e leftSym R rate (R + 1)
    (y.state.1.1, arriveA e.blank (DualQueueShared.capture enc) (some a) y.tape)

inductive FrameTrace (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) :
    List Terminal → List (TaskCond k → Bool) → Prop where
  | nil : FrameTrace e leftSym enc R rate [] []
  | snoc {word : List Terminal} {es : List (TaskCond k → Bool)}
      (h : FrameTrace e leftSym enc R rate word es) (a : Terminal) :
      FrameTrace e leftSym enc R rate (word ++ [a])
        (es ++ frameObservations e leftSym enc R rate word a)

theorem frame_observe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) (a : Terminal) :
    ((machine e leftSym enc R rate).srun (word ++ [a])).state.1.1.1.2.2.val =
      (observe (frameObservations e leftSym enc R rate word a)
        ((machine e leftSym enc R rate).srun word).state.1.1.1.2.2.val).1 := by
  obtain ⟨h₁, h₂, _⟩ := TextFeedPipelineSourceSafety.machine_run_safe e leftSym enc R rate word
  let y := (machine e leftSym enc R rate).srun word
  have hy : (machine e leftSym enc R rate).srun word =
      { state := ((y.state.1.1, 0), 0), tape := y.tape } := by
    change y = _
    have he : y.state = ((y.state.1.1, 0), 0) := Prod.ext (Prod.ext rfl h₁) h₂
    rw [← he]
  rw [StructuredMachine.srun_append_singleton, hy, machine_round]
  exact run_observe e leftSym R rate (R + 1)
    (y.state.1.1, arriveA e.blank (DualQueueShared.capture enc) (some a) y.tape)

/-- Every finite input has its genuine observation trace, and interpreting
that trace from the initial source recovers the exact actual continuation. -/
theorem word_observe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) :
    ∃ es, FrameTrace e leftSym enc R rate word es ∧
      ((machine e leftSym enc R rate).srun word).state.1.1.1.2.2.val =
        (observe es [task e leftSym rate]).1 ∧ es.length ≤ (R + 1) * word.length := by
  induction word using List.reverseRecOn with
  | nil => exact ⟨[], .nil, rfl, Nat.le_refl 0⟩
  | append_singleton word a ih =>
    obtain ⟨es, htrace, hs, hn⟩ := ih
    refine ⟨es ++ frameObservations e leftSym enc R rate word a, htrace.snoc a, ?_, ?_⟩
    · rw [frame_observe, hs, observe_append]
    · have hf : (frameObservations e leftSym enc R rate word a).length ≤ R + 1 :=
        observations_length e leftSym R rate (R + 1) _
      simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add hn hf

/-- The exposed control-path trace is available for the genuine finite-word
execution too, with its actual residual stack as endpoint. -/
theorem word_control_trace (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) :
    ∃ es as, FrameTrace e leftSym enc R rate word es ∧
      ProgLangControlSteps.Trace es [task e leftSym rate]
        ((machine e leftSym enc R rate).srun word).state.1.1.1.2.2.val as ∧
      es.length ≤ (R + 1) * word.length := by
  obtain ⟨es, hf, hs, hn⟩ := word_observe e leftSym enc R rate word
  refine ⟨es, (observe es [task e leftSym rate]).2, hf, ?_, hn⟩
  rw [hs]
  exact ProgLangControlSteps.trace_observe es [task e leftSym rate]

/-- info: 'PalPeg.TextFeedPipelineInputObservations.word_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms word_observe

end PalPeg.TextFeedPipelineInputObservations
