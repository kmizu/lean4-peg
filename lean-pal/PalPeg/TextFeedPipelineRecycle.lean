import PalPeg.ProgramRecycle
import PalPeg.TextFeedPipelineBirthBuild

set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.TextFeedPipelineRecycle
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.PatternProg
open PalPeg.TextFeedControl PalPeg.TextFeedInit

variable {k : ℕ}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

def cleared (blank : Fin k) (T : Fin 39 → STape (Fin k)) (m : ℕ) : Fin 39 → STape (Fin k) :=
  ((ProgramRecycle.commands m).foldl (ProgramRecycle.machine blank (by decide)).sRound ⟨(), T⟩).tape

noncomputable def rebuilt (e : Env k) (leftSym : Fin k) (T : Fin 39 → STape (Fin k))
    (m : ℕ) (w : List (Fin k)) : Fin 39 → STape (Fin k) :=
  ((TextFeedPipelineBirthBuild.commands w).foldl (TextFeedPipelineBirthBuild.machine e leftSym).sRound
    ⟨(), cleared e.blank T m⟩).tape

/-- Recycling does not require the previous stage to leave stack-shaped tapes.
The movement bound suffices, and finite blank padding is retained safely. -/
theorem rebuilt_seed (e : Env k) (leftSym : Fin k) (T : Fin 39 → STape (Fin k))
    (m : ℕ) (w : List (Fin k)) (h : ∀ j, MiddleClear.Near e.blank (ProgramRecycle.view (T j)) m) :
    ∀ j, STape.BlankEq e.blank (rebuilt e leftSym T m w j)
      (TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 j) := by
  have hc : ConfigBlankEq e.blank (⟨(), cleared e.blank T m⟩ : SConfig Unit (Fin k) 39)
      ⟨(), blankBundle e.blank 39⟩ :=
    ⟨rfl, ProgramRecycle.reset e.blank (by decide) T m h⟩
  have hh := (TextFeedPipelineBirthBuild.machine e leftSym).runFrom_blankEq
    (TextFeedPipelineBirthBuild.commands w) hc
  intro j
  have ht := hh.2 j
  change STape.BlankEq e.blank (rebuilt e leftSym T m w j)
    (((TextFeedPipelineBirthBuild.machine e leftSym).srun
      (TextFeedPipelineBirthBuild.commands w)).tape j) at ht
  rw [TextFeedPipelineBirthBuild.build_machine] at ht
  exact ht

noncomputable def start (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (T : Fin 39 → STape (Fin k)) (m : ℕ) (w : List (Fin k)) (L : ℕ) :
    TextFeedPipelineOutputPrepFinish.Config e leftSym R rate :=
  ⟨((TextFeedPipelineOutput.initial e leftSym R rate, 0), 0), rebuilt e leftSym T m (w.take L)⟩

theorem start_blankEq (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (T : Fin 39 → STape (Fin k)) (m : ℕ) (w : List (Fin k)) (L : ℕ)
    (hw : L ≤ w.length) (h : ∀ j, MiddleClear.Near e.blank (ProgramRecycle.view (T j)) m) :
    ConfigBlankEq e.blank (start e leftSym R rate T m w L)
      (TextFeedPipelineOutputBirth.start e leftSym R rate w L 0) := by
  refine ⟨rfl, ?_⟩
  intro j
  have hh := rebuilt_seed e leftSym T m (w.take L) h j
  simpa only [start, TextFeedPipelineOutputBirth.start, List.length_take, Nat.min_eq_left hw,
    ← TextFeedPipelineOutputBirth.seed_take] using hh

theorem future_output {Terminal : Type} (e : Env k) (leftSym : Fin k)
    (enc : Terminal → Fin k) (R rate : ℕ) (T : Fin 39 → STape (Fin k)) (m : ℕ)
    (w : List (Fin k)) (L : ℕ) (hw : L ≤ w.length)
    (h : ∀ j, MiddleClear.Near e.blank (ProgramRecycle.view (T j)) m) (input : List Terminal) :
    let M := TextFeedPipelineOutput.machine e leftSym enc R rate
    M.accepting (input.foldl M.sRound (start e leftSym R rate T m w L)).state =
      M.accepting (input.foldl M.sRound (TextFeedPipelineOutputBirth.start e leftSym R rate w L 0)).state :=
  (TextFeedPipelineOutput.machine e leftSym enc R rate).accepting_runFrom_blankEq input
    (start_blankEq e leftSym R rate T m w L hw h)

/-- info: 'PalPeg.TextFeedPipelineRecycle.future_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms future_output

end PalPeg.TextFeedPipelineRecycle
