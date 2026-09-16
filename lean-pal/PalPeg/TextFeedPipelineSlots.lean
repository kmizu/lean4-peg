import PalPeg.ProgramBroadcast
import PalPeg.TextFeedPipelineStage

/-! Concrete 156-tape broadcast wiring for four stage pipelines. Each
slot retains its own continuation and output bit. Lifecycle selection and
the final PAL acceptance predicate are deliberately not supplied here. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.TextFeedPipelineSlots
open PalPeg.Program PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineOutputBudget (workerRate)
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

abbrev Ctrl (e : Env k) (leftSym : Fin k) :=
  (TextFeedPipelineOutput.State e leftSym (workerRate 8) 8 × Fin 96) × Fin ((workerRate 8 + 1) * 96 + 1)

abbrev Config (e : Env k) (leftSym : Fin k) := SConfig (Fin 4 → Ctrl e leftSym) (Fin k) 156

noncomputable local instance (e : Env k) (leftSym : Fin k) :
    DecidableEq (Fin 4 → Ctrl e leftSym) := fun a b => Fintype.decidablePiFintype a b

noncomputable def machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) :=
  ProgramBroadcast.machine (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8)

def output (e : Env k) (leftSym : Fin k) (x : Config e leftSym) (i : Fin 4) : Bool :=
  (x.state i).1.1.2.2

/-- Every slot receives exactly the same actual input word; its tapes,
clocks, continuation and observer coincide with the standalone machine. -/
theorem input_local (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (word : List Terminal) (x : Config e leftSym) (i : Fin 4) :
    ProgramBroadcast.slice i (word.foldl (machine e leftSym enc).sRound x) =
      word.foldl (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sRound
        (ProgramBroadcast.slice i x) :=
  ProgramBroadcast.run_slice (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8) i word x

theorem output_local (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (word : List Terminal) (x : Config e leftSym) (i : Fin 4) :
    output e leftSym (word.foldl (machine e leftSym enc).sRound x) i =
      (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).accepting
        (word.foldl (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sRound
          (ProgramBroadcast.slice i x)).state :=
  congrArg (fun c : TextFeedPipelineOutputPrepFinish.Config e leftSym (workerRate 8) 8 =>
    (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).accepting c.state)
    (input_local e leftSym enc word x i)

/-- info: 'PalPeg.TextFeedPipelineSlots.output_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_local
end PalPeg.TextFeedPipelineSlots
