import PalPeg.ProgramTapeReplay
import PalPeg.TextFeedPipelineOutputBirth

set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.TextFeedPipelineReplay
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedInit
variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineOutput.State e leftSym R rate) := inferInstance

/-- Replay the complete pipeline, not just its FIFO worker. Thus all
preparation, input counters and outputs agree with the existing empty-queue
start theorem. The extra source tape is read by finite control. -/
noncomputable def machine (e : Env k) (leftSym : Fin k)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (R rate : ℕ) :=
  TapeReplay.machine (TextFeedPipelineOutput.machine e leftSym enc R rate)
    (by change 0 < (R + 1) * 96 + 1; omega) decode

theorem from_seed (e : Env k) (leftSym : Fin k)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (R rate : ℕ)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ e.blank)
    (pat : List (Fin k)) (L : ℕ) (input : List Terminal) (junk : List (Fin k))
    (n : ℕ) (hn : input.length * ((R + 1) * 96 + 1) ≤ n) :
    (List.replicate n ()).foldl (machine e leftSym enc decode R rate).sRound
      (TapeReplay.pack ⟨0, by omega⟩ (TapeReplay.source e.blank (input.map enc) junk)
        (TextFeedPipelineOutputBirth.start e leftSym R rate pat L 0)) =
    TapeReplay.pack ⟨0, by omega⟩
      (TapeReplay.source e.blank [] ((input.map enc).reverse ++ junk))
      (input.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
        (TextFeedPipelineOutputBirth.start e leftSym R rate pat L 0)) :=
  TapeReplay.encoded_word (TextFeedPipelineOutput.machine e leftSym enc R rate)
    (by change 0 < (R + 1) * 96 + 1; omega) enc decode hdec henc input junk _ n hn

/-- info: 'PalPeg.TextFeedPipelineReplay.from_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_seed

end PalPeg.TextFeedPipelineReplay
