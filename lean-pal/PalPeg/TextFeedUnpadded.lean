import PalPeg.TextFeedPrepare
import PalPeg.StageBirth
import PalPeg.ProgLangBlankEq

/-! Execute preparation without allocating any blank cells from the
unknown future input length. Padding exists only in a proof representative. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepare
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedInit PalPeg.TextFeedRefine
open PalPeg.PatternTapes PalPeg.PatternProg

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedInput.CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (TextFeedSchedule.Outer R rate) := Classical.decEq _

private theorem step_blankEq {blank : Fin k} {s t : TapeConfiguration k}
    (h : STape.BlankEq blank (RTQueueProg.toS s) (RTQueueProg.toS t)) (a : Fin k) (mv : Move) :
    STape.BlankEq blank (RTQueueProg.toS (Tape.step blank s a mv))
      (RTQueueProg.toS (Tape.step blank t a mv)) := by
  rw [RTQueueProg.toS_step, RTQueueProg.toS_step]
  exact h.applyAction (a, mv)

private theorem copyFeed_blankEq {blank : Fin k} (w : List (Fin k)) {s t : TapeConfiguration k}
    (h : STape.BlankEq blank (RTQueueProg.toS s) (RTQueueProg.toS t)) :
    STape.BlankEq blank (RTQueueProg.toS (InputCopySentinel.feed blank s w))
      (RTQueueProg.toS (InputCopySentinel.feed blank t w)) := by
  induction w generalizing s t with
  | nil => exact h
  | cons a w ih => exact ih (step_blankEq h a .right)

theorem birth_blankTape_blankEq (blank : Fin k) (N : ℕ) :
    STape.BlankEq blank (RTQueueProg.toS (StageBirth.blankTape blank 0))
      (RTQueueProg.toS (StageBirth.blankTape blank N)) :=
  ⟨rfl, rfl, rightBlankEq_nil_replicate blank N⟩

theorem birth_zeroCounter_blankEq (blank mark : Fin k) (N : ℕ) :
    STape.BlankEq blank (RTQueueProg.toS (StageBirth.zeroCounter blank mark 0))
      (RTQueueProg.toS (StageBirth.zeroCounter blank mark N)) :=
  ⟨rfl, rfl, rightBlankEq_nil_replicate blank N⟩

theorem birth_copyTape_blankEq (blank leftSym : Fin k) (w : List (Fin k)) (L N : ℕ) :
    STape.BlankEq blank (RTQueueProg.toS (StageBirth.copyTape blank leftSym w L 0))
      (RTQueueProg.toS (StageBirth.copyTape blank leftSym w L N)) := by
  have hinit := step_blankEq (birth_blankTape_blankEq blank N) leftSym .right
  have hfeed := copyFeed_blankEq (w.take L) hinit
  exact step_blankEq hfeed blank .left

theorem birthTapes_blankEq (blank mark leftSym : Fin k) (w : List (Fin k)) (L N : ℕ) :
    ∀ j, STape.BlankEq blank (TSg (StageBirth.birthTapes blank mark leftSym w L 0) j)
      (TSg (StageBirth.birthTapes blank mark leftSym w L N) j) := by
  intro j
  change STape.BlankEq blank (RTQueueProg.toS (StageBirth.birthTapes blank mark leftSym w L 0 j))
    (RTQueueProg.toS (StageBirth.birthTapes blank mark leftSym w L N j))
  unfold StageBirth.birthTapes
  split_ifs
  · exact birth_copyTape_blankEq blank leftSym w L N
  · exact birth_blankTape_blankEq blank N
  · exact birth_zeroCounter_blankEq blank mark N

theorem before_blankEq {e : Env k} {S T : PatternTapes.Tapes k} (old : Fin k)
    (h : ∀ j, STape.BlankEq e.blank (TSg S j) (TSg T j)) :
    ∀ j, STape.BlankEq e.blank (before e S old j) (before e T old j) := by
  intro j
  refine Fin.addCases (m := 26) (n := 1) (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (m := 11) (n := 15) (fun r => ?_) (fun r => ?_) i
    · simpa only [before, Fin.append_left, Fin.append_right] using
        STape.BlankEq.refl e.blank ((Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)) r)
    · simpa only [before, Fin.append_left, Fin.append_right] using h r
  · simpa only [before, Fin.append_right] using STape.BlankEq.refl e.blank (TextFeedInput.cell old i)

/-- Preparation starts from a tape bundle independent of Text.length.
The future length is used only to choose a logically padded representative;
the actual program, its initial tapes, its instructions and its cost do not
use that padding. The output is head-equivalent to the proved initial Sim. -/
theorem prepare_unpadded {e : Env k} {leftSym : Fin k} {w Text : List (Fin k)} {L : ℕ}
    (R rate : ℕ) (old : Fin k) (hmb : e.mark ≠ e.blank) (hpos : 0 < L) (hle : L ≤ w.length)
    (hfresh : leftSym ∉ w) (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym) :
    let d := PrepInstances.prepRes w L
    let T₀ := before e (StageBirth.birthTapes e.blank e.mark leftSym w L 0) old
    ∃ tr S', Exec (interp (Terminal := Terminal) e) e.blank (prepareProg e leftSym rate) T₀ tr ∧
      tr.length ≤ (GSPreProg.preprocessSlope + 25 + 7 * rate) * L +
        GSPreProg.preprocessOffset + 49 + 11 * rate ∧
      (∀ j, STape.BlankEq e.blank (applyTrace e.blank T₀ tr j) (after e S' old j)) ∧
      Sim e ((w.take L).reverse.drop d.1) Text R rate d.2.1 d.2.2 0
        (seedModel e (toGS S')) .loop
        (initialCtrl e R rate, feedView (after e S' old)) old := by
  dsimp only
  have hpre := StageBirth.birthTapes_prepPre (blank := e.blank) (mark := e.mark)
    (Text := Text) hpos hle hfresh (Nat.le_refl Text.length)
  obtain ⟨tr, S', he, ht, hlen, _, hsim⟩ := prepare_spec (Terminal := Terminal) R rate old hmb
    hpre hstart hend hne
  have hb := before_blankEq old (birthTapes_blankEq e.blank e.mark leftSym w L Text.length)
  have he' := exec_blankEq hb he
  have ht' := applyTrace_blankEq hb tr
  rw [ht] at ht' hsim
  exact ⟨tr, S', he', hlen, ht', hsim⟩

/-- Right-padding equivalence survives every future input round and every
microstep prefix within a round, so intermediate physical reports as well
as final control states are preserved. -/
theorem future_blankEq (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    {T U : Fin 27 → STape (Fin k)} (h : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (input : List Terminal) (microInputs : List (Option Terminal)) :
    ConfigBlankEq e.blank
      (microInputs.foldl (TextFeedSchedule.machine e enc R rate).sMicroStep
        (preparedRun e enc R rate (initialCtrl e R rate, feedView T) input))
      (microInputs.foldl (TextFeedSchedule.machine e enc R rate).sMicroStep
        (preparedRun e enc R rate (initialCtrl e R rate, feedView U) input)) := by
  apply StructuredMachine.microSteps_blankEq
  apply StructuredMachine.runFrom_blankEq
  exact ⟨rfl, fun j => h (feedSlot j)⟩

/-- info: 'PalPeg.TextFeedPrepare.prepare_unpadded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare_unpadded

/-- info: 'PalPeg.TextFeedPrepare.future_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms future_blankEq

end PalPeg.TextFeedPrepare
