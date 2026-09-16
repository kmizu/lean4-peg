import PalPeg.TextFeedPipelineBirthBuild

/-! The finite seed builder consumes actual input symbols in two fixed
microsteps per arrival. The pending symbol is held in finite control. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBirthInput
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedInit PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineBirthBuild

variable {k : ℕ} {Terminal : Type}

noncomputable def body (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) :
    PhaseBody Terminal (Bool × Fin k) (Fin k) 39 2 := fun q a ph σ =>
  if ph = 0 then
    ((q.1, (a.map enc).getD q.2), if q.1 then vec e leftSym .beginCopy else fun j => (σ j, .stay))
  else ((false, q.2), vec e leftSym (.copy q.2))

noncomputable def machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) :
    StructuredMachine Terminal ((Bool × Fin k) × Fin 2) (Fin k) 39 2 :=
  ofPhases (by decide) (by decide) e.blank (true, e.blank) (fun _ => false) (body e leftSym enc)

theorem round (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (first : Bool) (old : Fin k) (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    (machine e leftSym enc).sRound ⟨((first, old), 0), T⟩ a =
      ⟨((false, enc a), 0), applyTrace e.blank T
        ((if first then [vec e leftSym .beginCopy] else []) ++ [vec e leftSym (.copy (enc a))])⟩ := by
  refine (ofPhases_round (by decide : 0 < 39) (by decide : 0 < 2) e.blank
    (true, e.blank) (fun _ => false) (body e leftSym enc) (first, old) T a).trans ?_
  cases first <;>
    simp only [PalPeg.Speedup.MultiStepMachine.roundInputs, Nat.reduceSub,
      List.replicate_succ, List.replicate_zero, phaseRun_cons, phaseRun_nil,
      bodyStep, body, nextPhase, Fin.zero_eta, Fin.isValue,
      ↓reduceIte, Bool.false_eq_true, Option.map_some, Option.getD_some,
      List.nil_append, List.cons_append, applyTrace_cons, applyTrace_nil]
  · rfl
  · rfl

noncomputable def liveTapes (e : Env k) (leftSym : Fin k) (w : List (Fin k)) : Fin 39 → STape (Fin k) :=
  extend prepSlot (live e leftSym w) (blankBundle e.blank 39)

theorem copy_tapes (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (a : Fin k) :
    applyTrace e.blank (liveTapes e leftSym w) [vec e leftSym (.copy a)] =
      liveTapes e leftSym (w ++ [a]) := by
  have hh := applyTrace_extend prepSlot e.blank (blankBundle e.blank 39) [copyP e a] (live e leftSym w)
  rw [copy_live] at hh
  exact hh

theorem init_tapes (e : Env k) (leftSym : Fin k) :
    applyTrace e.blank (blankBundle e.blank 39) [vec e leftSym .beginCopy] = liveTapes e leftSym [] := by
  have hh := applyTrace_extend prepSlot e.blank (blankBundle e.blank 39) [initP e leftSym] (blankBundle e.blank 15)
  rw [extend_blank, init_live] at hh
  exact hh

theorem run_live (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (input : List Terminal) (w : List (Fin k)) (old : Fin k) :
    ∃ last, input.foldl (machine e leftSym enc).sRound
      ⟨((false, old), 0), liveTapes e leftSym w⟩ =
      ⟨((false, last), 0), liveTapes e leftSym (w ++ input.map enc)⟩ := by
  induction input generalizing w old with
  | nil => exact ⟨old, by simp⟩
  | cons a input ih =>
    simp only [List.foldl_cons, round, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, copy_tapes]
    obtain ⟨last, h⟩ := ih (w ++ [enc a]) (enc a)
    exact ⟨last, by simpa only [List.map_cons, List.append_assoc, List.singleton_append] using h⟩

theorem run_input (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (a : Terminal) (input : List Terminal) :
    ∃ last, (machine e leftSym enc).srun (a :: input) =
      ⟨((false, last), 0), liveTapes e leftSym ((a :: input).map enc)⟩ := by
  change ∃ last, input.foldl (machine e leftSym enc).sRound
    ((machine e leftSym enc).sRound ⟨((true, e.blank), 0), blankBundle e.blank 39⟩ a) = _
  rw [round]
  simp only [↓reduceIte, applyTrace_append, init_tapes, copy_tapes, List.nil_append]
  simpa only [List.map_cons, List.singleton_append] using run_live e leftSym enc input [enc a] (enc a)

theorem freeze_tapes (e : Env k) (leftSym : Fin k) (w : List (Fin k)) :
    applyTrace e.blank (liveTapes e leftSym w) [vec e leftSym .freeze] =
      TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 := by
  rw [seed_plain]
  have hh := applyTrace_extend prepSlot e.blank (blankBundle e.blank 39)
    [freezeP e] (live e leftSym w)
  rw [freeze_live] at hh
  exact hh

/-- Real symbols are read once each; one fixed freeze action produces the
exact unpadded seed. Choosing the freeze time belongs to the stage controller. -/
theorem input_seed (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (a : Terminal) (input : List Terminal) :
    applyTrace e.blank ((machine e leftSym enc).srun (a :: input)).tape
      [vec e leftSym .freeze] =
      TextFeedPipelineOutputBirth.seed e leftSym ((a :: input).map enc) (a :: input).length 0 := by
  obtain ⟨last, h⟩ := run_input e leftSym enc a input
  rw [h]
  simpa only [List.length_map] using freeze_tapes e leftSym ((a :: input).map enc)

theorem input_start (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (a : Terminal) (input : List Terminal) :
    (⟨((TextFeedPipelineOutput.initial e leftSym R rate, 0), 0),
      applyTrace e.blank ((machine e leftSym enc).srun (a :: input)).tape
        [vec e leftSym .freeze]⟩ : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate) =
      TextFeedPipelineOutputBirth.start e leftSym R rate
        ((a :: input).map enc) (a :: input).length 0 := by
  rw [input_seed]
  rfl

/-- info: 'PalPeg.TextFeedPipelineBirthInput.input_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms input_seed
/-- info: 'PalPeg.TextFeedPipelineBirthInput.input_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms input_start
end PalPeg.TextFeedPipelineBirthInput
