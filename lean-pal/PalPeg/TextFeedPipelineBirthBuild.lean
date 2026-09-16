import PalPeg.TextFeedPipelineOutputBirth

/-! Materialize the fresh pipeline seed by fixed initialization, one
copy action per arrived symbol, and a final freeze action. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBirthBuild
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedInit PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank

variable {k : ℕ}

def initP (e : Env k) (leftSym : Fin k) (j : Fin 15) : Fin k × Move :=
  if j = sIn then (leftSym, .right)
  else if j = sU ∨ j = sP ∨ j = sT ∨ j = sX2 then (e.blank, .stay)
  else (e.mark, .right)

def copyP (e : Env k) (a : Fin k) (j : Fin 15) : Fin k × Move :=
  if j = sIn then (a, .right) else (e.blank, .stay)

def freezeP (e : Env k) (j : Fin 15) : Fin k × Move :=
  if j = sIn then (e.blank, .left) else (e.blank, .stay)

def live (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (j : Fin 15) : STape (Fin k) :=
  if j = sIn then toS (InputCopySentinel.feed e.blank
    (GSTapes.runProg e.blank (StageBirth.blankTape e.blank 0) (InputCopySentinel.sentinelInit leftSym)) w)
  else if j = sU ∨ j = sP ∨ j = sT ∨ j = sX2 then STape.blankTape e.blank
  else toS (StageBirth.zeroCounter e.blank e.mark 0)

theorem init_live (e : Env k) (leftSym : Fin k) :
    applyTrace e.blank (blankBundle e.blank 15) [initP e leftSym] = live e leftSym [] := by
  funext j
  simp only [applyTrace_cons, applyTrace_nil, initP, live]
  split_ifs <;> rfl

theorem copy_live (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (a : Fin k) :
    applyTrace e.blank (live e leftSym w) [copyP e a] = live e leftSym (w ++ [a]) := by
  funext j
  simp only [applyTrace_cons, applyTrace_nil, live, copyP]
  split_ifs
  · simp only [InputCopySentinel.feed, List.foldl_append, List.foldl_cons, List.foldl_nil, toS_step]
  · rfl
  · rfl

theorem copy_word (e : Env k) (leftSym : Fin k) (w pre : List (Fin k)) :
    applyTrace e.blank (live e leftSym pre) (w.map (copyP e)) = live e leftSym (pre ++ w) := by
  induction w generalizing pre with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons]
    change applyTrace e.blank (applyTrace e.blank (live e leftSym pre) [copyP e a])
      (w.map (copyP e)) = _
    rw [copy_live, ih]
    simp only [List.append_assoc, List.singleton_append]

theorem freeze_live (e : Env k) (leftSym : Fin k) (w : List (Fin k)) :
    applyTrace e.blank (live e leftSym w) [freezeP e] =
      TSg (StageBirth.birthTapes e.blank e.mark leftSym w w.length 0) := by
  funext j
  simp only [applyTrace_cons, applyTrace_nil, live, freezeP, TSg, StageBirth.birthTapes]
  split_ifs
  · simp only [StageBirth.copyTape, List.take_length, toS_step]
  · rfl
  · rfl

theorem prepare_seed (e : Env k) (leftSym : Fin k) (w : List (Fin k)) :
    applyTrace e.blank (blankBundle e.blank 15)
      (initP e leftSym :: (w.map (copyP e) ++ [freezeP e])) =
      TSg (StageBirth.birthTapes e.blank e.mark leftSym w w.length 0) := by
  change applyTrace e.blank (applyTrace e.blank (blankBundle e.blank 15) [initP e leftSym])
    (w.map (copyP e) ++ [freezeP e]) = _
  rw [init_live, applyTrace_append, copy_word, List.nil_append, freeze_live]

theorem extend_blank {n m : ℕ} (ι : Fin n ↪ Fin m) (blank : Fin k) :
    extend ι (blankBundle blank n) (blankBundle blank m) = blankBundle blank m := by
  funext j
  unfold extend
  cases proj ι j <;> rfl

theorem seed_plain (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L : ℕ) :
    TextFeedPipelineOutputBirth.seed e leftSym w L 0 =
      extend prepSlot (TSg (StageBirth.birthTapes e.blank e.mark leftSym w L 0)) (blankBundle e.blank 39) := by
  have hp : DualQueueInput.tapes (DualQueue.blankPair e.blank) e.blank = blankBundle e.blank 23 := by
    funext j
    fin_cases j <;> rfl
  unfold TextFeedPipelineOutputBirth.seed
  rw [hp, extend_blank]

theorem build_trace (e : Env k) (leftSym : Fin k) (w : List (Fin k)) :
    applyTrace e.blank (blankBundle e.blank 39)
      ((initP e leftSym :: (w.map (copyP e) ++ [freezeP e])).map
        (extendVec prepSlot (blankBundle e.blank 39))) =
      TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 := by
  have hh := applyTrace_extend prepSlot e.blank (blankBundle e.blank 39)
    (initP e leftSym :: (w.map (copyP e) ++ [freezeP e])) (blankBundle e.blank 15)
  rw [extend_blank, prepare_seed] at hh
  exact hh.trans (seed_plain e leftSym w w.length).symm

/-- Internal commands of a finite seed-building component. The enclosing
stage controller must select begin/freeze and relay each arriving symbol. -/
inductive Command (k : ℕ) where
  | beginCopy
  | copy (a : Fin k)
  | freeze
  deriving DecidableEq, Fintype

def pvec (e : Env k) (leftSym : Fin k) : Command k → Fin 15 → Fin k × Move
  | .beginCopy => initP e leftSym
  | .copy a => copyP e a
  | .freeze => freezeP e

noncomputable def vec (e : Env k) (leftSym : Fin k) (cmd : Command k) : Fin 39 → Fin k × Move :=
  extendVec prepSlot (blankBundle e.blank 39) (pvec e leftSym cmd)

noncomputable def machine (e : Env k) (leftSym : Fin k) :
    StructuredMachine (Command k) Unit (Fin k) 39 1 where
  tapeCount_pos := by decide
  blank := e.blank
  initial := ()
  accepting := fun _ => false
  micro := fun _ a σ => ((), match a with
    | some cmd => vec e leftSym cmd
    | none => fun j => (σ j, .stay))

def commands (w : List (Fin k)) : List (Command k) := .beginCopy :: (w.map .copy ++ [.freeze])

theorem commands_length (w : List (Fin k)) : (commands w).length = w.length + 2 := by
  simp [commands, Nat.add_assoc]

theorem round (e : Env k) (leftSym : Fin k) (T : Fin 39 → STape (Fin k)) (cmd : Command k) :
    (machine e leftSym).sRound ⟨(), T⟩ cmd =
      ⟨(), fun j => (T j).applyAction e.blank (vec e leftSym cmd j)⟩ := by
  simp only [StructuredMachine.sRound, PalPeg.Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil, StructuredMachine.sMicroStep, machine]

theorem run_commands (e : Env k) (leftSym : Fin k) (cmds : List (Command k)) (T : Fin 39 → STape (Fin k)) :
    (cmds.foldl (machine e leftSym).sRound ⟨(), T⟩).tape =
      applyTrace e.blank T (cmds.map (vec e leftSym)) := by
  induction cmds generalizing T with
  | nil => rfl
  | cons cmd cmds ih =>
    rw [List.foldl_cons, round, ih]
    rfl

/-- A genuine finite-control, one-microstep component builds the exact
unpadded seed from all-blank tapes in |w|+2 internal command rounds. -/
theorem build_machine (e : Env k) (leftSym : Fin k) (w : List (Fin k)) :
    ((machine e leftSym).srun (commands w)).tape =
      TextFeedPipelineOutputBirth.seed e leftSym w w.length 0 := by
  change ((commands w).foldl (machine e leftSym).sRound ⟨(), blankBundle e.blank 39⟩).tape = _
  rw [run_commands]
  simpa only [commands, List.map_cons, List.map_append, List.map_map, List.map_nil,
    Function.comp_def, vec, pvec] using build_trace e leftSym w

noncomputable def builtStart (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (w : List (Fin k)) (L : ℕ) : TextFeedPipelineOutputPrepFinish.Config e leftSym R rate :=
  ⟨((TextFeedPipelineOutput.initial e leftSym R rate, 0), 0),
    ((machine e leftSym).srun (commands (w.take L))).tape⟩

/-- The tape result of the finite builder is exactly the initial state
used by seed_timed, after the fixed pipeline-control handoff. -/
theorem builtStart_eq (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (w : List (Fin k)) (L : ℕ) (hw : L ≤ w.length) :
    builtStart e leftSym R rate w L = TextFeedPipelineOutputBirth.start e leftSym R rate w L 0 := by
  unfold builtStart TextFeedPipelineOutputBirth.start
  rw [build_machine, List.length_take, Nat.min_eq_left hw, ← TextFeedPipelineOutputBirth.seed_take]

/-- info: 'PalPeg.TextFeedPipelineBirthBuild.builtStart_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms builtStart_eq
/-- info: 'PalPeg.TextFeedPipelineBirthBuild.build_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_machine
/-- info: 'PalPeg.TextFeedPipelineBirthBuild.prepare_seed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_seed
end PalPeg.TextFeedPipelineBirthBuild
