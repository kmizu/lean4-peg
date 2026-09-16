import PalPeg.MiddleClear
import PalPeg.ProgramBlankEq

set_option autoImplicit false
namespace PalPeg.ProgramRecycle
open PegSeparation.RealTimeTM PalPeg.Program

variable {k t : ℕ}

def view (T : STape (Fin k)) : TapeConfiguration k := ⟨T.left, T.focus, T.right⟩

theorem view_action (blank : Fin k) (T : STape (Fin k)) (a : Fin k × Move) :
    view (T.applyAction blank a) = Tape.step blank (view T) a.1 a.2 := by
  rcases T with ⟨l, f, r⟩
  rcases a with ⟨w, mv⟩
  cases mv <;> cases l <;> cases r <;> rfl

def sweep (blank : Fin k) (T : STape (Fin k)) (mv : Move) (n : ℕ) : STape (Fin k) :=
  (List.replicate n mv).foldl (fun T d => T.applyAction blank (blank, d)) T

theorem sweep_left (blank : Fin k) (n : ℕ) (T : STape (Fin k)) :
    view (sweep blank T .left n) = MiddleClear.runL blank (view T) n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    change view (sweep blank (T.applyAction blank (blank, .left)) .left n) = _
    rw [ih, view_action]
    rfl

theorem sweep_right (blank : Fin k) (n : ℕ) (T : STape (Fin k)) :
    view (sweep blank T .right n) = MiddleClear.runR blank (view T) n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    change view (sweep blank (T.applyAction blank (blank, .right)) .right n) = _
    rw [ih, view_action]
    rfl

def commands (m : ℕ) : List Move :=
  List.replicate (m + 1) .left ++ List.replicate (2 * m + 1) .right ++
    List.replicate (2 * m + 2) .left

theorem commands_length (m : ℕ) : (commands m).length = 5 * m + 4 := by
  simp [commands]
  omega

theorem blankEq_of_stack (blank : Fin k) (T : STape (Fin k))
    (h : Tape.StackView blank (view T) []) : STape.BlankEq blank T (STape.blankTape blank) := by
  refine ⟨h.left_eq, h.focus_blank, ?_⟩
  intro n
  change T.right[n]?.getD blank = blank
  cases he : T.right[n]? with
  | none => rfl
  | some a =>
    have ha := h.right_blanks a (List.mem_of_getElem? he)
    exact ha

theorem clear_tape (blank : Fin k) (T : STape (Fin k)) (m : ℕ)
    (h : MiddleClear.Near blank (view T) m) :
    STape.BlankEq blank
      ((commands m).foldl (fun T d => T.applyAction blank (blank, d)) T) (STape.blankTape blank) := by
  apply blankEq_of_stack
  have hh := MiddleClear.clear_spec h
  simpa only [commands, List.foldl_append, ← sweep_left, ← sweep_right, sweep] using hh

/-- All tapes are swept simultaneously. The enclosing finite scheduler must
supply the three sweep durations; this component does not read m at runtime. -/
def machine (blank : Fin k) (ht : 0 < t) : StructuredMachine Move Unit (Fin k) t 1 where
  tapeCount_pos := ht
  blank := blank
  initial := ()
  accepting := fun _ => false
  micro := fun _ a σ => ((), fun j => match a with
    | some d => (blank, d)
    | none => (σ j, .stay))

theorem round (blank : Fin k) (ht : 0 < t) (T : Fin t → STape (Fin k)) (d : Move) :
    (machine blank ht).sRound ⟨(), T⟩ d =
      ⟨(), fun j => (T j).applyAction blank (blank, d)⟩ := rfl

theorem run_tape (blank : Fin k) (ht : 0 < t) (ds : List Move)
    (T : Fin t → STape (Fin k)) (j : Fin t) :
    (ds.foldl (machine blank ht).sRound ⟨(), T⟩).tape j =
      ds.foldl (fun T d => T.applyAction blank (blank, d)) (T j) := by
  induction ds generalizing T with
  | nil => rfl
  | cons d ds ih => simp only [List.foldl_cons, round, ih]

theorem reset (blank : Fin k) (ht : 0 < t) (T : Fin t → STape (Fin k)) (m : ℕ)
    (h : ∀ j, MiddleClear.Near blank (view (T j)) m) :
    ∀ j, STape.BlankEq blank
      (((commands m).foldl (machine blank ht).sRound ⟨(), T⟩).tape j) (STape.blankTape blank) := by
  intro j
  rw [run_tape]
  exact clear_tape blank (T j) m (h j)

def Near {Q : Type} (blank : Fin k) (x : SConfig Q (Fin k) t) (m : ℕ) : Prop :=
  ∀ j, MiddleClear.Near blank (view (x.tape j)) m

section Executions
variable {Q Terminal : Type} [Fintype Q] [DecidableEq Q] {B : ℕ}

theorem near_step (M : StructuredMachine Terminal Q (Fin k) t B)
    (x : SConfig Q (Fin k) t) (m : ℕ) (h : Near M.blank x m) (a : Option Terminal) :
    Near M.blank (M.sMicroStep x a) (m + 1) := by
  intro j
  change MiddleClear.Near M.blank (view ((x.tape j).applyAction M.blank
    ((M.micro x.state a (fun j => (x.tape j).focus)).2 j))) (m + 1)
  rw [view_action]
  exact (h j).step _ _

theorem near_steps (M : StructuredMachine Terminal Q (Fin k) t B)
    (ops : List (Option Terminal)) (x : SConfig Q (Fin k) t) (m : ℕ) (h : Near M.blank x m) :
    Near M.blank (ops.foldl M.sMicroStep x) (m + ops.length) := by
  induction ops generalizing x m with
  | nil => exact h
  | cons a ops ih =>
    have hh := ih (M.sMicroStep x a) (m + 1) (near_step M x m h a)
    simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 ops.length] using hh

theorem near_init (M : StructuredMachine Terminal Q (Fin k) t B) : Near M.blank M.sInit 0 := by
  intro j
  refine ⟨by simp [view, StructuredMachine.sInit, STape.blankTape], ?_⟩
  intro a ha
  simp [view, StructuredMachine.sInit, STape.blankTape] at ha

theorem near_round (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (x : SConfig Q (Fin k) t) (m : ℕ) (h : Near M.blank x m) (a : Terminal) :
    Near M.blank (M.sRound x a) (m + B) := by
  have hh := near_steps M (PalPeg.Speedup.MultiStepMachine.roundInputs B a) x m h
  have hl : (PalPeg.Speedup.MultiStepMachine.roundInputs B a).length = B := by
    simp [PalPeg.Speedup.MultiStepMachine.roundInputs]
    omega
  simpa only [StructuredMachine.sRound, hl] using hh

theorem near_rounds (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (input : List Terminal) (x : SConfig Q (Fin k) t) (m : ℕ) (h : Near M.blank x m) :
    Near M.blank (input.foldl M.sRound x) (m + B * input.length) := by
  induction input generalizing x m with
  | nil => simpa using h
  | cons a input ih =>
    have hh := ih (M.sRound x a) (m + B) (near_round M hB x m h a)
    simpa only [List.foldl_cons, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc, Nat.add_comm B (B * input.length)] using hh

theorem near_run (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (input : List Terminal) : Near M.blank (M.srun input) (B * input.length) := by
  simpa only [StructuredMachine.srun, Nat.zero_add] using near_rounds M hB input M.sInit 0 (near_init M)

theorem reset_after_run (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (input : List Terminal) :
    ∀ j, STape.BlankEq M.blank
      (((commands (B * input.length)).foldl (machine M.blank M.tapeCount_pos).sRound
        ⟨(), (M.srun input).tape⟩).tape j) (STape.blankTape M.blank) :=
  reset M.blank M.tapeCount_pos (M.srun input).tape _ (near_run M hB input)

end Executions

/-- info: 'PalPeg.ProgramRecycle.reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset
/-- info: 'PalPeg.ProgramRecycle.near_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms near_steps
/-- info: 'PalPeg.ProgramRecycle.reset_after_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_after_run

end PalPeg.ProgramRecycle
