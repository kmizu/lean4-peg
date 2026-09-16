import PalPeg.ProgramRecycle

set_option autoImplicit false
namespace PalPeg.ProgramRecycleWindow
open PegSeparation.RealTimeTM PalPeg.Program

variable {k : ℕ}

/-- Uniform 1:2:3 sweep lengths fit six complete clock phases. -/
theorem uniform_clear (blank : Fin k) (tp : TapeConfiguration k) (m N : ℕ)
    (h : MiddleClear.Near blank tp m) (hm : m < N) :
    Tape.StackView blank
      (MiddleClear.runL blank (MiddleClear.runR blank (MiddleClear.runL blank tp N)
        (2 * N)) (3 * N)) [] := by
  rcases tp with ⟨l, f, r⟩
  have hl : l.length ≤ m := h.left_le
  have hr : Tape.Blanks blank (r.drop m) := h.right_blanks
  have hL : MiddleClear.runL blank ⟨l, f, r⟩ N =
      ⟨[], blank, List.replicate l.length blank ++ r⟩ := by
    have hh := MiddleClear.runL_spec blank (N - 1) l f r (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hh
  let r1 := List.replicate l.length blank ++ r
  have hb : Tape.Blanks blank (r1.drop (2 * N - 1)) := by
    have hd : r1.drop (2 * N - 1) = r.drop (2 * N - 1 - l.length) := by
      simp only [r1, List.drop_append, List.length_replicate]
      rw [List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
    rw [hd]
    exact MiddleClear.blanks_drop_mono (by omega) hr
  have hf : (r1.drop (2 * N - 1)).headD blank = blank := by
    cases he : r1.drop (2 * N - 1) with
    | nil => rfl
    | cons a rest => exact hb a (by rw [he]; simp)
  have hR : MiddleClear.runR blank ⟨[], blank, r1⟩ (2 * N) =
      ⟨List.replicate (2 * N) blank, blank, r1.drop (2 * N)⟩ := by
    have hh := MiddleClear.runR_spec blank (2 * N - 1) [] blank r1
    simpa only [List.tail_drop_eq_drop_tail, MiddleClear.tail_drop_comm,
      Nat.sub_add_cancel (by omega : 1 ≤ 2 * N), List.append_nil, hf] using hh
  rw [hL]
  change Tape.StackView blank (MiddleClear.runL blank
    (MiddleClear.runR blank ⟨[], blank, r1⟩ (2 * N)) (3 * N)) []
  rw [hR]
  have hF := MiddleClear.runL_spec blank (3 * N - 1) (List.replicate (2 * N) blank)
    blank (r1.drop (2 * N)) (by simp; omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 3 * N)] at hF
  rw [hF]
  refine ⟨rfl, rfl, ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact List.eq_of_mem_replicate ha
  · exact (MiddleClear.blanks_drop_mono (by omega : 2 * N - 1 ≤ 2 * N) hb) a ha

def commands (N : ℕ) : List Move :=
  List.replicate N .left ++ List.replicate (2 * N) .right ++ List.replicate (3 * N) .left

theorem commands_length (N : ℕ) : (commands N).length = 6 * N := by
  simp [commands]
  omega

theorem clear_tape (blank : Fin k) (T : STape (Fin k)) (m N : ℕ)
    (h : MiddleClear.Near blank (ProgramRecycle.view T) m) (hm : m < N) :
    STape.BlankEq blank ((commands N).foldl (fun T d => T.applyAction blank (blank, d)) T)
      (STape.blankTape blank) := by
  apply ProgramRecycle.blankEq_of_stack
  have hh := uniform_clear blank (ProgramRecycle.view T) m N h hm
  simpa only [commands, List.foldl_append, ← ProgramRecycle.sweep_left,
    ← ProgramRecycle.sweep_right, ProgramRecycle.sweep] using hh

/-- Finite phase decoding; no work bound or input length is inspected here. -/
def direction (p : Fin 30) : Move :=
  if p.val = 15 ∨ p.val = 16 then .right else .left

def enabled (p : Fin 30) : Bool := decide (14 ≤ p.val ∧ p.val < 20)

def phaseWords (q : ℕ) : List (Fin 30) :=
  [14, 15, 16, 17, 18, 19].flatMap (fun p => List.replicate q p)

theorem phase_commands (C q : ℕ) :
    (phaseWords q).flatMap (fun p => List.replicate C (direction p)) = commands (C * q) := by
  simp only [phaseWords, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    List.flatMap_replicate]
  simp [direction, commands, Nat.mul_comm C q]
  rw [← List.append_assoc, ← List.replicate_add]
  congr 2 <;> omega

theorem reset_phases {t : ℕ} (blank : Fin k) (ht : 0 < t)
    (T : Fin t → STape (Fin k)) (m C q : ℕ)
    (h : ∀ j, MiddleClear.Near blank (ProgramRecycle.view (T j)) m) (hm : m < C * q) :
    ∀ j, STape.BlankEq blank
      ((((phaseWords q).flatMap (fun p => List.replicate C (direction p))).foldl
        (ProgramRecycle.machine blank ht).sRound ⟨(), T⟩).tape j) (STape.blankTape blank) := by
  intro j
  rw [phase_commands, ProgramRecycle.run_tape]
  exact clear_tape blank (T j) m (C * q) (h j) hm

/-- info: 'PalPeg.ProgramRecycleWindow.reset_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_phases

/-- info: 'PalPeg.ProgramRecycleWindow.clear_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clear_tape

end PalPeg.ProgramRecycleWindow
