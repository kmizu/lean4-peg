import PalPeg.GSPreprocessProg67
import PalPeg.PatternProg

/-! # Sentinel-controlled two-destination copying for the finite prologue -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank leftSym : Fin sc}
  {i j1 j2 : Fin 15}

def copy2Round (i j1 j2 : Fin 15) : List (TAct 15 sc) :=
  [.copy j1 i .right, .copy j2 i .right, .keep i .left]

def copy2Acts (i j1 j2 : Fin 15) : ℕ → List (TAct 15 sc)
  | 0 => []
  | n + 1 => copy2Round i j1 j2 ++ copy2Acts i j1 j2 n

def copy2Prog (i j1 j2 : Fin 15) (leftSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .loop (i, leftSym) (TAct.copy j1 i .right).act
    (seqActs [.copy j2 i .right, .keep i .left])

theorem copy2Acts_length (i j1 j2 : Fin 15) (n : ℕ) :
    (copy2Acts (sc := sc) i j1 j2 n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [copy2Acts, List.length_append, ih]; simp [copy2Round]; omega

theorem copy2Round_run (h1 : j1 ≠ i) (S : Tapes sc) :
    runG blank (copy2Round i j1 j2) S = run blank (copyRound2 i j1 j2 S) S := by
  have hread : (applyG blank S (TAct.copy j1 i .right)) i = S i :=
    applyG_ne blank S _ (Ne.symm h1)
  have eq1 : applyG blank S (TAct.copy j1 i .right) =
      applyS blank S (SAct.put j1 (Tape.read (S i)) .right) := rfl
  have eq2 : applyG blank (applyG blank S (TAct.copy j1 i .right))
      (TAct.copy j2 i .right) =
      applyS blank (applyG blank S (TAct.copy j1 i .right))
        (SAct.put j2 (Tape.read (S i)) .right) := by
    change updG (applyG blank S (TAct.copy j1 i .right)) j2
      (Tape.step blank ((applyG blank S (TAct.copy j1 i .right)) j2)
        ((applyG blank S (TAct.copy j1 i .right)) i).focus .right) = _
    rw [hread]
    rfl
  simp only [copy2Round, copyRound2, runG_cons, runG_nil, run_cons, run_nil]
  rw [eq2, eq1]
  rfl

theorem copy2Acts_run (h1 : j1 ≠ i) (n : ℕ) (S : Tapes sc) :
    runG blank (copy2Acts i j1 j2 n) S = run blank (copyLoop2 blank i j1 j2 n S) S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [copy2Acts, copyLoop2, runG_append, run_append, copy2Round_run h1, ih]

theorem copy2Prog_exec (h1 : j1 ≠ i) (h2 : j2 ≠ i)
    {w : List (Fin sc)} (hfresh : leftSym ∉ w) :
    ∀ (b : ℕ) (S : Tapes sc), Tape.SeqView blank (S i) (leftSym :: w) b →
      ExecG Terminal blank (copy2Prog i j1 j2 leftSym) S (copy2Acts i j1 j2 b) := by
  intro b
  induction b with
  | zero =>
    intro S hS
    refine execG_loop_stop ?_
    have hf := hS.focus_eq
    have hc : (S i).focus = leftSym := by simpa using (Option.some.inj hf).symm
    simp [condOfG, hc]
  | succ b ih =>
    intro S hS
    have hf := hS.focus_eq
    have hn : (S i).focus ≠ leftSym := by
      intro hc
      rw [List.getElem?_cons_succ, hc] at hf
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hf
      exact hfresh (hget ▸ List.getElem_mem hlt)
    change ExecG Terminal blank (.loop (i, leftSym) (TAct.copy j1 i .right).act
      (seqActs [.copy j2 i .right, .keep i .left])) S
      (TAct.copy j1 i .right :: ([.copy j2 i .right, .keep i .left] ++ copy2Acts i j1 j2 b))
    refine execG_loop_cont (a := TAct.copy j1 i .right) ?_ (execG_seqActs _ _) ?_
    · simp [condOfG, hn]
    · apply ih
      have hread1 : (applyG blank S (TAct.copy j1 i .right)) i = S i :=
        applyG_ne blank S _ (Ne.symm h1)
      have hread2 : (applyG blank (applyG blank S (TAct.copy j1 i .right))
          (TAct.copy j2 i .right)) i = S i := by
        rw [applyG_ne blank _ (TAct.copy j2 i .right) (Ne.symm h2), hread1]
      change Tape.SeqView blank
        ((applyG blank (applyG blank (applyG blank S (TAct.copy j1 i .right))
          (TAct.copy j2 i .right)) (TAct.keep i .left)) i) (leftSym :: w) b
      rw [applyG_keep_self, hread2]
      exact Tape.seq_move_left hS

/-- Walk the source to its right sentinel while moving a second head by
exactly the same distance. This restores the input head without probing
beyond its last data cell or relying on blank being absent from input. -/
def tandemRight (i j : Fin 15) (endSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .loop (i, endSym) (TAct.keep i .right).act (ACT (.keep j .right))

def tandemActs (i j : Fin 15) : ℕ → List (TAct 15 sc)
  | 0 => []
  | n + 1 => [.keep i .right, .keep j .right] ++ tandemActs i j n

theorem tandemActs_length (i j : Fin 15) (n : ℕ) :
    (tandemActs (sc := sc) i j n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tandemActs, List.length_append, ih]; simp; omega

theorem tandemRight_exec {i j : Fin 15} (hij : j ≠ i)
    {endSym : Fin sc} {w : List (Fin sc)} (hend : endSym ∉ w) :
    ∀ (n b : ℕ) (S : Tapes sc), b + n = w.length →
      Tape.SeqView blank (S i) (w ++ [endSym]) b →
      ExecG Terminal blank (tandemRight i j endSym) S (tandemActs i j n) := by
  intro n
  induction n with
  | zero =>
    intro b S hlen he
    have hb : b = w.length := by omega
    have hf := he.focus_eq
    rw [hb, List.getElem?_append_right (by omega)] at hf
    have hc : (S i).focus = endSym := by simpa using hf.symm
    exact execG_loop_stop (by simp [condOfG, hc])
  | succ n ih =>
    intro b S hlen he
    have hb : b < w.length := by omega
    have hf := he.focus_eq
    rw [List.getElem?_append_left hb] at hf
    have hn : (S i).focus ≠ endSym := by
      intro hc
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hf
      exact hend (hc ▸ hget ▸ List.getElem_mem hlt)
    change ExecG Terminal blank (.loop (i, endSym) (TAct.keep i .right).act
      (ACT (.keep j .right))) S
      (TAct.keep i .right :: ([.keep j .right] ++ tandemActs i j n))
    refine execG_loop_cont (a := TAct.keep i .right) ?_ (execG_act _ _) ?_
    · simp [condOfG, hn]
    · apply ih (b + 1) _ (by omega)
      change Tape.SeqView blank
        ((applyG blank (applyG blank S (.keep i .right)) (.keep j .right)) i)
        (w ++ [endSym]) (b + 1)
      rw [applyG_ne blank _ (TAct.keep j .right) (Ne.symm hij), applyG_keep_self]
      exact Tape.seq_move_right he (by simp only [List.length_append, List.length_singleton]; omega)

theorem tandemActs_spec {i j : Fin 15} (hij : j ≠ i)
    (n : ℕ) (S : Tapes sc) {u v : List (Fin sc)} {a b : ℕ}
    (hu : Tape.SeqView blank (S i) u a) (hv : Tape.SeqView blank (S j) v b)
    (ha : a + n < u.length) (hb : b + n < v.length) :
    Tape.SeqView blank (runG blank (tandemActs i j n) S i) u (a + n) ∧
    Tape.SeqView blank (runG blank (tandemActs i j n) S j) v (b + n) := by
  induction n generalizing S a b with
  | zero => exact ⟨hu, hv⟩
  | succ n ih =>
    have hi : (runG blank [TAct.keep i .right, .keep j .right] S) i =
        Tape.step blank (S i) (S i).focus .right := by
      change (applyG blank (applyG blank S (.keep i .right)) (.keep j .right)) i = _
      rw [applyG_ne blank _ (TAct.keep j .right) (Ne.symm hij), applyG_keep_self]
    have hj : (runG blank [TAct.keep i .right, .keep j .right] S) j =
        Tape.step blank (S j) (S j).focus .right := by
      change (applyG blank (applyG blank S (.keep i .right)) (.keep j .right)) j = _
      rw [applyG_keep_self, applyG_ne blank _ (TAct.keep i .right) hij]
    have hu' : Tape.SeqView blank
        (runG blank [TAct.keep i .right, .keep j .right] S i) u (a + 1) := by
      rw [hi]; exact Tape.seq_move_right hu (by omega)
    have hv' : Tape.SeqView blank
        (runG blank [TAct.keep i .right, .keep j .right] S j) v (b + 1) := by
      rw [hj]; exact Tape.seq_move_right hv (by omega)
    have h := ih _ hu' hv' (by omega) (by omega)
    simpa only [tandemActs, runG_append, Nat.add_assoc, Nat.add_comm 1 n] using h

theorem tandemActs_other {i j k : Fin 15} (hi : k ≠ i) (hj : k ≠ j)
    (n : ℕ) (S : Tapes sc) : runG blank (tandemActs i j n) S k = S k := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [tandemActs, runG_append, ih]
    change (applyG blank (applyG blank S (.keep i .right)) (.keep j .right)) k = _
    rw [applyG_ne blank _ (TAct.keep j .right) hj,
      applyG_ne blank _ (TAct.keep i .right) hi]

/-- info: 'PalPeg.PrepInstance.tandemActs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tandemActs_spec
/-- info: 'PalPeg.PrepInstance.tandemRight_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tandemRight_exec
/-- info: 'PalPeg.PrepInstance.copy2Prog_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy2Prog_exec
/-- info: 'PalPeg.PrepInstance.copy2Acts_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copy2Acts_run
end PalPeg.PrepInstance
