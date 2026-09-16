import PalPeg.GSPreprocessProg70

/-! # Counting the remaining pattern into a unary counter -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank : Fin sc}

def countRightProg (i c : Fin 15) (endSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .loop (i, endSym) (TAct.keep i .right).act (ACT (.put c blank .right))

def countRightTrace (i c : Fin 15) : ℕ → List (TAct 15 sc)
  | 0 => []
  | n + 1 => [.keep i .right, .put c blank .right] ++ countRightTrace i c n

theorem countRight_spec {i c : Fin 15} {endSym mark : Fin sc} {w : List (Fin sc)}
    (hic : i ≠ c) (hend : endSym ∉ w) :
    ∀ (n b m : ℕ) (S : Tapes sc), b + n = w.length →
      Tape.SeqView blank (S i) (w ++ [endSym]) b →
      Tape.CounterView' blank mark (S c) m →
      ExecG Terminal blank (countRightProg (blank := blank) i c endSym) S
        (countRightTrace (blank := blank) i c n) ∧
      Tape.SeqView blank (runG blank (countRightTrace (blank := blank) i c n) S i)
        (w ++ [endSym]) w.length ∧
      Tape.CounterView' blank mark
        (runG blank (countRightTrace (blank := blank) i c n) S c) (m + n) := by
  intro n
  induction n with
  | zero =>
    intro b m S hn hv hc
    have hb : b = w.length := by omega
    subst b
    have hf := hv.focus_eq
    have he : (S i).focus = endSym := by simpa using hf.symm
    refine ⟨execG_loop_stop ?_, ?_, ?_⟩
    · simp [condOfG, he]
    · simpa [countRightTrace] using hv
    · simpa [countRightTrace] using hc
  | succ n ih =>
    intro b m S hn hv hc
    have hb : b < w.length := by omega
    have hf := hv.focus_eq
    rw [List.getElem?_append_left hb] at hf
    have he : (S i).focus ≠ endSym := by
      intro heq
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hf
      exact hend (heq ▸ hget ▸ List.getElem_mem hlt)
    let S' := applyG blank (applyG blank S (.keep i .right)) (.put c blank .right)
    have hv' : Tape.SeqView blank (S' i) (w ++ [endSym]) (b + 1) := by
      dsimp [S']
      rw [applyG_ne blank _ _ hic, applyG_keep_self]
      exact Tape.seq_move_right hv (by simp; omega)
    have hc' : Tape.CounterView' blank mark (S' c) (m + 1) := by
      dsimp [S']
      rw [applyG_put_self, applyG_ne blank _ _ hic.symm]
      exact Tape.counter'_inc hc
    obtain ⟨ee, vv, cc⟩ := ih (b + 1) (m + 1) S' (by omega) hv' hc'
    refine ⟨?_, ?_, ?_⟩
    · exact execG_loop_cont (by simp [condOfG, he]) (execG_act _ _) ee
    · simpa [countRightTrace, runG_cons, S'] using vv
    · simpa [countRightTrace, runG_cons, S', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cc

theorem countRightTrace_other {i c j : Fin 15} (hji : j ≠ i) (hjc : j ≠ c)
    (n : ℕ) (S : Tapes sc) :
    runG blank (countRightTrace (blank := blank) i c n) S j = S j := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    simp only [countRightTrace, List.cons_append, List.nil_append, runG_cons]
    rw [ih, applyG_ne blank _ _ hjc, applyG_ne blank _ _ hji]

@[simp] theorem countRightTrace_length (i c : Fin 15) (n : ℕ) :
    (countRightTrace (blank := blank) i c n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countRightTrace, ih]; omega

/-- Include one final increment, for the degenerate period `L - s + 1`. -/
def countSuffixProg (i c : Fin 15) (endSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (countRightProg (blank := blank) i c endSym) (ACT (.put c blank .right))

theorem countSuffix_spec {i c : Fin 15} {start endSym mark : Fin sc}
    {w : List (Fin sc)} {s : ℕ} (S : Tapes sc)
    (hic : i ≠ c) (hne : start ≠ endSym) (hend : endSym ∉ w)
    (hs : s ≤ w.length)
    (hv : Tape.SeqView blank (S i) (start :: w ++ [endSym]) (s + 1))
    (hc : Tape.CounterView' blank mark (S c) 0) :
    ∃ trace, ExecG Terminal blank (countSuffixProg (blank := blank) i c endSym) S trace ∧
      Tape.SeqView blank (runG blank trace S i)
        (start :: w ++ [endSym]) (w.length + 1) ∧
      Tape.CounterView' blank mark (runG blank trace S c) (w.length - s + 1) ∧
      (∀ j, j ≠ i → j ≠ c → runG blank trace S j = S j) ∧
      trace.length = 2 * (w.length - s) + 1 := by
  obtain ⟨ee, vv, cc⟩ := countRight_spec (Terminal := Terminal) hic
    (w := start :: w) (by simp [hne.symm, hend]) (w.length - s) (s + 1) 0 S
    (by simp; omega) hv hc
  refine ⟨countRightTrace (blank := blank) i c (w.length - s) ++ [.put c blank .right],
    execG_seq ee (execG_act _ _), ?_, ?_, ?_, ?_⟩
  · simp only [runG_append, runG_cons, runG_nil]
    rw [applyG_ne blank _ _ hic]
    simpa using vv
  · simp only [runG_append, runG_cons, runG_nil, applyG_put_self]
    exact Tape.counter'_inc (by simpa using cc)
  · intro j hji hjc
    simp only [runG_append, runG_cons, runG_nil]
    rw [applyG_ne blank _ _ hjc, countRightTrace_other hji hjc]
  · simp

end PalPeg.PrepInstance
