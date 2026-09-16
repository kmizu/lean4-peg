import PalPeg.GSPreprocessProg10

/-! # Constant-cost saturated decrement for the bounded first search

The first search can maintain `bound - p` on a scratch counter. Advancing
the candidate uses this operation, even after the bound has been reached.
No counter value is inspected by the finite program itself.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def SAT_DEC (j : Fin 12) : Prog A9 Cond9 := TRY_DEC j 1 .skip .skip

def satDecL (c : CT sc) (blank mark : Fin sc) (n : ℕ) (t : Tapes sc) : List (Act sc) :=
  tryDecL c blank mark 1 n t

theorem satDecL_length (c : CT sc) (n : ℕ) (t : Tapes sc) :
    (satDecL c blank mark n t).length = 2 := by
  cases n <;> simp [satDecL, tryDecL, dTest]

theorem SAT_DEC_exec (c : CT sc) (hmark : mark ≠ blank) (n : ℕ) (t : Tapes sc)
    (hn : Tape.CounterView' blank mark (c.get t) n) :
    ExecA Terminal blank endSym mark (SAT_DEC c.idx) t (satDecL c blank mark n t) := by
  have hx : ExecA Terminal blank endSym mark (if 1 ≤ n then .skip else .skip)
      (applyActs blank (tryDecL c blank mark 1 n t) t) [] := by
    split <;> exact execA_skip
  simpa only [SAT_DEC, satDecL, List.append_nil] using
    TRY_DEC_exec c hmark 1 n .skip .skip t [] hn hx

theorem satDecL_counter (c : CT sc) (hmark : mark ≠ blank) (n : ℕ) (t : Tapes sc)
    (hn : Tape.CounterView' blank mark (c.get t) n) :
    Tape.CounterView' blank mark (c.get (applyActs blank (satDecL c blank mark n t) t))
      (n - 1) := by
  have h := tryDec_counter c hmark 1 n t hn
  have heq : (if 1 ≤ n then n - 1 else n) = n - 1 := by split <;> omega
  rw [heq] at h
  exact h

theorem satDecL_other (c : CT sc) (j : Fin 12) (hj : j ≠ c.idx) (n : ℕ) (t : Tapes sc) :
    getT (applyActs blank (satDecL c blank mark n t) t) j = getT t j :=
  tryDec_other c j hj 1 n t

theorem satDecL_bound (c : CT sc) (hmark : mark ≠ blank) (bound p : ℕ) (t : Tapes sc)
    (hn : Tape.CounterView' blank mark (c.get t) (bound - p)) :
    Tape.CounterView' blank mark
      (c.get (applyActs blank (satDecL c blank mark (bound - p) t) t))
      (bound - (p + 1)) := by
  simpa only [Nat.sub_sub] using satDecL_counter c hmark (bound - p) t hn

end PalPeg.GSPreProg
