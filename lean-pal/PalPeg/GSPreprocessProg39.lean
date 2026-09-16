import PalPeg.GSPreprocessProg38
import PalPeg.GSPreprocessProg19

/-! # State-read traces for saturated decrement and fixed countdown increments -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def satDecRawL (c : CT sc) (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  [c.act blank .left] ++
    if probe blank (c.get ts) = mark then [c.act mark .right] else [c.act blank .stay]

theorem satDecRaw_exec (c : CT sc) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (SAT_DEC c.idx) ts (satDecRawL c blank mark ts) := by
  have hr : (getT (applyActs blank [c.act blank .left] ts) c.idx).focus =
      probe blank (c.get ts) := by
    simp only [applyActs, List.foldl_cons, List.foldl_nil, c.get_eq, c.step_eq]
    rfl
  by_cases hc : probe blank (c.get ts) = mark
  · rw [satDecRawL, if_pos hc]
    apply execA_seq (execA_ct_put c .left ts)
    apply execA_ite_neg
    · simp only [condOf9, hr, hc, ne_eq, not_true_eq_false, decide_false]
    · simpa only [List.append_nil] using
        execA_seq (execA_ct_mark c .right _) (execA_skip (Terminal := Terminal))
  · rw [satDecRawL, if_neg hc]
    apply execA_seq (execA_ct_put c .left ts)
    apply execA_ite_pos
    · simp only [condOf9, hr, decide_eq_true_eq]; exact hc
    · simpa only [List.append_nil, TRY_DEC] using
        execA_seq (execA_ct_put c .stay _) (execA_skip (Terminal := Terminal))

theorem satDecRaw_eq (c : CT sc) (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hn : Tape.CounterView' blank mark (c.get ts) n) :
    satDecRawL c blank mark ts = satDecL c blank mark n ts := by
  have hp := probe_eq hn
  cases n with
  | zero => simp [satDecRawL, hp, satDecL, tryDecL, dTest]
  | succ n => simp [satDecRawL, hp, Ne.symm hmark, satDecL, tryDecL]

theorem satDecRaw_other (c : CT sc) (j : Fin 12) (hj : j ≠ c.idx) (ts : Tapes sc) :
    getT (applyActs blank (satDecRawL c blank mark ts) ts) j = getT ts j := by
  apply getT_applyActs_other
  intro a ha
  unfold satDecRawL at ha
  split at ha <;> simp only [List.mem_append, List.mem_singleton] at ha <;>
    rcases ha with rfl | rfl <;> simpa only [c.tape_eq] using Ne.symm hj

theorem satDecRaw_length (c : CT sc) (ts : Tapes sc) :
    (satDecRawL c blank mark ts).length = 2 := by
  unfold satDecRawL
  split <;> rfl

theorem satDecRaw_counter (c : CT sc) (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hn : Tape.CounterView' blank mark (c.get ts) n) :
    Tape.CounterView' blank mark (c.get (applyActs blank (satDecRawL c blank mark ts) ts))
      (n - 1) := by
  rw [satDecRaw_eq c hmark n ts hn]
  exact satDecL_counter c hmark n ts hn

def CD_UP (n : ℕ) : Prog A9 Cond9 := repeatProg (.act (tCd, .blk, .right)) n

theorem CD_UP_exec (n : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (CD_UP n) ts (cdIncs blank n) := by
  induction n generalizing ts with
  | zero => exact execA_skip
  | succ n ih =>
    exact execA_seq (execA_ct_put ctCd .right ts) (ih _)

theorem cdIncs_other (n : ℕ) (j : Fin 12) (hj : j ≠ tCd) (ts : Tapes sc) :
    getT (applyActs blank (cdIncs blank n) ts) j = getT ts j := by
  apply getT_applyActs_other
  intro a ha
  have hh : a = Act.Cd blank .right := (List.mem_replicate.mp ha).2
  subst a
  exact Ne.symm hj

end PalPeg.GSPreProg
