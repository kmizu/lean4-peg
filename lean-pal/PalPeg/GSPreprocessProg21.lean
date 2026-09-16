import PalPeg.GSPreprocessProg20

/-! # State-driven traces for signed-counter updates

Unlike arithmetic-indexed traces, these execute even on unencoded tapes. This
lets the generic counter-loop theorems compose them without extra hypotheses.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def oneIncTrace (c : CT sc) (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if (c.get ts).focus = mark then [c.act blank .left, c.act blank .left] ++
    (if probe blank (Tape.step blank (c.get ts) blank .left) = mark then [c.act mark .right]
     else [c.act blank .right, c.act mark .stay])
  else [c.act blank .right]

theorem oneIncTrace_exec (c : CT sc) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (SIGNED1_INC c.idx) ts (oneIncTrace c blank mark ts) := by
  have hc : condOf9 endSym mark (.notMark c.idx) (fun j => (getT ts j).focus) =
      decide ((c.get ts).focus ≠ mark) := by rw [condOf9, c.get_eq]
  unfold oneIncTrace SIGNED1_INC
  by_cases h : (c.get ts).focus = mark
  · rw [if_pos h]
    apply execA_ite_neg (by simp only [hc, h, ne_eq, not_true_eq_false, decide_false])
    apply execA_seq (execA_ct_put c .left ts)
    apply execA_seq (execA_ct_put c .left _)
    have hp : condOf9 endSym mark (.notMark c.idx)
        (fun j => (getT (applyAct blank (applyAct blank ts (c.act blank .left))
          (c.act blank .left)) j).focus) =
        decide (probe blank (Tape.step blank (c.get ts) blank .left) ≠ mark) := by
      simp only [condOf9, c.get_eq, c.step_eq]
      rfl
    by_cases h2 : probe blank (Tape.step blank (c.get ts) blank .left) = mark
    · rw [if_pos h2]
      exact execA_ite_neg (hp.trans (by simp only [h2, ne_eq, not_true_eq_false, decide_false]))
        (execA_ct_mark c .right _)
    · rw [if_neg h2]
      exact execA_ite_pos (hp.trans (by simp only [ne_eq, h2, not_false_eq_true, decide_true]))
        (execA_seq (execA_ct_put c .right _) (execA_ct_mark c .stay _))
  · rw [if_neg h]
    exact execA_ite_pos (by simp only [hc, ne_eq, h, not_false_eq_true, decide_true])
      (execA_ct_put c .right ts)

theorem oneIncTrace_eq (c : CT sc) (hmark : mark ≠ blank)
    (neg : Bool) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark neg n (c.get ts)) (hn : neg = true → 0 < n) :
    oneIncTrace c blank mark ts = flagIncL c blank mark neg n := by
  cases neg with
  | false =>
    have hf : (c.get ts).focus ≠ mark := by rw [h.focus_eq]; exact Ne.symm hmark
    simp only [oneIncTrace, flagIncL, if_neg hf, Bool.false_eq_true, ite_false]
  | true =>
    have hf : (c.get ts).focus = mark := h.focus_eq
    cases n with
    | zero => exact False.elim (by have := hn rfl; omega)
    | succ n =>
      have hd := flagCV_dec h
      have hp := probe_eq hd
      simp only [oneIncTrace, flagIncL, if_pos hf, ite_true]
      cases n with
      | zero => simp only [hp, ite_true]
      | succ n =>
        have hp' : probe blank (Tape.step blank (c.get ts) blank .left) ≠ mark := by
          rw [hp, if_neg (by omega : n + 1 ≠ 0)]
          exact Ne.symm hmark
        simp only [if_neg hp', if_neg (by omega : n + 1 + 1 ≠ 1)]

theorem oneIncTrace_eq_oneIncL (c : CT sc) (hmark : mark ≠ blank)
    {M N : ℕ} {ts : Tapes sc} (h : OneSgn blank mark M N (c.get ts)) :
    oneIncTrace c blank mark ts = oneIncL c blank mark M N := by
  apply oneIncTrace_eq c hmark _ _ ts h
  intro hh
  have hl := of_decide_eq_true hh
  omega

theorem oneIncTrace_length (c : CT sc) (ts : Tapes sc) :
    (oneIncTrace c blank mark ts).length ≤ 4 := by
  unfold oneIncTrace
  split <;> (try split) <;> simp

theorem oneIncTrace_other (c : CT sc) (j : Fin 12) (hj : j ≠ c.idx) (ts : Tapes sc) :
    getT (applyActs blank (oneIncTrace c blank mark ts) ts) j = getT ts j := by
  unfold oneIncTrace
  split <;> (try split) <;>
    simp only [List.cons_append, List.nil_append, applyActs, List.foldl_cons, List.foldl_nil,
      getT_applyAct, c.tape_eq, if_neg hj]

theorem oneIncTrace_spec (c : CT sc) (hmark : mark ≠ blank)
    {M N : ℕ} {ts : Tapes sc} (h : OneSgn blank mark M N (c.get ts)) :
    OneSgn blank mark (M + 1) N
      (c.get (applyActs blank (oneIncTrace c blank mark ts) ts)) := by
  rw [oneIncTrace_eq_oneIncL c hmark h]
  exact oneInc_spec c M N ts h

/-- info: 'PalPeg.GSPreProg.oneIncTrace_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneIncTrace_exec

end PalPeg.GSPreProg
