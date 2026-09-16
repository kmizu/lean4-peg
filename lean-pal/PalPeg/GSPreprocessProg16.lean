import PalPeg.GSPreprocessProg15

/-! # One-tape signed unary counter

The origin marker still delimits the magnitude. A second marker at the current
head denotes a negative value; a blank head denotes a nonnegative value. Each
update clears the old sign before moving, so no sign markers are left behind.
This representation is intended for the changing difference `r-q`.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

structure FlagCV (blank mark : Fin sc) (neg : Bool) (n : ℕ)
    (tp : TapeConfiguration sc) : Prop where
  left_eq : tp.left = List.replicate n blank ++ [mark]
  focus_eq : tp.focus = if neg then mark else blank
  right_blanks : Tape.Blanks blank tp.right

theorem flagCV_normal {n : ℕ} {tp : TapeConfiguration sc} :
    FlagCV blank mark false n tp ↔ Tape.CounterView' blank mark tp n := by
  constructor
  · intro h; exact ⟨h.left_eq, h.focus_eq, h.right_blanks⟩
  · intro h; exact ⟨h.left_eq, h.focus_blank, h.right_blanks⟩

theorem flagCV_set {n : ℕ} {tp : TapeConfiguration sc}
    (h : Tape.CounterView' blank mark tp n) (neg : Bool) :
    FlagCV blank mark neg n (Tape.step blank tp (if neg then mark else blank) .stay) :=
  ⟨h.left_eq, rfl, h.right_blanks⟩

theorem flagCV_inc {neg : Bool} {n : ℕ} {tp : TapeConfiguration sc}
    (h : FlagCV blank mark neg n tp) :
    Tape.CounterView' blank mark (Tape.step blank tp blank .right) (n + 1) := by
  rw [Tape.step_right]
  refine ⟨?_, h.right_blanks.headD, h.right_blanks.tail⟩
  simp only [h.left_eq, List.replicate_succ, List.cons_append]

theorem flagCV_dec {neg : Bool} {n : ℕ} {tp : TapeConfiguration sc}
    (h : FlagCV blank mark neg (n + 1) tp) :
    Tape.CounterView' blank mark (Tape.step blank tp blank .left) n := by
  have hl : tp.left = blank :: (List.replicate n blank ++ [mark]) := by
    simpa only [List.replicate_succ, List.cons_append] using h.left_eq
  rw [Tape.step_left_of_left_cons hl]
  exact ⟨rfl, rfl, h.right_blanks.cons⟩

/-- Increment a signed counter; only the head and its two left neighbors are read. -/
def SIGNED1_INC (j : Fin 12) : Prog A9 Cond9 :=
  .ite (.notMark j) (.act (j, .blk, .right))
    (.seq (.act (j, .blk, .left)) (.seq (.act (j, .blk, .left))
      (.ite (.notMark j) (.seq (.act (j, .blk, .right)) (.act (j, .mrk, .stay)))
        (.act (j, .mrk, .right)))))

def SIGNED1_DEC (j : Fin 12) : Prog A9 Cond9 :=
  .ite (.notMark j)
    (.seq (.act (j, .blk, .left)) (.ite (.notMark j) (.act (j, .blk, .stay))
      (.seq (.act (j, .mrk, .right))
        (.seq (.act (j, .blk, .right)) (.act (j, .mrk, .stay))))))
    (.seq (.act (j, .blk, .right)) (.act (j, .mrk, .stay)))

def flagIncL (c : CT sc) (blank mark : Fin sc) (neg : Bool) (n : ℕ) : List (Act sc) :=
  if neg then [c.act blank .left, c.act blank .left] ++
    (if n = 1 then [c.act mark .right] else [c.act blank .right, c.act mark .stay])
  else [c.act blank .right]

def flagDecL (c : CT sc) (blank mark : Fin sc) (neg : Bool) (n : ℕ) : List (Act sc) :=
  if neg then [c.act blank .right, c.act mark .stay]
  else if n = 0 then [c.act blank .left, c.act mark .right, c.act blank .right, c.act mark .stay]
  else [c.act blank .left, c.act blank .stay]

theorem flagIncL_length (c : CT sc) (neg : Bool) (n : ℕ) :
    (flagIncL c blank mark neg n).length ≤ 4 := by
  unfold flagIncL
  split <;> (try split) <;> simp

theorem flagDecL_length (c : CT sc) (neg : Bool) (n : ℕ) :
    (flagDecL c blank mark neg n).length ≤ 4 := by
  unfold flagDecL
  split <;> (try split) <;> simp

theorem flagInc_pos (c : CT sc) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark false n (c.get ts)) :
    FlagCV blank mark false (n + 1)
      (c.get (applyActs blank (flagIncL c blank mark false n) ts)) := by
  apply flagCV_normal.mpr
  simpa only [flagIncL, Bool.false_eq_true, ite_false, applyActs,
    List.foldl_cons, List.foldl_nil, c.step_eq] using flagCV_inc h

theorem flagDec_neg (c : CT sc) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark true n (c.get ts)) :
    FlagCV blank mark true (n + 1)
      (c.get (applyActs blank (flagDecL c blank mark true n) ts)) := by
  have hh := flagCV_set (flagCV_inc h) true
  simpa only [flagDecL, ite_true, applyActs, List.foldl_cons, List.foldl_nil,
    c.step_eq] using hh

theorem flagDec_pos (c : CT sc) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark false (n + 1) (c.get ts)) :
    FlagCV blank mark false n
      (c.get (applyActs blank (flagDecL c blank mark false (n + 1)) ts)) := by
  have hh := flagCV_set (flagCV_dec h) false
  simpa only [flagDecL, Bool.false_eq_true, ite_false, Nat.succ_ne_zero,
    applyActs, List.foldl_cons, List.foldl_nil, c.step_eq] using hh

theorem flagDec_zero (c : CT sc) (hmark : mark ≠ blank) (ts : Tapes sc)
    (h : FlagCV blank mark false 0 (c.get ts)) :
    FlagCV blank mark true 1
      (c.get (applyActs blank (flagDecL c blank mark false 0) ts)) := by
  have hh := flagCV_set (flagCV_inc h) true
  have hr := ct_dTest_restore c hmark ts (flagCV_normal.mp h)
  have he : applyActs blank (flagDecL c blank mark false 0) ts =
      applyAct blank (applyAct blank ts (c.act blank .right)) (c.act mark .stay) := by
    change applyActs blank (dTest c blank mark ++ [c.act blank .right, c.act mark .stay]) ts = _
    rw [applyActs_append, hr]
    rfl
  rw [he, c.step_eq, c.step_eq]
  exact hh

theorem flagInc_neg (c : CT sc) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark true (n + 1) (c.get ts)) :
    FlagCV blank mark (decide (n ≠ 0)) n
      (c.get (applyActs blank (flagIncL c blank mark true (n + 1)) ts)) := by
  let t1 := applyAct blank ts (c.act blank .left)
  have h1 : Tape.CounterView' blank mark (c.get t1) n := by
    simpa only [t1, c.step_eq] using flagCV_dec h
  have hr := ct_probe_restore c t1 h1
  have hp := probe_eq h1
  cases n with
  | zero =>
    have hp' : probe blank (c.get t1) = mark := by simpa only [ite_true] using hp
    rw [hp'] at hr
    have he : applyActs blank (flagIncL c blank mark true (0 + 1)) ts = t1 := by
      exact hr
    rw [he]
    exact flagCV_normal.mpr h1
  | succ n =>
    have hp' : probe blank (c.get t1) = blank := by
      simpa only [if_neg (Nat.succ_ne_zero n)] using hp
    rw [hp'] at hr
    have he : applyActs blank (flagIncL c blank mark true (n + 1 + 1)) ts =
        applyAct blank t1 (c.act mark .stay) := by
      simp only [flagIncL, ite_true, if_neg (by omega : n + 1 + 1 ≠ 1),
        List.cons_append, List.nil_append, applyActs, List.foldl_cons, List.foldl_nil]
      change applyAct blank
        (applyAct blank (applyAct blank t1 (c.act blank .left)) (c.act blank .right))
        (c.act mark .stay) = _
      rw [hr]
    rw [he, c.step_eq]
    have hn : decide (n + 1 ≠ 0) = true := decide_eq_true (by omega)
    rw [hn]
    exact flagCV_set h1 true

theorem flagCV_notMark (c : CT sc) (hmark : mark ≠ blank)
    {neg : Bool} {n : ℕ} {ts : Tapes sc}
    (h : FlagCV blank mark neg n (c.get ts)) :
    condOf9 endSym mark (.notMark c.idx) (fun j => (getT ts j).focus) = !neg := by
  cases neg <;> simp only [condOf9, c.get_eq, h.focus_eq, ite_true, ite_false,
    Bool.false_eq_true, ne_eq, not_true_eq_false, decide_false, Bool.not_true,
    Ne.symm hmark, not_false_eq_true, decide_true, Bool.not_false]

theorem SIGNED1_INC_exec (c : CT sc) (hmark : mark ≠ blank)
    (neg : Bool) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark neg n (c.get ts)) (hn : neg = true → 0 < n) :
    ExecA Terminal blank endSym mark (SIGNED1_INC c.idx) ts
      (flagIncL c blank mark neg n) := by
  have hc := flagCV_notMark (endSym := endSym) c hmark h
  cases neg with
  | false => exact execA_ite_pos hc (execA_ct_put c .right ts)
  | true =>
    cases n with
    | zero => exact False.elim (by have := hn rfl; omega)
    | succ n =>
      apply execA_ite_neg hc
      apply execA_seq (execA_ct_put c .left ts)
      apply execA_seq (execA_ct_put c .left _)
      have hd : Tape.CounterView' blank mark
          (c.get (applyAct blank ts (c.act blank .left))) n := by
        rw [c.step_eq]
        exact flagCV_dec h
      have hp : condOf9 endSym mark (.notMark c.idx)
          (fun j => (getT (applyAct blank (applyAct blank ts (c.act blank .left))
            (c.act blank .left)) j).focus) = decide (n ≠ 0) := by
        simp only [condOf9, c.get_eq, c.step_eq]
        change decide (Tape.read (Tape.step blank
          (Tape.step blank (c.get ts) blank .left) blank .left) ≠ mark) = _
        rw [Tape.counter'_read_after_probe (by simpa only [c.step_eq] using hd)]
        by_cases hz : n = 0 <;> simp [hz, Ne.symm hmark]
      cases n with
      | zero => exact execA_ite_neg (by simpa using hp) (execA_ct_mark c .right _)
      | succ n =>
        simp only [if_neg (by omega : n + 1 + 1 ≠ 1)]
        apply execA_ite_pos (by simpa using hp)
        exact execA_seq (execA_ct_put c .right _) (execA_ct_mark c .stay _)

theorem SIGNED1_DEC_exec (c : CT sc) (hmark : mark ≠ blank)
    (neg : Bool) (n : ℕ) (ts : Tapes sc)
    (h : FlagCV blank mark neg n (c.get ts)) :
    ExecA Terminal blank endSym mark (SIGNED1_DEC c.idx) ts
      (flagDecL c blank mark neg n) := by
  have hc := flagCV_notMark (endSym := endSym) c hmark h
  cases neg with
  | true =>
    exact execA_ite_neg hc (execA_seq (execA_ct_put c .right ts) (execA_ct_mark c .stay _))
  | false =>
    apply execA_ite_pos hc
    have hp : condOf9 endSym mark (.notMark c.idx)
        (fun j => (getT (applyAct blank ts (c.act blank .left)) j).focus) =
        decide (n ≠ 0) := by
      simp only [condOf9, c.get_eq, c.step_eq]
      change decide (Tape.read (Tape.step blank (c.get ts) blank .left) ≠ mark) = _
      rw [Tape.counter'_read_after_probe (flagCV_normal.mp h)]
      by_cases hz : n = 0 <;> simp [hz, Ne.symm hmark]
    cases n with
    | zero =>
      apply execA_seq (execA_ct_put c .left ts)
      exact execA_ite_neg (by simpa using hp)
        (execA_seq (execA_ct_mark c .right _)
          (execA_seq (execA_ct_put c .right _) (execA_ct_mark c .stay _)))
    | succ n =>
      simp only [flagDecL, Bool.false_eq_true, ite_false,
        if_neg (by omega : n + 1 ≠ 0)]
      apply execA_seq (execA_ct_put c .left ts)
      exact execA_ite_pos (by simpa using hp) (execA_ct_put c .stay _)

end PalPeg.GSPreProg
