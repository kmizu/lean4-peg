import PalPeg.GSPreprocessProg16

/-! # Arithmetic specification of the one-tape signed counter -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

/-- The signed difference `M-N`, with zero always represented as nonnegative. -/
def OneSgn (blank mark : Fin sc) (M N : ℕ) (tp : TapeConfiguration sc) : Prop :=
  FlagCV blank mark (decide (M < N)) (M - N + (N - M)) tp

def oneIncL (c : CT sc) (blank mark : Fin sc) (M N : ℕ) : List (Act sc) :=
  flagIncL c blank mark (decide (M < N)) (M - N + (N - M))

def oneDecL (c : CT sc) (blank mark : Fin sc) (M N : ℕ) : List (Act sc) :=
  flagDecL c blank mark (decide (M < N)) (M - N + (N - M))

theorem OneSgn_zero {M : ℕ} {tp : TapeConfiguration sc} :
    OneSgn blank mark M 0 tp ↔ Tape.CounterView' blank mark tp M := by
  simp only [OneSgn, Nat.not_lt_zero, decide_false, Nat.sub_zero,
    Nat.zero_sub, Nat.add_zero, flagCV_normal]

theorem OneSgn_nonneg (c : CT sc) (hmark : mark ≠ blank)
    {M N : ℕ} {ts : Tapes sc} (h : OneSgn blank mark M N (c.get ts)) :
    condOf9 endSym mark (.notMark c.idx) (fun j => (getT ts j).focus) = true ↔ N ≤ M := by
  rw [flagCV_notMark c hmark h]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]

theorem oneInc_exec (c : CT sc) (hmark : mark ≠ blank)
    (M N : ℕ) (ts : Tapes sc) (h : OneSgn blank mark M N (c.get ts)) :
    ExecA Terminal blank endSym mark (SIGNED1_INC c.idx) ts (oneIncL c blank mark M N) := by
  apply SIGNED1_INC_exec c hmark _ _ ts h
  intro hh
  have hlt : M < N := of_decide_eq_true hh
  omega

theorem oneDec_exec (c : CT sc) (hmark : mark ≠ blank)
    (M N : ℕ) (ts : Tapes sc) (h : OneSgn blank mark M N (c.get ts)) :
    ExecA Terminal blank endSym mark (SIGNED1_DEC c.idx) ts (oneDecL c blank mark M N) :=
  SIGNED1_DEC_exec c hmark _ _ ts h

theorem oneInc_spec (c : CT sc) (M N : ℕ) (ts : Tapes sc)
    (h : OneSgn blank mark M N (c.get ts)) :
    OneSgn blank mark (M + 1) N
      (c.get (applyActs blank (oneIncL c blank mark M N) ts)) := by
  by_cases hlt : M < N
  · have hm : M - N + (N - M) = (N - M - 1) + 1 := by omega
    have hflag : FlagCV blank mark true ((N - M - 1) + 1) (c.get ts) := by
      simpa only [OneSgn, hlt, decide_true, hm] using h
    have hh := flagInc_neg c (N - M - 1) ts hflag
    have hs : (M + 1 < N) ↔ (N - M - 1 ≠ 0) := by omega
    have hn : M + 1 - N + (N - (M + 1)) = N - M - 1 := by omega
    simpa only [OneSgn, oneIncL, hlt, decide_true, hm, hn, hs] using hh
  · have hm : M - N + (N - M) = M - N := by omega
    have hflag : FlagCV blank mark false (M - N) (c.get ts) := by
      simpa only [OneSgn, hlt, decide_false, hm] using h
    have hh := flagInc_pos c (M - N) ts hflag
    have hs : ¬ M + 1 < N := by omega
    have hn : M + 1 - N + (N - (M + 1)) = M - N + 1 := by omega
    simpa only [OneSgn, oneIncL, hlt, decide_false, hm, hs, hn] using hh

theorem oneDec_spec (c : CT sc) (hmark : mark ≠ blank) (M N : ℕ) (ts : Tapes sc)
    (h : OneSgn blank mark M N (c.get ts)) :
    OneSgn blank mark M (N + 1)
      (c.get (applyActs blank (oneDecL c blank mark M N) ts)) := by
  by_cases hlt : M < N
  · have hm : M - N + (N - M) = N - M := by omega
    have hflag : FlagCV blank mark true (N - M) (c.get ts) := by
      simpa only [OneSgn, hlt, decide_true, hm] using h
    have hh := flagDec_neg c (N - M) ts hflag
    have hs : M < N + 1 := by omega
    have hn : M - (N + 1) + (N + 1 - M) = N - M + 1 := by omega
    simpa only [OneSgn, oneDecL, hlt, decide_true, hm, hs, hn] using hh
  · by_cases he : M = N
    · subst M
      have hflag : FlagCV blank mark false 0 (c.get ts) := by
        simpa only [OneSgn, Nat.lt_irrefl, decide_false, Nat.sub_self, Nat.zero_add] using h
      have hh := flagDec_zero c hmark ts hflag
      have hs : N < N + 1 := by omega
      have hm : N - (N + 1) + (N + 1 - N) = 1 := by omega
      simpa only [OneSgn, oneDecL, Nat.lt_irrefl, decide_false, Nat.sub_self,
        Nat.zero_add, hs, decide_true, hm] using hh
    · have hm : M - N + (N - M) = (M - N - 1) + 1 := by omega
      have hflag : FlagCV blank mark false ((M - N - 1) + 1) (c.get ts) := by
        simpa only [OneSgn, hlt, decide_false, hm] using h
      have hh := flagDec_pos c (M - N - 1) ts hflag
      have hs : ¬ M < N + 1 := by omega
      have hn : M - (N + 1) + (N + 1 - M) = M - N - 1 := by omega
      simpa only [OneSgn, oneDecL, hlt, decide_false, hm, hs, hn] using hh

theorem oneInc_length (c : CT sc) (M N : ℕ) :
    (oneIncL c blank mark M N).length ≤ 4 := flagIncL_length c _ _

theorem oneDec_length (c : CT sc) (M N : ℕ) :
    (oneDecL c blank mark M N).length ≤ 4 := flagDecL_length c _ _

theorem oneInc_other (c : CT sc) (j : Fin 12) (hj : j ≠ c.idx)
    (M N : ℕ) (ts : Tapes sc) :
    getT (applyActs blank (oneIncL c blank mark M N) ts) j = getT ts j := by
  unfold oneIncL flagIncL
  split <;> (try split) <;>
    simp only [List.cons_append, List.nil_append, applyActs, List.foldl_cons,
      List.foldl_nil, getT_applyAct, c.tape_eq, if_neg hj]

theorem oneDec_other (c : CT sc) (j : Fin 12) (hj : j ≠ c.idx)
    (M N : ℕ) (ts : Tapes sc) :
    getT (applyActs blank (oneDecL c blank mark M N) ts) j = getT ts j := by
  unfold oneDecL flagDecL
  split <;> (try split) <;>
    simp only [applyActs, List.foldl_cons, List.foldl_nil,
      getT_applyAct, c.tape_eq, if_neg hj]

theorem OneSgn_add_cancel (M N z : ℕ) (tp : TapeConfiguration sc) :
    OneSgn blank mark (M + z) (N + z) tp ↔ OneSgn blank mark M N tp := by
  simp only [OneSgn, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

/-- info: 'PalPeg.GSPreProg.oneInc_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneInc_exec

/-- info: 'PalPeg.GSPreProg.oneDec_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneDec_exec

/-- info: 'PalPeg.GSPreProg.oneInc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneInc_spec

/-- info: 'PalPeg.GSPreProg.oneDec_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms oneDec_spec

end PalPeg.GSPreProg
