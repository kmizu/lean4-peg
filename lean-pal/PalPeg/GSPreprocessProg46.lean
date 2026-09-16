import PalPeg.GSPreprocessProg45

/-! # Finite reach extension

At a normal (unprobed) countdown head the symbol is blank. Thus `mReady`
reduces to the two text-head checks, without consuming the countdown.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def EXTEND_REACH : Prog A9 Cond9 :=
  .loop .mReady (tV1, .keep, .right)
    (.seq (.act (tV2, .keep, .right)) (.act (tCr, .blk, .right)))

theorem reachReady_iff (hmark : mark ≠ blank) (ts : Tapes sc) {d : ℕ}
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    condOf9 endSym mark .mReady (fun j => (getT ts j).focus) = true ↔ rCond endSym ts := by
  change decide (ts.V2.focus ≠ endSym ∧ ts.Cd.focus ≠ mark ∧ ts.V1.focus = ts.V2.focus) = true ↔ _
  rw [hd.focus_blank]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, Ne.symm hmark, h.2⟩⟩

theorem EXTEND_REACH_exec (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel a b : ℕ) (c : Ctr) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b c ts → a ≤ b → x.length ≤ b + fuel →
    ExecA Terminal blank endSym mark EXTEND_REACH ts (rProg blank endSym fuel ts) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c ts he hab hbound
    apply execA_loop_stop
    apply Bool.eq_false_iff.mpr
    intro hc
    have hh := ((rCond_iff hend he hab).mp ((reachReady_iff hmark ts he.cd).mp hc)).1
    omega
  | succ fuel ih =>
    intro a b c ts he hab hbound
    by_cases hc : rCond endSym ts
    · rw [rProg, if_pos hc]
      have he1 := enc_r_step hend he hab hc
      have hx := ih (a + 1) (b + 1) _ _ he1 (by omega) (by omega)
      simp only [rActs, if_pos hc] at hx ⊢
      exact execA_loop_cont rfl rfl rfl ((reachReady_iff hmark ts he.cd).mpr hc)
        (execA_seq (execA_v2 .right _) (execA_ct_put ctCr .right _)) hx
    · rw [rProg, if_neg hc]
      apply execA_loop_stop
      exact Bool.eq_false_iff.mpr (fun hh => hc ((reachReady_iff hmark ts he.cd).mp hh))

theorem EXTEND_REACH_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (fuel a b : ℕ) (c : Ctr) (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x a b c g ts)
    (hab : a ≤ b) (hbound : x.length ≤ b + fuel) :
    ∃ L, ExecA Terminal blank endSym mark EXTEND_REACH ts L ∧
      EncS blank startSym endSym mark x (a + rSteps x fuel a b) (b + rSteps x fuel a b)
        {c with r := c.r + rSteps x fuel a b} g (applyActs blank L ts) ∧
      L.length ≤ 3 * rWork x fuel a b := by
  refine ⟨rProg blank endSym fuel ts, EXTEND_REACH_exec hend hmark fuel a b c ts he.base hab hbound,
    he.frame (rProg_noSigned blank endSym fuel ts) (rProg_spec hend fuel ts a b c he.base hab), ?_⟩
  exact rProg_length hend fuel ts a b c he.base hab

/-- info: 'PalPeg.GSPreProg.EXTEND_REACH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EXTEND_REACH_spec

end PalPeg.GSPreProg
