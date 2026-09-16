import PalPeg.GSPreprocessProg36

/-! # Finite first-phase scan -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def mProbe (blank : Fin sc) (ts : Tapes sc) : Tapes sc :=
  applyAct blank ts (.Cd blank .left)

def mRunBody : Prog A9 Cond9 :=
  .seq (.act (tV1, .keep, .right))
    (.seq (.act (tV2, .keep, .right))
      (.seq (.act (tCq, .blk, .right)) (.act (tCd, .blk, .left))))

def mRUN : Prog A9 Cond9 := .loop .mReady (tCd, .blk, .stay) mRunBody

def FIRST_SCAN : Prog A9 Cond9 :=
  .seq (.act (tCd, .blk, .left)) (.seq mRUN (.act (tCd, .keep, .right)))

def mIter (blank : Fin sc) : List (Act sc) :=
  [.Cd blank .stay, .V1 .right, .V2 .right, .Cq blank .right, .Cd blank .left]

theorem mReady_iff (ts : Tapes sc) :
    condOf9 endSym mark .mReady (fun j => (getT (mProbe blank ts) j).focus) = true ↔
      mCond blank endSym mark ts := by
  simp only [condOf9, decide_eq_true_eq]
  rfl

theorem mIter_effect (ts : Tapes sc) (hc : mCond blank endSym mark ts) :
    applyActs blank (mIter blank) (mProbe blank ts) =
      mProbe blank (applyActs blank (mActs blank endSym mark ts) ts) := by
  rw [applyActs_mActs_pos hc]
  rfl

theorem mRUN_stop (ts : Tapes sc) (hc : ¬ mCond blank endSym mark ts) :
    ExecA Terminal blank endSym mark mRUN (mProbe blank ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun h => hc ((mReady_iff ts).mp h))

theorem mRUN_cont (ts : Tapes sc) (hc : mCond blank endSym mark ts)
    (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark mRUN
      (mProbe blank (applyActs blank (mActs blank endSym mark ts) ts)) L) :
    ExecA Terminal blank endSym mark mRUN (mProbe blank ts) (mIter blank ++ L) := by
  have hb : ExecA Terminal blank endSym mark mRunBody
      (applyAct blank (mProbe blank ts) (.Cd blank .stay))
      [.V1 .right, .V2 .right, .Cq blank .right, .Cd blank .left] :=
    execA_seq (execA_v1 .right _) (execA_seq (execA_v2 .right _)
      (execA_seq (execA_ct_put ctCq .right _) (execA_ct_put ctCd .left _)))
  have hx' : ExecA Terminal blank endSym mark mRUN
      (applyActs blank (mIter blank) (mProbe blank ts)) L := by
    rw [mIter_effect ts hc]; exact hx
  exact execA_loop_cont rfl rfl rfl ((mReady_iff ts).mpr hc) hb hx'

def mRunL (blank endSym mark : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts => if mCond blank endSym mark ts then
      mIter blank ++ mRunL blank endSym mark fuel (applyActs blank (mActs blank endSym mark ts) ts)
    else []

theorem mRUN_exec (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel a b : ℕ) (c : Ctr) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b c ts → a ≤ b → x.length ≤ b + fuel →
    ExecA Terminal blank endSym mark mRUN (mProbe blank ts) (mRunL blank endSym mark fuel ts) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c ts he hab hbound
    apply mRUN_stop
    intro hc
    have := ((mCond_iff hend hmark he hab).mp hc).1
    omega
  | succ fuel ih =>
    intro a b c ts he hab hbound
    by_cases hc : mCond blank endSym mark ts
    · rw [mRunL, if_pos hc]
      apply mRUN_cont ts hc
      exact ih (a + 1) (b + 1) _ _ (enc_m_step hend hmark he hab hc) (by omega) (by omega)
    · rw [mRunL, if_neg hc]
      exact mRUN_stop ts hc

theorem mRunL_complete (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel a b : ℕ) (c : Ctr) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b c ts → a ≤ b → x.length < b + fuel →
    ∃ u, applyActs blank (mRunL blank endSym mark fuel ts) (mProbe blank ts) = mProbe blank u ∧
      [.Cd blank .left] ++ mRunL blank endSym mark fuel ts ++ [.Cd (probe blank u.Cd) .right] =
        mProg blank endSym mark fuel ts := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c ts he hab hbound
    have := pat_le he.v2
    omega
  | succ fuel ih =>
    intro a b c ts he hab hbound
    by_cases hc : mCond blank endSym mark ts
    · obtain ⟨u, hu, htrace⟩ := ih (a + 1) (b + 1) _ _
        (enc_m_step hend hmark he hab hc) (by omega) (by omega)
      refine ⟨u, ?_, ?_⟩
      · rw [mRunL, if_pos hc, applyActs_append, mIter_effect ts hc]
        exact hu
      · rw [mRunL, if_pos hc, mProg, if_pos hc, ← htrace]
        simp [mActs, hc, mIter]
    · refine ⟨ts, ?_, ?_⟩
      · simp [mRunL, hc, applyActs]
      · simp [mRunL, mProg, mActs, hc]

theorem FIRST_SCAN_exec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (fuel a b : ℕ) (c : Ctr) (ts : Tapes sc)
    (he : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (hbound : x.length < b + fuel) :
    ExecA Terminal blank endSym mark FIRST_SCAN ts (mProg blank endSym mark fuel ts) := by
  obtain ⟨u, hu, htrace⟩ := mRunL_complete hend hmark fuel a b c ts he hab hbound
  rw [← htrace]
  apply execA_seq (execA_ct_put ctCd .left ts)
  apply execA_seq (mRUN_exec hend hmark fuel a b c ts he hab (by omega))
  rw [hu]
  exact execA_ct_keep ctCd .right _

theorem FIRST_SCAN_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (fuel a b : ℕ) (c : Ctr) (ts : Tapes sc)
    (he : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (hbound : x.length < b + fuel) :
    ∃ L, ExecA Terminal blank endSym mark FIRST_SCAN ts L ∧
      Enc blank startSym endSym mark x (a + mSteps x fuel a b c.d)
        (b + mSteps x fuel a b c.d)
        {c with d := c.d - mSteps x fuel a b c.d, q := c.q + mSteps x fuel a b c.d}
        (applyActs blank L ts) ∧ NoSigned L ∧ L.length ≤ 5 * mWork x fuel a b c.d := by
  exact ⟨mProg blank endSym mark fuel ts, FIRST_SCAN_exec hend hmark fuel a b c ts he hab hbound,
    mProg_spec hend hmark fuel ts a b c he hab, mProg_noSigned blank endSym mark fuel ts,
    mProg_length hend hmark fuel ts a b c he hab⟩

theorem FIRST_SCAN_firstInner (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k s p q E F S R : ℕ) (g : Ctr3) (ts : Tapes sc)
    (hs : s ≤ x.length) (hq : q ≤ (k - 1) * p) (hfit : s + p + q ≤ x.length)
    (he : EncS blank startSym endSym mark x (s + q) (s + p + q)
      ⟨(k - 1) * p - q, q, E, p, F, S, R⟩ g ts) :
    let q' := firstInner (x.drop s) k p ((x.drop s).length + 1) q
    ∃ L, ExecA Terminal blank endSym mark FIRST_SCAN ts L ∧
      EncS blank startSym endSym mark x (s + q') (s + p + q')
        ⟨(k - 1) * p - q', q', E, p, F, S, R⟩ g (applyActs blank L ts) ∧
      q ≤ q' ∧ s + p + q' ≤ x.length ∧ q' ≤ (k - 1) * p ∧
      L.length ≤ 5 * firstInnerWork (x.drop s) k p ((x.drop s).length + 1) q := by
  dsimp only
  let fuel := (x.drop s).length + 1
  let d := (k - 1) * p - q
  have hb : x.length < (s + p + q) + fuel := by
    dsimp [fuel]; rw [List.length_drop]; omega
  obtain ⟨L, hx, hout, hframe, hc⟩ := FIRST_SCAN_spec hend hmark fuel (s + q)
    (s + p + q) ⟨d, q, E, p, F, S, R⟩ ts he.base (by omega) hb
  have hi := mSteps_firstInner (k := k) (p := p) hs fuel q d (by dsimp [d]; omega) hfit
  have hle := mSteps_le_d x fuel (s + q) (s + p + q) d
  have hout' := he.frame hframe hout
  have hh := pat_le hout.v2
  dsimp only [fuel, d] at *
  refine ⟨L, hx, ?_, by omega, ?_, ?_, ?_⟩
  · convert hout' using 1 <;> try omega
    congr 1 <;> omega
  · omega
  · omega
  · rw [hi.2] at hc
    exact hc

/-- info: 'PalPeg.GSPreProg.FIRST_SCAN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_SCAN_spec

end PalPeg.GSPreProg
