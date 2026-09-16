import PalPeg.GSPreprocessProg59

/-! # One finite stripping iteration, including candidate-bound restoration -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def STRIP_STEP (k : ℕ) : Prog A9 Cond9 :=
  .seq (FIRST_PHASE true k) (CD_CASE .skip (ADVANCE_BOUND k))

def stripRate (k : ℕ) : ℕ := foRate k + 5 * k + 250

theorem STRIP_STEP_success (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s F p m : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts)
    (hfp : firstOuter (x.drop s) k F (x.length + 1) 1 = some (p, m)) :
    let r := extendReach (x.drop s) p (x.length + 1) (k * p)
    let s' := s + (r - k * p + 1)
    ∃ L, ExecA Terminal blank endSym mark (STRIP_STEP k) ts L ∧
      EncS blank startSym endSym mark x s' s' ⟨0, 0, 0, 0, F, s', 0⟩
        ⟨F, 0, 0⟩ (applyActs blank L ts) ∧ s < s' ∧ s' ≤ x.length ∧
      L.length ≤ stripRate k * (firstOuterWork (x.drop s) k F (x.length + 1) 1 +
        extendReachWork (x.drop s) p (x.length + 1) (k * p)) := by
  dsimp only
  have hp := firstOuter_pos (x.drop s) k F _ 1 p m (by omega) hfp
  have hpf := firstOuter_lt_bound (x.drop s) k F _ 1 p m hfp
  have hm := firstOuter_snd (x.drop s) k F _ 1 p m hfp
  have hk1 : k - 1 + 1 = k := by omega
  have hm' : m = k * p := by nlinarith only [hm, congrArg (fun z => z * p) hk1]
  clear hm
  subst m
  have hr := extendReach_work_span (x.drop s) p (x.length + 1) (k * p)
  have hw := firstOuter_success_work (x.drop s) k F (by omega) _ 1 p (k * p) hfp
  have hwpos := firstOuterWork_pos (x.drop s) k F _ 1 p (k * p) hfp
  obtain ⟨L1, hx1, h1, hl1⟩ := FIRST_PHASE_success (Terminal := Terminal)
    hend hmark true F k s F s 0 0 (x.length + 1) p (k * p) (by omega) hs ts
      (by simpa [foBound] using he) (by simp; omega) (by simpa only [foLimit, if_true] using hfp)
  simp only [foBound, foLimit, if_true] at h1 hl1
  have hkp : p ≤ k * p := by nlinarith only [hk, Nat.zero_le p]
  have hkp0 : 0 < k * p := Nat.mul_pos (by omega) hp
  have hfit := pat_le h1.base.v2
  obtain ⟨L2, hx2, h2, hl2⟩ := ADVANCE_BOUND_spec (Terminal := Terminal) hmark k
    hr.1 (by omega) (by omega) h1
  let t1 := applyActs blank L1 ts
  have hx3 := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t1 h1.base.cd
    .skip (ADVANCE_BOUND k) L2 (by simpa using hx2)
  have hrestore := cdCaseTest_restore t1 h1.base.cd
  refine ⟨_, execA_seq hx1 hx3, ?_, by omega, by omega, ?_⟩
  · rw [applyActs_append, applyActs_append]
    change EncS blank startSym endSym mark x _ _ _ _
      (applyActs blank L2 (applyActs blank (cdCaseTest blank t1) t1))
    rw [hrestore]
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hpf)] using h2
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    have hscale := Nat.mul_le_mul_left (5 * k + 69) hwpos
    unfold stripRate
    nlinarith only [hl1, hl2, hr.2, hw.1, hw.2, hscale,
      congrArg (fun z => z * p) hk1, Nat.sub_le k 1, Nat.zero_le (foRate k)]

theorem STRIP_STEP_failure (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s F : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts)
    (hfp : firstOuter (x.drop s) k F (x.length + 1) 1 = none) :
    ∃ L P, ExecA Terminal blank endSym mark (STRIP_STEP k) ts L ∧
      EncS blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, s, 0⟩
        ⟨F - P, 0, 0⟩ (applyActs blank L ts) ∧ 0 < P ∧ s + P ≤ x.length ∧
      P ≤ 1 + firstOuterWork (x.drop s) k F (x.length + 1) 1 ∧
      L.length ≤ foRate k * firstOuterWork (x.drop s) k F (x.length + 1) 1 + k + 12 := by
  obtain ⟨L1, P, hx1, h1, hp, hfit, hsize, _, hl1⟩ := FIRST_PHASE_failure
    (Terminal := Terminal) hend hmark true F k s F s 0 0 (x.length + 1)
      (by omega) hs ts (by simpa [foBound] using he) (by simp; omega)
      (by simpa only [foLimit, if_true] using hfp)
  simp only [foBound, foLimit, if_true] at h1 hl1 hsize
  let t1 := applyActs blank L1 ts
  have hd : (k - 1) * P ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by omega) hp)
  have hx2 := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t1 h1.base.cd
    .skip (ADVANCE_BOUND k) [] (by rw [if_neg hd]; exact execA_skip)
  have hr := cdCaseTest_restore t1 h1.base.cd
  refine ⟨_, P, execA_seq hx1 hx2, ?_, hp, hfit, hsize, ?_⟩
  · simp only [List.append_nil, applyActs_append]
    change EncS blank startSym endSym mark x s (s + P) _ _
      (applyActs blank (cdCaseTest blank t1) t1)
    rw [hr]; exact h1
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.STRIP_STEP_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_STEP_success
/-- info: 'PalPeg.GSPreProg.STRIP_STEP_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_STEP_failure
end PalPeg.GSPreProg
