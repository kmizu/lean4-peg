import PalPeg.GSPreprocessProg54

/-! # A complete finite search step of the decomposition procedure -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def STEP_SEARCH (k : ℕ) : Prog A9 Cond9 :=
  .seq (FIRST_PHASE false k) (CD_CASE CLEAN (SECOND_PHASE k))

def stepRate (k : ℕ) : ℕ := foRate k + soRRate k + 2 * k + 90

theorem STEP_SEARCH_success (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s S p m : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, S, 0⟩ ⟨0, 0, 0⟩ ts)
    (hfp : firstPeriod (x.drop s) k = some (p, m)) :
    let r := extendReach (x.drop s) p (x.length + 1) m
    ∃ L E P, ExecA Terminal blank endSym mark (STEP_SEARCH k) ts L ∧
      EncS blank startSym endSym mark x s (s + P) ⟨0, 0, E, P, p, S, r⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      s + P ≤ x.length ∧
      P ≤ 1 + secondOuterWork (x.drop s) k p r ((x.drop s).length + 1) 1 0 ∧
      (∀ p2, secondPeriod (x.drop s) k p r = some p2 → P = p2) ∧
      E = (if (secondPeriod (x.drop s) k p r).isSome then 1 else 0) ∧
      L.length ≤ stepRate k * decomposeStepWork x k s + 4 * k + 112 := by
  dsimp only
  have hp := firstOuter_pos (x.drop s) k (x.drop s).length _ 1 p m (by omega) hfp
  have hm := firstOuter_snd (x.drop s) k (x.drop s).length _ 1 p m hfp
  have hr := extendReach_work_span (x.drop s) p (x.length + 1) m
  have hw := firstOuter_success_work (x.drop s) k (x.drop s).length (by omega) _ 1 p m hfp
  obtain ⟨L1, hx1, h1, hl1⟩ := FIRST_PHASE_success (Terminal := Terminal)
    hend hmark false 0 k s 0 S 0 0 ((x.drop s).length + 1) p m (by omega) hs ts
      (by simpa [foBound] using he) (by omega) (by simpa [foLimit, firstPeriod] using hfp)
  simp only [foBound, foLimit, Bool.false_eq_true, if_false] at h1 hl1
  obtain ⟨L2, E, P, hx2, h2, hfit, hsize, hans, hflag, hl2⟩ := SECOND_PHASE_spec
    (Terminal := Terminal) hend hmark k ((x.drop s).length + 1) hk hp (by omega) h1 (by omega)
  let t1 := applyActs blank L1 ts
  have hx3 := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t1 h1.base.cd
    CLEAN (SECOND_PHASE k) L2 (by simpa using hx2)
  have hrestore := cdCaseTest_restore t1 h1.base.cd
  have hfin : applyActs blank (L1 ++ (cdCaseTest blank t1 ++ L2)) ts =
      applyActs blank L2 t1 := by
    rw [applyActs_append, applyActs_append]
    change applyActs blank L2 (applyActs blank (cdCaseTest blank t1) t1) = _
    rw [hrestore]
  refine ⟨_, E, P, execA_seq hx1 hx3, ?_, hfit, hsize, hans, hflag, ?_⟩
  · rw [hfin]; exact h2
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    rw [decomposeStepWork, hfp]
    dsimp only
    have hk1 : k - 1 ≤ k := Nat.sub_le k 1
    have ha : 0 ≤ foRate k * secondOuterWork (x.drop s) k p
        (extendReach (x.drop s) p (x.length + 1) m) ((x.drop s).length + 1) 1 0 := Nat.zero_le _
    unfold stepRate
    nlinarith only [hl1, hl2, hw.1, hw.2, hr.2, hm, hk1,
      Nat.zero_le (foRate k), Nat.zero_le (soRRate k), ha]

theorem STEP_SEARCH_failure (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s S : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, S, 0⟩ ⟨0, 0, 0⟩ ts)
    (hfp : firstPeriod (x.drop s) k = none) :
    ∃ L, ExecA Terminal blank endSym mark (STEP_SEARCH k) ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, S, 0⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ stepRate k * decomposeStepWork x k s + 4 * k + 112 := by
  obtain ⟨L1, P, hx1, h1, hp, _, hsize, _, hl1⟩ := FIRST_PHASE_failure
    (Terminal := Terminal) hend hmark false 0 k s 0 S 0 0 ((x.drop s).length + 1)
      (by omega) hs ts (by simpa [foBound] using he) (by omega)
      (by simpa [foLimit, firstPeriod] using hfp)
  simp only [foBound, foLimit, Bool.false_eq_true, if_false] at h1 hl1 hsize
  obtain ⟨L2, hx2, h2, hl2⟩ := CLEAN_spec (Terminal := Terminal) hmark h1
  let t1 := applyActs blank L1 ts
  have hd : (k - 1) * P ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by omega) hp)
  have hx3 := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t1 h1.base.cd
    CLEAN (SECOND_PHASE k) L2 (by rw [if_neg hd]; exact hx2)
  have hr := cdCaseTest_restore t1 h1.base.cd
  refine ⟨_, execA_seq hx1 hx3, ?_, ?_⟩
  · rw [applyActs_append, applyActs_append]
    change EncS blank startSym endSym mark x s s _ _
      (applyActs blank L2 (applyActs blank (cdCaseTest blank t1) t1))
    rw [hr]; exact h2
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil, hl2]
    rw [decomposeStepWork, hfp]
    dsimp only
    have hk1 : k - 1 ≤ k := Nat.sub_le k 1
    have hscale := Nat.mul_le_mul_left (2 * k + 3) hsize
    have hdscale := Nat.mul_le_mul_right P hk1
    unfold stepRate
    nlinarith only [hl1, hscale, hdscale, hk1, Nat.zero_le (soRRate k)]

/-- info: 'PalPeg.GSPreProg.STEP_SEARCH_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STEP_SEARCH_failure

/-- info: 'PalPeg.GSPreProg.STEP_SEARCH_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STEP_SEARCH_success
end PalPeg.GSPreProg
