import PalPeg.GSPreprocessProg53

/-! # First-search work accounting and finite failure cleanup -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem CLEAN_spec (hmark : mark ≠ blank) {s D P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x s (s + P) ⟨D, 0, 0, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark CLEAN ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩ g
        (applyActs blank L ts) ∧ L.length = 3 * P + 2 * D + 4 := by
  have h1 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s D 0 0 0 F S R ts (by simpa using he.base)
  have h2 := dTest_enc_Cp h1
  rw [← applyActs_append] at h2
  have h3 := he.frame (acts := pvLoop blank P ++ dTest ctCp blank mark)
    (by simp [dTest, Act.noSigned, ctCp]) h2
  have hx1 := pvProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts he.base.cp
  obtain ⟨L2, hx2, h4, hl2⟩ := ERASE_Cd_spec (Terminal := Terminal) hmark h3
  refine ⟨_, execA_seq hx1 hx2, ?_, ?_⟩
  · simpa only [applyActs_append] using h4
  · simp only [List.length_append, pvLoop_length, dTest_length, hl2]
    omega

theorem firstOuter_success_work (v : List (Fin sc)) (k bound : ℕ) (hk : 0 < k)
    (fuel : ℕ) : ∀ p p' m,
    firstOuter v k bound fuel p = some (p', m) →
    p' ≤ p + firstOuterWork v k bound fuel p ∧
      (k - 1) * p' ≤ firstOuterWork v k bound fuel p := by
  induction fuel with
  | zero => intro p p' m h; simp [firstOuter] at h
  | succ fuel ih =>
      intro p p' m h
      by_cases hg : p < v.length ∧ p < bound
      · rw [firstOuter, if_pos hg] at h
        rw [firstOuterWork, if_pos hg]
        by_cases hs : firstInner v k p (v.length + 1) 0 = (k - 1) * p
        · rw [if_pos hs] at h ⊢
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          have hw := firstInner_le_work v k p (v.length + 1) 0
          rw [hs] at hw
          constructor <;> omega
        · rw [if_neg hs] at h ⊢
          obtain ⟨hp, hm⟩ := ih _ _ _ h
          have hw := firstInner_le_work v k p (v.length + 1) 0
          have hd := shiftNoPeriod_le_succ hk (firstInner v k p (v.length + 1) 0)
          constructor <;> omega
      · simp [firstOuter, hg] at h

theorem extendReach_work_span (v : List (Fin sc)) (p fuel r : ℕ) :
    r ≤ extendReach v p fuel r ∧ extendReach v p fuel r ≤ r + extendReachWork v p fuel r := by
  induction fuel generalizing r with
  | zero => simp [extendReach, extendReachWork]
  | succ fuel ih =>
      simp only [extendReach, extendReachWork]
      split
      · have h := ih (r + 1); constructor <;> omega
      · constructor <;> omega

/-- info: 'PalPeg.GSPreProg.CLEAN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CLEAN_spec
end PalPeg.GSPreProg
