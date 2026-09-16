import PalPeg.GSPreprocessProg55

/-! # Finite post-search reset and finalization -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

@[simp] theorem fcLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (fcLoop blank n) := by
  induction n with
  | zero => simp [fcLoop]
  | succ n ih => simp [fcLoop, fcUnit, Act.noSigned, ih]

theorem resetActs_enc {s Q P F S R D : ℕ} {ts : Tapes sc}
    (he : Enc blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, 0, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, P, S, 0⟩
      (applyActs blank (resetActs blank mark Q F P R D) ts) := by
  have h0 := he
  have h1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) Q s (s + P) D 0 0 P F S R _ (by simpa using h0)
  have h1 := dTest_enc_Cq h1
  rw [← applyActs_append] at h1
  have h2 := fzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) F s (s + P) D 0 0 P 0 S R _ (by simpa using h1)
  have h2 := dTest_enc_Cf h2
  rw [← applyActs_append] at h2
  have h3 := pfvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s D 0 0 0 0 S R _ (by simpa using h2)
  simp only [Nat.zero_add] at h3
  have h3 := dTest_enc_Cp h3
  rw [← applyActs_append] at h3
  have h4 := rzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) R s s D 0 0 0 P S 0 _ (by simpa using h3)
  have h4 := dTest_enc_Cr h4
  rw [← applyActs_append] at h4
  have h5 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) D s s 0 0 0 0 P S 0 _ (by simpa using h4)
  have h5 := dTest_enc_Cd h5
  rw [← applyActs_append] at h5
  simpa only [resetActs, applyActs_append] using h5

theorem RESET_spec (hmark : mark ≠ blank) {s Q P F R D : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, 0, P, F, s, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark RESET ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, P, s, 0⟩ g
        (applyActs blank L ts) ∧ L.length = 4 * Q + 2 * F + 4 * P + 2 * R + 2 * D + 10 := by
  refine ⟨resetActs blank mark Q F P R D, RESET_exec hmark he.base,
    he.frame (by simp [resetActs, dTest, Act.noSigned, ctCq, ctCf, ctCp, ctCr, ctCd])
      (resetActs_enc he.base), ?_⟩
  simp

theorem swapActs_enc {s Q P F S R D : ℕ} {ts : Tapes sc}
    (he : Enc blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, 0, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, F, 0, S, R⟩
      (applyActs blank (swapActs blank mark Q P F D) ts) := by
  have h0 := he
  have h1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) Q s (s + P) D 0 0 P F S R _ (by simpa using h0)
  have h1 := dTest_enc_Cq h1
  rw [← applyActs_append] at h1
  have h2 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s D 0 0 0 F S R _ (by simpa using h1)
  have h2 := dTest_enc_Cp h2
  rw [← applyActs_append] at h2
  have h3 := fcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) F s s D 0 0 0 0 S R _ (by simpa using h2)
  simp only [Nat.zero_add] at h3
  have h3 := dTest_enc_Cf h3
  rw [← applyActs_append] at h3
  have h4 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) D s s 0 0 0 F 0 S R _ (by simpa using h3)
  have h4 := dTest_enc_Cd h4
  rw [← applyActs_append] at h4
  simpa only [swapActs, applyActs_append] using h4

theorem SWAP_spec (hmark : mark ≠ blank) {s Q P F R D : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, 0, P, F, s, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark SWAP ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, F, 0, s, R⟩ g
        (applyActs blank L ts) ∧ L.length = 4 * Q + 3 * P + 3 * F + 2 * D + 8 := by
  refine ⟨swapActs blank mark Q P F D, SWAP_exec hmark he.base,
    he.frame (by simp [swapActs, dTest, Act.noSigned, ctCq, ctCf, ctCp, ctCd])
      (swapActs_enc he.base), ?_⟩
  simp

theorem EZ_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark ezProg ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g
        (applyActs blank L ts) ∧ L.length = 2 * E + 2 := by
  have h1 := ezLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) E a b D Q 0 P F S R ts (by simpa using he.base)
  have h2 := dTest_enc_Ce h1
  rw [← applyActs_append] at h2
  refine ⟨_, ezProg_exec hmark E ts he.base.ce,
    he.frame (by simp [dTest, Act.noSigned, ctCe]) h2, ?_⟩
  simp

theorem DRST_spec (hmark : mark ≠ blank) {s Q E P F R D : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, E, P, F, s, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark DRST ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, P, s, 0⟩ g
        (applyActs blank L ts) ∧
      L.length = 2 * E + 4 * Q + 2 * F + 4 * P + 2 * R + 2 * D + 12 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := EZ_spec (Terminal := Terminal) hmark he
  obtain ⟨L2, hx2, h2, hl2⟩ := RESET_spec (Terminal := Terminal) hmark h1
  refine ⟨_, execA_seq hx1 hx2, ?_, ?_⟩
  · simpa only [applyActs_append] using h2
  · rw [List.length_append, hl1, hl2]; omega

theorem DSWAP_spec (hmark : mark ≠ blank) {s Q E P F R D : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x (s + Q) (s + P + Q)
      ⟨D, Q, E, P, F, s, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark DSWAP ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, F, 0, s, R⟩ g
        (applyActs blank L ts) ∧
      L.length = 2 * E + 4 * Q + 3 * P + 3 * F + 2 * D + 10 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := EZ_spec (Terminal := Terminal) hmark he
  obtain ⟨L2, hx2, h2, hl2⟩ := SWAP_spec (Terminal := Terminal) hmark h1
  refine ⟨_, execA_seq hx1 hx2, ?_, ?_⟩
  · simpa only [applyActs_append] using h2
  · rw [List.length_append, hl1, hl2]; omega

/-- info: 'PalPeg.GSPreProg.DRST_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DRST_spec
/-- info: 'PalPeg.GSPreProg.DSWAP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DSWAP_spec
end PalPeg.GSPreProg
