import PalPeg.GSPreprocessProg49

/-! # Finite repositioning between the two searches -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def REPO : Prog A9 Cond9 :=
  .seq pfProg (.seq cpProg (.seq prProg (.seq cpProg
    (.seq rvProg (.seq crProg (.seq pcProg (.seq cpProg PVM1)))))))

theorem REPO_spec (hmark : mark ≠ blank) {s P R D S : ℕ}
    {g : Ctr3} {ts : Tapes sc} (hP : 0 < P) (hPR : P ≤ R)
    (he : EncS blank startSym endSym mark x (s + (R - P)) (s + R)
      ⟨D, 0, 0, P, 0, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark REPO ts L ∧
      EncS blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, P, S, R⟩ g
        (applyActs blank L ts) ∧ L.length ≤ 8 * R + 17 * P + 23 := by
  have e0 : (0 : ℕ) + P = P := by omega
  have eR : (0 : ℕ) + (R - P) = R - P := by omega
  have ePR : R - P + P = R := by omega
  have es : s + P + (R - P) = s + R := by omega
  have h0 := he.base
  let L1 := pfLoop blank P ++ dTest (ctCp : CT sc) blank mark
  have hx1 := pfProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h0.cp
  have h1 := pfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 0 S R _ (by rw [e0]; exact h0)
  rw [e0] at h1
  have h1 := dTest_enc_Cp h1
  rw [← applyActs_append] at h1
  let L2 := cpLoop blank P ++ dTest (ctCe : CT sc) blank mark
  have hx2 := cpProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h1.ce
  have h2 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S R _ (by rw [e0]; exact h1)
  rw [e0] at h2
  have h2 := dTest_enc_Ce h2
  rw [← applyActs_append] at h2
  let L3 := prLoop blank P ++ dTest (ctCp : CT sc) blank mark
  have hx3 := prProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h2.cp
  have h3 := prLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S (R - P) _ (by rw [e0, ePR]; exact h2)
  rw [e0] at h3
  have h3 := dTest_enc_Cp h3
  rw [← applyActs_append] at h3
  let L4 := cpLoop blank P ++ dTest (ctCe : CT sc) blank mark
  have hx4 := cpProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h3.ce
  have h4 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S (R - P) _ (by rw [e0]; exact h3)
  rw [e0] at h4
  have h4 := dTest_enc_Ce h4
  rw [← applyActs_append] at h4
  let L5 := rvLoop blank (R - P) ++ dTest (ctCr : CT sc) blank mark
  have hx5 := rvProg_exec (Terminal := Terminal) (endSym := endSym) hmark (R - P) _ h4.cr
  have h5 := rvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P P S 0 _ (by rw [eR, es]; exact h4)
  rw [eR] at h5
  have h5 := dTest_enc_Cr h5
  rw [← applyActs_append] at h5
  let L6 := crLoop blank (R - P) ++ dTest (ctCe : CT sc) blank mark
  have hx6 := crProg_exec (Terminal := Terminal) (endSym := endSym) hmark (R - P) _ h5.ce
  have h6 := crLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P P S 0 _ (by rw [eR]; exact h5)
  rw [eR] at h6
  have h6 := dTest_enc_Ce h6
  rw [← applyActs_append] at h6
  let L7 := pcLoop blank P ++ dTest (ctCp : CT sc) blank mark
  have hx7 := pcProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h6.cp
  have h7 := pcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s (s + P) D 0 0 0 P S (R - P) _ (by rw [e0]; exact h6)
  rw [e0, ePR] at h7
  have h7 := dTest_enc_Cp h7
  rw [← applyActs_append] at h7
  let L8 := cpLoop blank P ++ dTest (ctCe : CT sc) blank mark
  have hx8 := cpProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h7.ce
  have h8 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s (s + P) D 0 0 0 P S R _ (by rw [e0]; exact h7)
  rw [e0] at h8
  have h8 := dTest_enc_Ce h8
  rw [← applyActs_append] at h8
  have hx9 := PVM1_exec (Terminal := Terminal) hmark h8
  have h9 := PVM1_enc hP h8
  let L := L1 ++ (L2 ++ (L3 ++ (L4 ++ (L5 ++ (L6 ++ (L7 ++
    (L8 ++ pvm1Acts blank mark P)))))))
  have hx : ExecA Terminal blank endSym mark REPO ts L :=
    execA_seq hx1 (execA_seq hx2 (execA_seq hx3 (execA_seq hx4
      (execA_seq hx5 (execA_seq hx6 (execA_seq hx7 (execA_seq hx8 hx9)))))))
  have hn : NoSigned L := by
    simp [L, L1, L2, L3, L4, L5, L6, L7, L8, pvm1Acts,
      dTest, Act.noSigned, ctCp, ctCe, ctCr]
  refine ⟨L, hx, he.frame hn ?_, ?_⟩
  · simpa only [L, L1, L2, L3, L4, L5, L6, L7, L8, applyActs_append] using h9
  · simp only [L, L1, L2, L3, L4, L5, L6, L7, L8, List.length_append,
      pfLoop_length, cpLoop_length, prLoop_length, rvLoop_length, crLoop_length,
      pcLoop_length, dTest_length, pvm1Acts_length blank mark hP, pvLoop_length]
    omega

/-- info: 'PalPeg.GSPreProg.REPO_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms REPO_spec
end PalPeg.GSPreProg

