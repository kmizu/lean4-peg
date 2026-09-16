import PalPeg.GSPreprocessProg58

/-! # Finite cut advancement with restoration of the candidate bound -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

@[simp] theorem subKActs_noSigned (blank mark : Fin sc) (p k : ℕ) :
    NoSigned (subKActs blank mark p k) := by
  induction k with
  | zero => simp [subKActs]
  | succ k ih => simp [subKActs, dTest, Act.noSigned, ctCp, ctCq, ih]

def ADVANCE_BOUND (k : ℕ) : Prog A9 Cond9 :=
  .seq REWIND_TO_CUT (.seq (SUBK k) (.seq csProg
    (.seq (.seq (.act (tCs, .blk, .right))
      (.seq (.act (tV1, .keep, .right)) (.act (tV2, .keep, .right)))) PA)))

theorem ADVANCE_BOUND_spec (hmark : mark ≠ blank) (k : ℕ)
    {s P R D F S : ℕ} {g : Ctr3} {ts : Tapes sc} (hkp : k * P ≤ R) (hpr : P ≤ R)
    (hfit : s + (R - k * P + 1) ≤ x.length)
    (he : EncS blank startSym endSym mark x (s + (R - P)) (s + R)
      ⟨D, 0, 0, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark (ADVANCE_BOUND k) ts L ∧
      EncS blank startSym endSym mark x (s + (R - k * P + 1)) (s + (R - k * P + 1))
        ⟨D, 0, 0, 0, F, S + (R - k * P + 1), 0⟩ ⟨g.ap + P, g.an, g.bn⟩
        (applyActs blank L ts) ∧ L.length ≤ 24 * R + 3 * (k * P) + 4 * k + 17 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := REWIND_TO_CUT_spec (Terminal := Terminal) hmark hpr he
  have h2in : Enc blank startSym endSym mark x s s
      ⟨D, 0, (R - k * P) + k * P, P, F, S, 0⟩ (applyActs blank L1 ts) := by
    rw [Nat.sub_add_cancel hkp]; exact h1.base
  have hx2 := SUBK_exec (Terminal := Terminal) hmark P k s s D (R - k * P) F S 0 _ h2in
  have h2 := h1.frame (subKActs_noSigned blank mark P k)
    (SUBK_enc P k s s D (R - k * P) F S 0 _ h2in)
  have hx3 := csProg_exec (Terminal := Terminal) (endSym := endSym) hmark (R - k * P) _ h2.base.ce
  have h3 := csLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - k * P) s s D 0 0 P F S 0 _
      (by simpa using h2.base) (by omega) (by omega)
  have h3 := dTest_enc_Ce h3
  rw [← applyActs_append] at h3
  have h3s := h2.frame (acts := csLoop blank (R - k * P) ++ dTest ctCe blank mark)
    (by simp [dTest, Act.noSigned, ctCe]) h3
  let t3 := applyActs blank (csLoop blank (R - k * P) ++ dTest ctCe blank mark)
    (applyActs blank (subKActs blank mark P k) (applyActs blank L1 ts))
  let L4 := [Act.Cs blank .right, Act.V1 .right, Act.V2 .right]
  have hx4 : ExecA Terminal blank endSym mark
      (.seq (.act (tCs, .blk, .right))
        (.seq (.act (tV1, .keep, .right)) (.act (tV2, .keep, .right)))) t3 L4 :=
    execA_seq (execA_ct_put ctCs .right _) (execA_seq (execA_v1 .right _) (execA_v2 .right _))
  have h4 : EncS blank startSym endSym mark x (s + (R - k * P) + 1) (s + (R - k * P) + 1)
      ⟨D, 0, 0, P, F, S + (R - k * P) + 1, 0⟩ g (applyActs blank L4 t3) :=
    ⟨⟨pat_right h3s.base.v1 (by omega), pat_right h3s.base.v2 (by omega),
      h3s.base.cd, h3s.base.cq, h3s.base.ce, h3s.base.cp, h3s.base.cf,
      Tape.counter'_inc h3s.base.cs, h3s.base.cr⟩, h3s.ca, h3s.cb, h3s.cc⟩
  obtain ⟨L5, hx5, h5, hl5⟩ := PA_spec (Terminal := Terminal) hmark h4
  refine ⟨_, execA_seq hx1 (execA_seq hx2 (execA_seq hx3 (execA_seq hx4 hx5))), ?_, ?_⟩
  · simpa only [applyActs_append, t3, Nat.add_assoc] using h5
  · simp only [List.length_append, hl1, dTest_length, subKActs_length, subKLoop_length,
      csLoop_length, hl5, L4, List.length_cons, List.length_nil]
    have hm : 8 * P * k = 8 * (k * P) := by ring
    omega

/-- info: 'PalPeg.GSPreProg.ADVANCE_BOUND_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADVANCE_BOUND_spec
end PalPeg.GSPreProg
