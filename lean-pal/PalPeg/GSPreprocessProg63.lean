import PalPeg.GSPreprocessProg62

/-! # Complete finite stripping program, including scratch cleanup -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem FZ_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark fzProg ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, E, P, 0, S, R⟩ g
        (applyActs blank L ts) ∧ L.length = 2 * F + 2 := by
  have h1 := fzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) F a b D Q E P 0 S R ts (by simpa using he.base)
  have h2 := dTest_enc_Cf h1
  rw [← applyActs_append] at h2
  refine ⟨_, fzProg_exec hmark F ts he.base.cf,
    he.frame (by simp [dTest, Act.noSigned, ctCf]) h2, ?_⟩
  simp

def STRIP_CLEAN : Prog A9 Cond9 :=
  .seq ezProg (.seq CLEAN (.seq (DLOOP tCa .skip) fzProg))

theorem STRIP_CLEAN_spec (hmark : mark ≠ blank) (k : ℕ)
    {s P E F : ℕ} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x s (s + P)
      ⟨(k - 1) * P, 0, E, P, F, s, 0⟩ ⟨F - P, 0, 0⟩ ts) :
    ∃ L, ExecA Terminal blank endSym mark STRIP_CLEAN ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, s, 0⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ (2 * k + 3) * P + 2 * E + 4 * F + 10 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := EZ_spec (Terminal := Terminal) hmark he
  obtain ⟨L2, hx2, h2, hl2⟩ := CLEAN_spec (Terminal := Terminal) hmark h1
  obtain ⟨L3, hx3, h3, hl3⟩ := ERASE_Ca_spec (Terminal := Terminal) hmark h2
  obtain ⟨L4, hx4, h4, hl4⟩ := FZ_spec (Terminal := Terminal) hmark h3
  refine ⟨_, execA_seq hx1 (execA_seq hx2 (execA_seq hx3 hx4)), ?_, ?_⟩
  · simpa only [applyActs_append] using h4
  · simp only [List.length_append, hl1, hl2, hl3, hl4]
    have hm := Nat.mul_le_mul_right P (Nat.sub_le k 1)
    nlinarith only [hm, Nat.sub_le F P]

def STRIP (k : ℕ) : Prog A9 Cond9 :=
  .seq COPY_FA (.seq (STRIP_CORE k) STRIP_CLEAN)

theorem STRIP_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k F : ℕ) (hk : 3 ≤ k) (fuel : ℕ) {s : ℕ} {ts : Tapes sc}
    (hs : s ≤ x.length) (hf : x.length ≤ s + fuel)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, F, s, 0⟩ ⟨0, 0, 0⟩ ts) :
    let t := stripLoop2 x k F fuel s
    ∃ L, ExecA Terminal blank endSym mark (STRIP k) ts L ∧
      EncS blank startSym endSym mark x t t ⟨0, 0, 0, 0, 0, t, 0⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ (stripRate k + 2 * k + 9) * stripLoop2Work x k F fuel s +
        11 * F + 3 * k + 42 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := COPY_FA_spec (Terminal := Terminal) hmark he
  obtain ⟨L2, P, E, hx2, h2, _, hE, _, hP, hl2⟩ := STRIP_CORE_spec
    (Terminal := Terminal) hend hmark k F hk fuel hs hf (by simpa using h1)
  obtain ⟨L3, hx3, h3, hl3⟩ := STRIP_CLEAN_spec (Terminal := Terminal) hmark k h2
  refine ⟨_, execA_seq hx1 (execA_seq hx2 hx3), ?_, ?_⟩
  · simpa only [applyActs_append] using h3
  · simp only [List.length_append]
    have hm := Nat.mul_le_mul_left (2 * k + 3) hP
    nlinarith only [hl1, hl2, hl3, hE, hm]

/-- info: 'PalPeg.GSPreProg.STRIP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_spec
end PalPeg.GSPreProg
