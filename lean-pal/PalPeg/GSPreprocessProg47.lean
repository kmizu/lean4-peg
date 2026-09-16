import PalPeg.GSPreprocessProg46

/-! # Scratch-preserving transfer of first-search results -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

@[simp] theorem loadRActs_noSigned (blank mark : Fin sc) (Q P : ℕ) :
    NoSigned (loadRActs blank mark Q P) := by
  simp [loadRActs, dTest, Act.noSigned, ctCq, ctCp, ctCe]

theorem LOADR_spec (hmark : mark ≠ blank) {a b D P Q F S : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, 0⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark LOADR ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, 0, 0, P, F, S, Q + P⟩ g
        (applyActs blank L ts) ∧ L.length = 3 * Q + 7 * P + 6 := by
  refine ⟨loadRActs blank mark Q P, LOADR_exec hmark he.base,
    he.frame (loadRActs_noSigned blank mark Q P) (LOADR_enc he.base), ?_⟩
  simp

def LOAD_EXTEND : Prog A9 Cond9 := .seq LOADR EXTEND_REACH

theorem LOAD_EXTEND_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (fuel a b D P Q F S : ℕ) (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, 0⟩ g ts)
    (hab : a ≤ b) (hbound : x.length ≤ b + fuel) :
    ∃ L, ExecA Terminal blank endSym mark LOAD_EXTEND ts L ∧
      EncS blank startSym endSym mark x (a + rSteps x fuel a b) (b + rSteps x fuel a b)
        ⟨D, 0, 0, P, F, S, Q + P + rSteps x fuel a b⟩ g (applyActs blank L ts) ∧
      L.length ≤ 3 * Q + 7 * P + 6 + 3 * rWork x fuel a b := by
  obtain ⟨L₁, hx₁, he₁, hl₁⟩ := LOADR_spec (Terminal := Terminal) hmark he
  obtain ⟨L₂, hx₂, he₂, hl₂⟩ := EXTEND_REACH_spec (Terminal := Terminal)
    hend hmark fuel a b _ g _ he₁ hab hbound
  refine ⟨L₁ ++ L₂, execA_seq hx₁ hx₂, ?_, ?_⟩
  · simpa only [applyActs_append] using he₂
  · rw [List.length_append, hl₁]
    omega

/-- info: 'PalPeg.GSPreProg.LOAD_EXTEND_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LOAD_EXTEND_spec

/-- info: 'PalPeg.GSPreProg.LOADR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LOADR_spec

end PalPeg.GSPreProg
