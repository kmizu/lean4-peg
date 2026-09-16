import PalPeg.GSPreprocessProg51

/-! # Finite cleanup of the signed scratch counters -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem dPow_nil_eq_erase (ct : CT sc) (n : ℕ) :
    dPow ct blank [] n = eraseCells ct.act blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

theorem ERASE_exec (ct : CT sc) (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (he : Tape.CounterView' blank mark (ct.get ts) n) :
    ExecA Terminal blank endSym mark (DLOOP ct.idx .skip) ts
      (eraseCells ct.act blank n ++ dTest ct blank mark) := by
  simpa only [dPow_nil_eq_erase] using
    dLoop_exec (Terminal := Terminal) (endSym := endSym) ct .skip [] hmark
      (fun _ => execA_skip) (fun _ => rfl) n ts he

theorem ERASE_Ca_spec (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    ∃ L, ExecA Terminal blank endSym mark (DLOOP tCa .skip) ts L ∧
      EncS blank startSym endSym mark x a b c ({g with ap := 0}) (applyActs blank L ts) ∧
      L.length = 2 * g.ap + 2 := by
  have h1 := eraseCells_Ca_enc g.ap (g := {g with ap := 0}) (by simpa using he)
  have h2 : EncS blank startSym endSym mark x a b c ({g with ap := 0})
      (applyActs blank (dTest ctCa blank mark)
        (applyActs blank (eraseCells Act.Ca blank g.ap) ts)) :=
    ⟨⟨h1.base.v1, h1.base.v2, h1.base.cd, h1.base.cq, h1.base.ce, h1.base.cp,
      h1.base.cf, h1.base.cs, h1.base.cr⟩, Tape.counter'_dec_zero h1.ca, h1.cb, h1.cc⟩
  refine ⟨_, ERASE_exec ctCa hmark g.ap ts he.ca, ?_, ?_⟩
  · simpa only [applyActs_append, ctCa] using h2
  · simp [ctCa]

theorem ERASE_Cb_spec (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    ∃ L, ExecA Terminal blank endSym mark (DLOOP tCb .skip) ts L ∧
      EncS blank startSym endSym mark x a b c ({g with an := 0}) (applyActs blank L ts) ∧
      L.length = 2 * g.an + 2 := by
  have h1 := eraseCells_Cb_enc g.an (g := {g with an := 0}) (by simpa using he)
  have h2 : EncS blank startSym endSym mark x a b c ({g with an := 0})
      (applyActs blank (dTest ctCb blank mark)
        (applyActs blank (eraseCells Act.Cb blank g.an) ts)) :=
    ⟨⟨h1.base.v1, h1.base.v2, h1.base.cd, h1.base.cq, h1.base.ce, h1.base.cp,
      h1.base.cf, h1.base.cs, h1.base.cr⟩, h1.ca, Tape.counter'_dec_zero h1.cb, h1.cc⟩
  refine ⟨_, ERASE_exec ctCb hmark g.an ts he.cb, ?_, ?_⟩
  · simpa only [applyActs_append, ctCb] using h2
  · simp [ctCb]

theorem ERASE_Cc_spec (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    ∃ L, ExecA Terminal blank endSym mark (DLOOP tCc .skip) ts L ∧
      EncS blank startSym endSym mark x a b c ({g with bn := 0}) (applyActs blank L ts) ∧
      L.length = 2 * g.bn + 2 := by
  have h1 := eraseCells_Cc_enc g.bn (g := {g with bn := 0}) (by simpa using he)
  have h2 : EncS blank startSym endSym mark x a b c ({g with bn := 0})
      (applyActs blank (dTest ctCc blank mark)
        (applyActs blank (eraseCells Act.Cc blank g.bn) ts)) :=
    ⟨⟨h1.base.v1, h1.base.v2, h1.base.cd, h1.base.cq, h1.base.ce, h1.base.cp,
      h1.base.cf, h1.base.cs, h1.base.cr⟩, h1.ca, h1.cb, Tape.counter'_dec_zero h1.cc⟩
  refine ⟨_, ERASE_exec ctCc hmark g.bn ts he.cc, ?_, ?_⟩
  · simpa only [applyActs_append, ctCc] using h2
  · simp [ctCc]

theorem ERASE_Cd_spec (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    ∃ L, ExecA Terminal blank endSym mark (DLOOP tCd .skip) ts L ∧
      EncS blank startSym endSym mark x a b ({c with d := 0}) g (applyActs blank L ts) ∧
      L.length = 2 * c.d + 2 := by
  have h1 := eraseCells_Cd_enc c.d (c := {c with d := 0}) (by simpa using he)
  have h2 := h1.frame (acts := dTest ctCd blank mark)
    (by simp [dTest, Act.noSigned, ctCd]) (dTest_enc_Cd h1.base)
  refine ⟨_, ERASE_exec ctCd hmark c.d ts he.base.cd, ?_, ?_⟩
  · simpa only [applyActs_append, ctCd] using h2
  · simp [ctCd]

def CLEAR_SIGNED : Prog A9 Cond9 :=
  .seq (DLOOP tCd .skip) (.seq (DLOOP tCa .skip)
    (.seq (DLOOP tCb .skip) (DLOOP tCc .skip)))

theorem CLEAR_SIGNED_spec (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    ∃ L, ExecA Terminal blank endSym mark CLEAR_SIGNED ts L ∧
      EncS blank startSym endSym mark x a b ({c with d := 0}) ⟨0, 0, 0⟩
        (applyActs blank L ts) ∧
      L.length = 2 * (c.d + g.ap + g.an + g.bn) + 8 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := ERASE_Cd_spec (Terminal := Terminal) hmark he
  obtain ⟨L2, hx2, h2, hl2⟩ := ERASE_Ca_spec (Terminal := Terminal) hmark h1
  obtain ⟨L3, hx3, h3, hl3⟩ := ERASE_Cb_spec (Terminal := Terminal) hmark h2
  obtain ⟨L4, hx4, h4, hl4⟩ := ERASE_Cc_spec (Terminal := Terminal) hmark h3
  refine ⟨_, execA_seq hx1 (execA_seq hx2 (execA_seq hx3 hx4)), ?_, ?_⟩
  · simpa only [applyActs_append] using h4
  · simp only [List.length_append, hl1, hl2, hl3, hl4]
    omega

theorem CLEAR_SIGNED_bound (blank : Fin sc) {k r p q : ℕ} {c : Ctr} {g : Ctr3}
    (hk : 1 ≤ k) (hok : SignedOK k r p q c g) :
    2 * (c.d + g.ap + g.an + g.bn) + 8 ≤ 2 * (r + k * p + 2 * q + 1) + 8 := by
  have h := clearSigned_length_bound blank hk hok
  rw [clearSigned_length] at h
  omega

/-- info: 'PalPeg.GSPreProg.CLEAR_SIGNED_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CLEAR_SIGNED_spec
end PalPeg.GSPreProg
