import PalPeg.GSPreprocessProg50

/-! # Copying reach into the positive scratch counter -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def raRest : Prog A9 Cond9 :=
  .seq (.act (tCa, .blk, .right)) (.act (tCe, .blk, .right))

def raRestL (blank : Fin sc) : List (Act sc) :=
  [Act.Ca blank .right, Act.Ce blank .right]

def RA : Prog A9 Cond9 := DLOOP tCr raRest

theorem RA_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hr : Tape.CounterView' blank mark ts.Cr n) :
    ExecA Terminal blank endSym mark RA ts
      (dPow ctCr blank (raRestL blank) n ++ dTest ctCr blank mark) := by
  exact dLoop_exec ctCr raRest (raRestL blank) hmark
    (fun _ => execA_seq (execA_ct_put ctCa .right _) (execA_ct_put ctCe .right _))
    (fun _ => rfl) n ts hr

theorem raPow_enc (n : ℕ) {a b D Q E P F S R A B C : ℕ} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩
      ⟨A, B, C⟩ ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
      ⟨A + n, B, C⟩ (applyActs blank (dPow ctCr blank (raRestL blank) n) ts) := by
  induction n generalizing E A ts with
  | zero => simpa [dPow, applyActs] using he
  | succ n ih =>
      have hr : Tape.CounterView' blank mark ts.Cr ((R + n) + 1) := by
        simpa only [Nat.add_assoc] using he.base.cr
      have hs : EncS blank startSym endSym mark x a b
          ⟨D, Q, E + 1, P, F, S, R + n⟩ ⟨A + 1, B, C⟩
          (applyActs blank (dUnit ctCr blank (raRestL blank)) ts) :=
        ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq,
          Tape.counter'_inc he.base.ce, he.base.cp, he.base.cf, he.base.cs,
          by
            change Tape.CounterView' blank mark
              (Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay) (R + n)
            simpa using Tape.counter'_dec hr⟩,
          Tape.counter'_inc he.ca, he.cb, he.cc⟩
      simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n]
        using ih hs

def COPY_RA : Prog A9 Cond9 := .seq RA crProg

theorem COPY_RA_spec (hmark : mark ≠ blank) {a b D Q P F S R : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark COPY_RA ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩
        ⟨g.ap + R, g.an, g.bn⟩ (applyActs blank L ts) ∧ L.length = 7 * R + 4 := by
  have h1 := raPow_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) R (R := 0) (by simpa using he)
  simp only [Nat.zero_add] at h1
  have h2 := h1.frame (acts := dTest ctCr blank mark)
    (by simp [dTest, Act.noSigned, ctCr]) (dTest_enc_Cr h1.base)
  rw [← applyActs_append] at h2
  have hx1 := RA_exec (Terminal := Terminal) (endSym := endSym) hmark R ts he.base.cr
  have hx2 := crProg_exec (Terminal := Terminal) (endSym := endSym) hmark R _ h2.base.ce
  have h3 := crLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) R a b D Q 0 P F S 0 _ (by simpa using h2.base)
  simp only [Nat.zero_add] at h3
  have h4 := dTest_enc_Ce h3
  rw [← applyActs_append] at h4
  have h5 := h2.frame (acts := crLoop blank R ++ dTest ctCe blank mark)
    (by simp [dTest, Act.noSigned, ctCe]) h4
  refine ⟨_, execA_seq hx1 hx2, ?_, ?_⟩
  · simpa only [applyActs_append] using h5
  · simp [dPow_length, raRestL, crLoop_length]; omega

def SEED_SIGNED (k : ℕ) : Prog A9 Cond9 :=
  .seq COPY_RA (.seq (SAT_DEC tCa) (CD_UP (k - 2)))

theorem SEED_SIGNED_spec (hmark : mark ≠ blank) (k : ℕ) (hk : 3 ≤ k)
    {s F S R : ℕ} {ts : Tapes sc} (hr : 1 ≤ R)
    (he : EncS blank startSym endSym mark x s (s + 1)
      ⟨0, 0, 0, 1, F, S, R⟩ ⟨0, 0, 0⟩ ts) :
    ∃ L, ExecA Terminal blank endSym mark (SEED_SIGNED k) ts L ∧
      EncR blank startSym endSym mark x s (s + 1)
        ⟨k - 2, 0, 0, 1, F, S, R⟩ ⟨R - 1, 0, 0⟩ (applyActs blank L ts) ∧
      SignedOK k R 1 0 ⟨k - 2, 0, 0, 1, F, S, R⟩ ⟨R - 1, 0, 0⟩ ∧
      L.length = 7 * R + 6 + (k - 2) := by
  obtain ⟨L1, hx1, h1, hl1⟩ := COPY_RA_spec (Terminal := Terminal) hmark he
  have hx2 := satDecRaw_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) ctCa (applyActs blank L1 ts)
  have h2 := satDecCa_enc hmark h1
  have hx3 := CD_UP_exec (Terminal := Terminal) (blank := blank) (endSym := endSym) (mark := mark)
    (k - 2) (applyActs blank (satDecRawL ctCa blank mark (applyActs blank L1 ts))
      (applyActs blank L1 ts))
  have h3 := cdIncs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k - 2) s (s + 1) 0 0 0 1 F S R _ h2.base
  have h4 := h2.frame (acts := cdIncs blank (k - 2))
    (by simp [cdIncs, NoSigned, Act.noSigned]) h3
  refine ⟨_, execA_seq hx1 (execA_seq hx2 hx3), ?_, ?_, ?_⟩
  · simpa only [applyActs_append, Nat.zero_add] using EncR_of_EncS h4 rfl
  · simp [SignedOK]; omega
  · simp only [List.length_append, hl1, satDecRaw_length, cdIncs_length]
    omega

/-- info: 'PalPeg.GSPreProg.SEED_SIGNED_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SEED_SIGNED_spec

/-- info: 'PalPeg.GSPreProg.COPY_RA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COPY_RA_spec
end PalPeg.GSPreProg
