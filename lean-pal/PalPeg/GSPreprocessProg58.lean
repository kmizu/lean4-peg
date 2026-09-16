import PalPeg.GSPreprocessProg57

/-! # Counter-driven rewind without a data-dependent stopping threshold -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def pvrRest : Prog A9 Cond9 :=
  .seq (.act (tV2, .keep, .left))
    (.seq (.act (tCr, .blk, .right)) (.act (tCe, .blk, .right)))
def pvrRestL (blank : Fin sc) : List (Act sc) :=
  [Act.V2 .left, Act.Cr blank .right, Act.Ce blank .right]
def PVR : Prog A9 Cond9 := DLOOP tCp pvrRest

theorem pvrPow_enc (n : ℕ) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a (b + n) ⟨D, Q, E, P + n, F, S, R⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R + n⟩ g
      (applyActs blank (dPow ctCp blank (pvrRestL blank) n) ts) := by
  induction n generalizing E R ts with
  | zero => simpa [dPow, applyActs] using he
  | succ n ih =>
      have hp : Tape.CounterView' blank mark ts.Cp ((P + n) + 1) := by
        simpa only [Nat.add_assoc] using he.base.cp
      have hv : Tape.SeqView blank ts.V2 (pword startSym endSym x) ((b + n) + 1 + 1) := by
        simpa only [Nat.add_assoc] using he.base.v2
      have hs : EncS blank startSym endSym mark x a (b + n)
          ⟨D, Q, E + 1, P + n, F, S, R + 1⟩ g
          (applyActs blank (dUnit ctCp blank (pvrRestL blank)) ts) :=
        ⟨⟨he.base.v1, pat_left hv, he.base.cd, he.base.cq, Tape.counter'_inc he.base.ce,
          by
            change Tape.CounterView' blank mark
              (Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay) (P + n)
            simpa using Tape.counter'_dec hp,
          he.base.cf, he.base.cs, Tape.counter'_inc he.base.cr⟩, he.ca, he.cb, he.cc⟩
      simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n] using ih hs

theorem PVR_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a (b + P) ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark PVR ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, E + P, 0, F, S, R + P⟩ g
        (applyActs blank L ts) ∧ L.length = 5 * P + 2 := by
  have h1 := pvrPow_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (P := 0) (by simpa using he)
  have h2 := h1.frame (acts := dTest ctCp blank mark)
    (by simp [dTest, Act.noSigned, ctCp]) (dTest_enc_Cp h1.base)
  have hx := dLoop_exec (Terminal := Terminal) (endSym := endSym) ctCp pvrRest (pvrRestL blank)
    hmark (fun _ => execA_seq (execA_v2 .left _)
      (execA_seq (execA_ct_put ctCr .right _) (execA_ct_put ctCe .right _)))
      (fun _ => rfl) P ts he.base.cp
  refine ⟨_, hx, ?_, ?_⟩
  · simpa only [applyActs_append] using h2
  · simp [pvrRestL]; omega

def RP : Prog A9 Cond9 := DLOOP tCr (.act (tCp, .blk, .right))

theorem rpPow_enc (n : ℕ) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩ g
      (applyActs blank (dPow ctCr blank [Act.Cp blank .right] n) ts) := by
  induction n generalizing P ts with
  | zero => simpa [dPow, applyActs] using he
  | succ n ih =>
      have hr : Tape.CounterView' blank mark ts.Cr ((R + n) + 1) := by
        simpa only [Nat.add_assoc] using he.base.cr
      have hs : EncS blank startSym endSym mark x a b
          ⟨D, Q, E, P + 1, F, S, R + n⟩ g
          (applyActs blank (dUnit ctCr blank [Act.Cp blank .right]) ts) :=
        ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, he.base.ce,
          Tape.counter'_inc he.base.cp, he.base.cf, he.base.cs,
          by
            change Tape.CounterView' blank mark
              (Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay) (R + n)
            simpa using Tape.counter'_dec hr⟩, he.ca, he.cb, he.cc⟩
      simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n] using ih hs

theorem RP_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark RP ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, E, P + R, F, S, 0⟩ g
        (applyActs blank L ts) ∧ L.length = 3 * R + 2 := by
  have h1 := rpPow_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) R (R := 0) (by simpa using he)
  have h2 := h1.frame (acts := dTest ctCr blank mark)
    (by simp [dTest, Act.noSigned, ctCr]) (dTest_enc_Cr h1.base)
  have hx := dLoop_exec (Terminal := Terminal) (endSym := endSym) ctCr
    (.act (tCp, .blk, .right)) [Act.Cp blank .right] hmark
    (fun _ => execA_ct_put ctCp .right _) (fun _ => rfl) R ts he.base.cr
  refine ⟨_, hx, ?_, ?_⟩
  · simpa only [applyActs_append] using h2
  · simp; omega

def REWIND_TO_CUT : Prog A9 Cond9 :=
  .seq (.seq prProg (.seq cpProg rvProg)) (.seq PVR RP)

theorem REWIND_TO_CUT_spec (hmark : mark ≠ blank) {s P R D F S : ℕ} {g : Ctr3}
    {ts : Tapes sc} (hpr : P ≤ R)
    (he : EncS blank startSym endSym mark x (s + (R - P)) (s + R)
      ⟨D, 0, 0, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark REWIND_TO_CUT ts L ∧
      EncS blank startSym endSym mark x s s ⟨D, 0, R, P, F, S, 0⟩ g
        (applyActs blank L ts) ∧ L.length = 5 * R + 11 * P + 10 := by
  have hx1 := prProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts he.base.cp
  have h1 := prLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 F S (R - P) ts
      (by simpa only [Nat.zero_add, Nat.sub_add_cancel hpr] using he.base)
  have h1 := dTest_enc_Cp h1
  rw [← applyActs_append] at h1
  simp only [Nat.zero_add] at h1
  have hx2 := cpProg_exec (Terminal := Terminal) (endSym := endSym) hmark P _ h1.ce
  have h2 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 F S (R - P) _
      (by simpa using h1)
  have h2 := dTest_enc_Ce h2
  rw [← applyActs_append] at h2
  have hx3 := rvProg_exec (Terminal := Terminal) (endSym := endSym) hmark (R - P) _ h2.cr
  have h3 := rvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P F S 0 _
      (by simpa only [Nat.zero_add, show s + P + (R - P) = s + R from by omega] using h2)
  have h3 := dTest_enc_Cr h3
  rw [← applyActs_append] at h3
  let L0 := (prLoop blank P ++ dTest ctCp blank mark) ++
    ((cpLoop blank P ++ dTest ctCe blank mark) ++ (rvLoop blank (R - P) ++ dTest ctCr blank mark))
  have h3s := he.frame (acts := L0)
    (by simp [L0, dTest, Act.noSigned, ctCp, ctCe, ctCr])
    (by simpa only [L0, applyActs_append] using h3)
  obtain ⟨L4, hx4, h4, hl4⟩ := PVR_spec (Terminal := Terminal) hmark h3s
  obtain ⟨L5, hx5, h5, hl5⟩ := RP_spec (Terminal := Terminal) hmark h4
  have hx0 : ExecA Terminal blank endSym mark (.seq prProg (.seq cpProg rvProg)) ts L0 :=
    execA_seq hx1 (execA_seq hx2 hx3)
  have hx := execA_seq hx0 (execA_seq hx4 hx5)
  refine ⟨_, hx, ?_, ?_⟩
  · simpa only [applyActs_append, L0, Nat.zero_add, Nat.sub_add_cancel hpr] using h5
  · simp only [L0, List.length_append, prLoop_length, cpLoop_length, rvLoop_length,
      dTest_length, hl4, hl5, Nat.zero_add]
    omega

/-- info: 'PalPeg.GSPreProg.REWIND_TO_CUT_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms REWIND_TO_CUT_spec
end PalPeg.GSPreProg
