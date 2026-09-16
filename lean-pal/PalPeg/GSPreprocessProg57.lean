import PalPeg.GSPreprocessProg56

/-! # Establishing and recycling the saturated bound of a stripping search -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def FA : Prog A9 Cond9 := DLOOP tCf raRest

theorem FA_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hf : Tape.CounterView' blank mark ts.Cf n) :
    ExecA Terminal blank endSym mark FA ts
      (dPow ctCf blank (raRestL blank) n ++ dTest ctCf blank mark) := by
  exact dLoop_exec ctCf raRest (raRestL blank) hmark
    (fun _ => execA_seq (execA_ct_put ctCa .right _) (execA_ct_put ctCe .right _))
    (fun _ => rfl) n ts hf

theorem faPow_enc (n : ℕ) {a b D Q E P F S R A B C : ℕ} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩
      ⟨A, B, C⟩ ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
      ⟨A + n, B, C⟩ (applyActs blank (dPow ctCf blank (raRestL blank) n) ts) := by
  induction n generalizing E A ts with
  | zero => simpa [dPow, applyActs] using he
  | succ n ih =>
      have hf : Tape.CounterView' blank mark ts.Cf ((F + n) + 1) := by
        simpa only [Nat.add_assoc] using he.base.cf
      have hs : EncS blank startSym endSym mark x a b
          ⟨D, Q, E + 1, P, F + n, S, R⟩ ⟨A + 1, B, C⟩
          (applyActs blank (dUnit ctCf blank (raRestL blank)) ts) :=
        ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq,
          Tape.counter'_inc he.base.ce, he.base.cp,
          by
            change Tape.CounterView' blank mark
              (Tape.step blank (Tape.step blank ts.Cf blank .left) blank .stay) (F + n)
            simpa using Tape.counter'_dec hf,
          he.base.cs, he.base.cr⟩, Tape.counter'_inc he.ca, he.cb, he.cc⟩
      simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n] using ih hs

def COPY_FA : Prog A9 Cond9 := .seq FA cfProg

@[simp] theorem cfLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (cfLoop blank n) := by
  induction n with
  | zero => simp [cfLoop]
  | succ n ih => simp [cfLoop, Act.noSigned, ih]

theorem COPY_FA_spec (hmark : mark ≠ blank) {a b D Q P F S R : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark COPY_FA ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩
        ⟨g.ap + F, g.an, g.bn⟩ (applyActs blank L ts) ∧ L.length = 7 * F + 4 := by
  have h1 := faPow_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) F (F := 0) (by simpa using he)
  simp only [Nat.zero_add] at h1
  have h2 := h1.frame (acts := dTest ctCf blank mark)
    (by simp [dTest, Act.noSigned, ctCf]) (dTest_enc_Cf h1.base)
  rw [← applyActs_append] at h2
  have hx1 := FA_exec (Terminal := Terminal) (endSym := endSym) hmark F ts he.base.cf
  have hx2 := cfProg_exec (Terminal := Terminal) (endSym := endSym) hmark F _ h2.base.ce
  have h3 := cfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) F a b D Q 0 P 0 S R _ (by simpa using h2.base)
  simp only [Nat.zero_add] at h3
  have h4 := dTest_enc_Ce h3
  rw [← applyActs_append] at h4
  have h5 := h2.frame (acts := cfLoop blank F ++ dTest ctCe blank mark)
    (by simp [dTest, Act.noSigned, ctCe]) h4
  refine ⟨_, execA_seq hx1 hx2, ?_, ?_⟩
  · simpa only [applyActs_append] using h5
  · simp [dPow_length, raRestL, cfLoop_length]; omega

def PA : Prog A9 Cond9 := DLOOP tCp (.act (tCa, .blk, .right))

theorem paPow_enc (n : ℕ) {a b D Q E P F S R A B C : ℕ} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩
      ⟨A, B, C⟩ ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
      ⟨A + n, B, C⟩ (applyActs blank (dPow ctCp blank [Act.Ca blank .right] n) ts) := by
  induction n generalizing A ts with
  | zero => simpa [dPow, applyActs] using he
  | succ n ih =>
      have hp : Tape.CounterView' blank mark ts.Cp ((P + n) + 1) := by
        simpa only [Nat.add_assoc] using he.base.cp
      have hs : EncS blank startSym endSym mark x a b
          ⟨D, Q, E, P + n, F, S, R⟩ ⟨A + 1, B, C⟩
          (applyActs blank (dUnit ctCp blank [Act.Ca blank .right]) ts) :=
        ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, he.base.ce,
          by
            change Tape.CounterView' blank mark
              (Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay) (P + n)
            simpa using Tape.counter'_dec hp,
          he.base.cf, he.base.cs, he.base.cr⟩, Tape.counter'_inc he.ca, he.cb, he.cc⟩
      simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n] using ih hs

theorem PA_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark PA ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, E, 0, F, S, R⟩
        ⟨g.ap + P, g.an, g.bn⟩ (applyActs blank L ts) ∧ L.length = 3 * P + 2 := by
  have h1 := paPow_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (P := 0) (by simpa using he)
  have h2 := h1.frame (acts := dTest ctCp blank mark)
    (by simp [dTest, Act.noSigned, ctCp]) (dTest_enc_Cp h1.base)
  have hx := dLoop_exec (Terminal := Terminal) (endSym := endSym) ctCp
    (.act (tCa, .blk, .right)) [Act.Ca blank .right] hmark
    (fun _ => execA_ct_put ctCa .right _) (fun _ => rfl) P ts he.base.cp
  refine ⟨_, hx, ?_, ?_⟩
  · simpa only [applyActs_append] using h2
  · simp; omega

/-- info: 'PalPeg.GSPreProg.COPY_FA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COPY_FA_spec
/-- info: 'PalPeg.GSPreProg.PA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA_spec
end PalPeg.GSPreProg
