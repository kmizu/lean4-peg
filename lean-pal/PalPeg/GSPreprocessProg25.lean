import PalPeg.GSPreprocessProg24

/-! # Add the saved period to the physical reach counter, preserving it -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def DRAIN_F_E : Prog A9 Cond9 := DLOOP tCf (.act (tCe, .blk, .right))

def drainFEL (blank mark : Fin sc) (n : ℕ) : List (Act sc) :=
  dPow ctCf blank [Act.Ce blank .right] n ++ dTest ctCf blank mark

theorem DRAIN_F_E_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hf : Tape.CounterView' blank mark ts.Cf n) :
    ExecA Terminal blank endSym mark DRAIN_F_E ts (drainFEL blank mark n) := by
  apply dLoop_exec ctCf _ _ hmark
  · intro u; exact execA_ct_put ctCe .right u
  · intro u; rfl
  · exact hf

theorem drainFEPow_enc (n : ℕ) :
    ∀ (a b D Q E P S R : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x a b ⟨D, Q, E, P, n, S, R⟩ g ts →
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, 0, S, R⟩ g
      (applyActs blank (dPow ctCf blank [Act.Ce blank .right] n) ts) := by
  induction n with
  | zero => intro a b D Q E P S R g ts he; simpa only [Nat.add_zero, dPow, applyActs_nil] using he
  | succ n ih =>
    intro a b D Q E P S R g ts he
    have he1 : EncS blank startSym endSym mark x a b ⟨D, Q, E + 1, P, n, S, R⟩ g
        (applyActs blank (dUnit ctCf blank [Act.Ce blank .right]) ts) :=
      ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, Tape.counter'_inc he.base.ce,
        he.base.cp, Tape.counter'_dec he.base.cf, he.base.cs, he.base.cr⟩,
        he.ca, he.cb, he.cc⟩
    have hh := ih a b D Q (E + 1) P S R g _ he1
    simpa only [dPow, applyActs_append, Nat.add_assoc, Nat.add_comm 1 n] using hh

theorem drainFE_enc (hmark : mark ≠ blank) (n a b D Q E P S R : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, n, S, R⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, 0, S, R⟩ g
      (applyActs blank (drainFEL blank mark n) ts) := by
  have hh := drainFEPow_enc n a b D Q E P S R g ts he
  rw [drainFEL, applyActs_append, ct_dTest_restore ctCf hmark _ hh.base.cf]
  exact hh

def ADD_F_R : Prog A9 Cond9 := .seq DRAIN_F_E (CMUL_RESTORE tCf tCr 1)

theorem ADD_F_R_spec (hmark : mark ≠ blank) (n a b D Q P S R : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, n, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark ADD_F_R ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, n, S, R + n⟩ g
        (applyActs blank L ts) ∧ L.length = 7 * n + 4 := by
  let L1 := drainFEL blank mark n
  let t1 := applyActs blank L1 ts
  let L2 := cmulRestoreL ctCf ctCr blank mark 1 n
  have he1 : EncS blank startSym endSym mark x a b ⟨D, Q, n, P, 0, S, R⟩ g t1 := by
    simpa only [Nat.zero_add] using drainFE_enc hmark n a b D Q 0 P S R g ts he
  have hfe : tCe ≠ (ctCf : CT sc).idx := by change (4 : Fin 12) ≠ 6; decide
  have hre : tCe ≠ (ctCr : CT sc).idx := by change (4 : Fin 12) ≠ 8; decide
  have hfr : (ctCf : CT sc).idx ≠ (ctCr : CT sc).idx := by change (6 : Fin 12) ≠ 8; decide
  have hc := CMUL_RESTORE_counter ctCf ctCr hfr hfe hre hmark 1 n 0 R t1
    he1.base.cf he1.base.cr he1.base.ce
  have ho (j : Fin 12) (hjf : j ≠ tCf) (hjr : j ≠ tCr) (hje : j ≠ tCe) :
      getT (applyActs blank L2 t1) j = getT t1 j :=
    cmulRestore_other ctCf ctCr j hjf hjr hje 1 n t1
  have hs : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, n, S, R + n⟩ g
      (applyActs blank L2 t1) := by
    refine ⟨⟨?_, ?_, ?_, ?_, hc.2.2, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · change Tape.SeqView _ (getT (applyActs blank L2 t1) tV1) _ _
      rw [ho tV1 (by decide) (by decide) (by decide)]; exact he1.base.v1
    · change Tape.SeqView _ (getT (applyActs blank L2 t1) tV2) _ _
      rw [ho tV2 (by decide) (by decide) (by decide)]; exact he1.base.v2
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCd) _
      rw [ho tCd (by decide) (by decide) (by decide)]; exact he1.base.cd
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCq) _
      rw [ho tCq (by decide) (by decide) (by decide)]; exact he1.base.cq
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCp) _
      rw [ho tCp (by decide) (by decide) (by decide)]; exact he1.base.cp
    · simpa only [Nat.zero_add, ctCf, L2] using hc.1
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCs) _
      rw [ho tCs (by decide) (by decide) (by decide)]; exact he1.base.cs
    · simpa only [Nat.one_mul, ctCr, L2] using hc.2.1
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCa) _
      rw [ho tCa (by decide) (by decide) (by decide)]; exact he1.ca
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCb) _
      rw [ho tCb (by decide) (by decide) (by decide)]; exact he1.cb
    · change Tape.CounterView' _ _ (getT (applyActs blank L2 t1) tCc) _
      rw [ho tCc (by decide) (by decide) (by decide)]; exact he1.cc
  refine ⟨L1 ++ L2, execA_seq (DRAIN_F_E_exec hmark n ts he.base.cf)
    (CMUL_RESTORE_exec ctCf ctCr hfe hre hmark 1 n t1 he1.base.ce), ?_, ?_⟩
  · rw [applyActs_append]; exact hs
  · simp [L1, L2, drainFEL, cmulRestoreL_length, dTest]; ring

/-- info: 'PalPeg.GSPreProg.ADD_F_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADD_F_R_spec

end PalPeg.GSPreProg
