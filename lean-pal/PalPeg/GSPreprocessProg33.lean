import PalPeg.GSPreprocessProg32

/-! # Normalize a successful second-phase result -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem ezLoop_other (n : ℕ) (j : Fin 12) (hj : j ≠ tCe) (ts : Tapes sc) :
    getT (applyActs blank (ezLoop blank n) ts) j = getT ts j := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [ezLoop, applyActs_append, ih]
    simp only [ezUnit, applyActs_cons, applyActs_nil, getT_applyAct, actTape, if_neg hj]

theorem EZ_SIGNED_spec (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark ezProg ts L ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g
        (applyActs blank L ts) ∧ L.length = 2 * E + 2 := by
  have hb := ezLoop_enc E a b D Q 0 P F S R ts (by simpa only [Nat.zero_add] using he.base)
  have hs : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g
      (applyActs blank (ezLoop blank E) ts) := by
    refine ⟨hb, ?_, ?_, ?_⟩
    · change Tape.CounterView' _ _ (getT (applyActs blank (ezLoop blank E) ts) tCa) _
      rw [ezLoop_other E tCa (by decide)]; exact he.ca
    · change Tape.CounterView' _ _ (getT (applyActs blank (ezLoop blank E) ts) tCb) _
      rw [ezLoop_other E tCb (by decide)]; exact he.cb
    · change Tape.CounterView' _ _ (getT (applyActs blank (ezLoop blank E) ts) tCc) _
      rw [ezLoop_other E tCc (by decide)]; exact he.cc
  refine ⟨ezLoop blank E ++ dTest ctCe blank mark, ezProg_exec hmark E ts he.base.ce, ?_, ?_⟩
  · rw [applyActs_append, ct_dTest_restore ctCe hmark _ hb.ce]; exact hs
  · simp [dTest]

def SUCCESS_NORMALIZE_R (k : ℕ) : Prog A9 Cond9 :=
  .seq (REWIND_R k) (.seq ezProg (.act (tCe, .blk, .right)))

theorem SUCCESS_NORMALIZE_R_spec (hmark : mark ≠ blank) (k r s p q D first S : ℕ)
    (hk : 0 < k) (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 1, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 1, p, first, S, r⟩ g) :
    ∃ L D' g', ExecA Terminal blank endSym mark (SUCCESS_NORMALIZE_R k) ts L ∧
      EncS blank startSym endSym mark x s (s + p)
        ⟨D', 0, 1, p, first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r p 0 ⟨D', 0, 1, p, first, S, r⟩ g' ∧ L.length ≤ 21 * q + 7 := by
  obtain ⟨ha, hb⟩ := (signedOK_iff k r p q _ _).mp hok
  obtain ⟨L1, D1, g1, hx1, he1, ha1, hb1, hc1⟩ := REWIND_R_spec (Terminal := Terminal)
    hmark k q s (s + p) D 1 p first S r r p ((k - 1) * p) 1 hk g ts he ha
      (by simpa only [Nat.add_comm 1 q] using hb)
  obtain ⟨L2, hx2, he2, hc2⟩ := EZ_SIGNED_spec (Terminal := Terminal) hmark he1
  let L3 : List (Act sc) := [Act.Ce blank .right]
  refine ⟨L1 ++ (L2 ++ L3), D1, g1,
    execA_seq hx1 (execA_seq hx2 (execA_ct_put ctCe .right _)), ?_, ?_, ?_⟩
  · rw [applyActs_append, applyActs_append]
    exact ceFlagS_enc he2
  · exact (signedOK_iff k r p 0 _ _).mpr ⟨ha1, hb1⟩
  · have hs := stays_le k q 0
    simp only [List.length_append]
    have hl3 : L3.length = 1 := rfl
    rw [hl3, hc2]
    omega

/-- info: 'PalPeg.GSPreProg.SUCCESS_NORMALIZE_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SUCCESS_NORMALIZE_R_spec

end PalPeg.GSPreProg
