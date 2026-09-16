import PalPeg.GSPreprocessProg30

/-! # Correctness and amortized cost of one finite outer iteration -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem SO_BODY_R_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s p q D first S : ℕ) (hk : 0 < k) (hf : 0 < first)
    (g : Ctr3) (ts : Tapes sc) (hs : s ≤ x.length)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g)
    (hfit : s + p + q ≤ x.length) (hp : p < (x.drop s).length) :
    ∃ L D' q' E' P' g', ExecA Terminal blank endSym mark (SO_BODY_R k) ts L ∧
      EncR blank startSym endSym mark x (s + q') (s + P' + q')
        ⟨D', q', E', P', first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r P' q' ⟨D', q', E', P', first, S, r⟩ g' ∧
      s + P' + q' ≤ x.length ∧ E' ≤ 1 ∧ (E' = 0 → p < P') ∧
      P' + q' ≤ p + q + 1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q ∧
      (∀ fuel, secondOuter (x.drop s) k first r (fuel + 1) p q =
        if E' = 1 then some P' else secondOuter (x.drop s) k first r fuel P' q') ∧
      (∀ fuel, secondOuterWork (x.drop s) k first r (fuel + 1) p q =
        1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q +
        (if E' = 1 then 0 else secondOuterWork (x.drop s) k first r fuel P' q')) ∧
      L.length + 4 + soRPotential k * q' ≤
        soRRate k * (1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q) +
          soRPotential k * q := by
  obtain ⟨L1, D1, g1, j, hx1, he1, hok1, hfit1, hj, hsi, hc1⟩ :=
    SCAN_R_second_spec (Terminal := Terminal) hend hmark k r s p q D 0 first S g ts hs he hok hfit
  let t1 := applyActs blank L1 ts
  change secondInner (x.drop s) k p r ((x.drop s).length + 1) q =
    (if sAbort endSym (orcAB blank mark) t1 then none else some (q + j)) at hsi
  have ht : applyActs blank (sAbortTest blank t1) t1 = t1 :=
    sAbortTest_restore t1 he1.enc.ca he1.enc.base.cd
  by_cases hab : sAbort endSym (orcAB blank mark) t1
  · have hsi0 : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = none := by
      simpa only [if_pos hab] using hsi
    let L2 : List (Act sc) := [Act.Ce blank .right]
    have hx2 : ExecA Terminal blank endSym mark
        (SABORT (.act (tCe, .blk, .right)) (ORC2_FAST k (PERIOD_R k) (RESET_R k))) t1
        (sAbortTest blank t1 ++ L2) := by
      apply SABORT_exec t1 he1.enc.ca he1.enc.base.cd
      rw [if_pos hab]
      exact execA_ct_put ctCe .right t1
    have he2 : EncR blank startSym endSym mark x (s + (q + j)) (s + p + (q + j))
        ⟨D1, q + j, 1, p, first, S, r⟩ g1 (applyActs blank L2 t1) :=
      ⟨ceFlagS_enc he1.enc, he1.diff⟩
    refine ⟨L1 ++ (sAbortTest blank t1 ++ L2), D1, q + j, 1, p, g1,
      execA_seq hx1 hx2, ?_, hok1, hfit1, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [applyActs_append, applyActs_append, ht]; exact he2
    · intro fuel; simp only [secondOuter, if_pos hp, hsi0, ite_true]
    · intro fuel; simp only [secondOuterWork, if_pos hp, hsi0, ite_true]
    · have hc := soR_abort_cost k q j _ hj
      simp only [List.length_append, sAbortTest_length]
      have hl2 : L2.length = 1 := rfl
      rw [hl2]
      omega
  · have hsi1 : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = some (q + j) := by
      simpa only [if_neg hab] using hsi
    obtain ⟨LO, u, hu, heu, hco, hxo⟩ := ORC2_FAST_spec (Terminal := Terminal) hmark k hk he1
    have hprefix (L2 : List (Act sc)) :
        applyActs blank (L1 ++ (sAbortTest blank t1 ++ (LO ++ L2))) ts = applyActs blank L2 u := by
      rw [applyActs_append, applyActs_append, ht, applyActs_append, hu]
    have hex (L2 : List (Act sc))
        (hx2 : ExecA Terminal blank endSym mark
          (if k * first ≤ q + j ∧ q + j ≤ r then PERIOD_R k else RESET_R k) u L2) :
        ExecA Terminal blank endSym mark (SO_BODY_R k) ts
          (L1 ++ (sAbortTest blank t1 ++ (LO ++ L2))) := by
      apply execA_seq hx1
      apply SABORT_exec t1 he1.enc.ca he1.enc.base.cd
      rw [if_neg hab]
      exact hxo _ _ _ hx2
    by_cases hcmp : k * first ≤ q + j ∧ q + j ≤ r
    · obtain ⟨L2, D2, g2, hx2, he2, hok2, hc2⟩ := PERIOD_R_signed_spec
        (Terminal := Terminal) hmark k r s p (q + j) D1 first S hk g1 u heu hok1 hcmp
      have hfq : first ≤ q + j := (Nat.le_mul_of_pos_left first hk).trans hcmp.1
      rw [if_pos hcmp] at hco
      refine ⟨L1 ++ (sAbortTest blank t1 ++ (LO ++ L2)), D2, q + j - first, 0,
        p + first, g2, hex L2 (by rw [if_pos hcmp]; exact hx2), ?_, hok2,
        by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hprefix]; exact he2
      · intro fuel; simp only [secondOuter, if_pos hp, hsi1, if_pos hcmp, ite_false, Nat.zero_ne_one]
      · intro fuel; simp only [secondOuterWork, if_pos hp, hsi1, if_pos hcmp, ite_false, Nat.zero_ne_one]
      · have hc := soR_period_cost k q j _ first hj hfq
        simp only [List.length_append, sAbortTest_length]
        omega
    · have hdelta : shiftNoPeriod (q + j) k ≤ q + j + 1 := shiftNoPeriod_le_succ hk _
      have hfit2 : s + p + shiftNoPeriod (q + j) k ≤ x.length := by
        rcases Nat.eq_zero_or_pos (q + j) with h0 | h0
        · rw [h0, shiftNoPeriod_zero hk]
          rw [List.length_drop] at hp
          omega
        · have hh := shiftNoPeriod_le_of_pos hk h0
          omega
      obtain ⟨L2, D2, g2, hx2, he2, hok2, hc2⟩ := RESET_R_signed_spec
        (Terminal := Terminal) hmark k r s p (q + j) D1 first S hk g1 u heu hok1 hfit2
      rw [if_neg hcmp] at hco
      have hdpos : 0 < shiftNoPeriod (q + j) k := by
        unfold shiftNoPeriod; omega
      refine ⟨L1 ++ (sAbortTest blank t1 ++ (LO ++ L2)), D2, 0, 0,
        p + shiftNoPeriod (q + j) k, g2, hex L2 (by rw [if_neg hcmp]; exact hx2), ?_, hok2,
        by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hprefix]; exact he2
      · intro fuel; simp only [secondOuter, if_pos hp, hsi1, if_neg hcmp, ite_false, Nat.zero_ne_one]
      · intro fuel; simp only [secondOuterWork, if_pos hp, hsi1, if_neg hcmp, ite_false, Nat.zero_ne_one]
      · have hc := soR_reset_cost k q j _ _ hj hdelta
        simp only [List.length_append, sAbortTest_length, Nat.mul_zero, Nat.add_zero]
        omega

/-- info: 'PalPeg.GSPreProg.SO_BODY_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SO_BODY_R_spec

end PalPeg.GSPreProg
