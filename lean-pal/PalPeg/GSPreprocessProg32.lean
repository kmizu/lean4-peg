import PalPeg.GSPreprocessProg31

/-! # The finite outer loop: semantics, termination, and amortized cost -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem SO_RUN_R_stop_enc (hend : endSym ∉ x) (hmark : mark ≠ blank) (k : ℕ)
    {s p q D E first S r : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, first, S, r⟩ g ts) (hfit : s + p + q ≤ x.length)
    (hstop : ¬ (E = 0 ∧ p < (x.drop s).length)) :
    ExecA Terminal blank endSym mark (SO_RUN_R k) (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => hstop ((soReady_encR_iff hend hmark hfit he).mp hh))

theorem SO_RUN_R_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s first S : ℕ) (hk : 0 < k) (hf : 0 < first) (hs : s ≤ x.length) :
    ∀ (fuel p q D : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts →
    SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g →
    s + p + q ≤ x.length → (x.drop s).length ≤ p + fuel →
    ∃ L u D' q' E' P' g',
      ExecA Terminal blank endSym mark (SO_RUN_R k) (applyActs blank (soProbe blank) ts) L ∧
      applyActs blank L (applyActs blank (soProbe blank) ts) = applyActs blank (soProbe blank) u ∧
      EncR blank startSym endSym mark x (s + q') (s + P' + q')
        ⟨D', q', E', P', first, S, r⟩ g' u ∧
      SignedOK k r P' q' ⟨D', q', E', P', first, S, r⟩ g' ∧
      s + P' + q' ≤ x.length ∧ (E' = 0 → (x.drop s).length ≤ P') ∧
      P' + q' ≤ p + q + secondOuterWork (x.drop s) k first r fuel p q ∧
      (∀ p2, secondOuter (x.drop s) k first r fuel p q = some p2 → P' = p2) ∧
      E' = (if (secondOuter (x.drop s) k first r fuel p q).isSome then 1 else 0) ∧
      L.length + soRPotential k * q' ≤
        soRRate k * secondOuterWork (x.drop s) k first r fuel p q + soRPotential k * q := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q D g ts he hok hfit hbound
    have hp : ¬ p < (x.drop s).length := by omega
    refine ⟨[], ts, D, q, 0, p, g, SO_RUN_R_stop_enc hend hmark k he hfit (by tauto),
      rfl, he, hok, hfit, by omega, ?_, ?_, ?_, ?_⟩
    · simp only [secondOuterWork, Nat.add_zero, le_refl]
    · intro p2 hh; simp only [secondOuter] at hh; contradiction
    · rfl
    · simp only [List.length_nil, secondOuterWork, Nat.mul_zero, Nat.zero_add, le_refl]
  | succ fuel ih =>
    intro p q D g ts he hok hfit hbound
    by_cases hp : p < (x.drop s).length
    · obtain ⟨B, D1, q1, E1, P1, g1, hxB, he1, hok1, hfit1, hE1, hprogress,
        hsize, hanswer, hwork, hcost⟩ := SO_BODY_R_spec (Terminal := Terminal)
        hend hmark k r s p q D first S hk hf g ts hs he hok hfit hp
      have hready : probe blank ts.Ce = mark ∧ soCond blank endSym mark ts :=
        (soReady_iff ts).mp ((soReady_encR_iff hend hmark hfit he).mpr ⟨rfl, hp⟩)
      by_cases hflag : E1 = 1
      · have hstop := SO_RUN_R_stop_enc (Terminal := Terminal) hend hmark k he1 hfit1
          (by intro hh; omega)
        have hx := SO_RUN_R_cont k ts he.enc.base.cq he.enc.base.ce hready hxB hstop
        have hres := hanswer fuel
        have hW := hwork fuel
        rw [if_pos hflag] at hres hW
        refine ⟨soIter blank ts B ++ [], applyActs blank B ts, D1, q1, E1, P1, g1,
          hx, ?_, he1, hok1, hfit1, by omega, ?_, ?_, ?_, ?_⟩
        · simpa only [List.append_nil] using soIter_effect ts he.enc.base.cq he.enc.base.ce B
        · rw [hW]; omega
        · intro p2 hh; rw [hres] at hh; exact Option.some.inj hh
        · rw [hres]; exact hflag
        · rw [List.append_nil, soIter_length, hW]
          simpa only [Nat.add_zero] using hcost
      · have hE0 : E1 = 0 := by omega
        subst E1
        have hbound1 : (x.drop s).length ≤ P1 + fuel := by
          have hh := hprogress rfl
          omega
        obtain ⟨T, u, D2, q2, E2, P2, g2, hxT, hu, he2, hok2, hfit2, hstop2,
          hsize2, hanswer2, hflag2, hcost2⟩ := ih P1 q1 D1 g1 _ he1 hok1 hfit1 hbound1
        have hx := SO_RUN_R_cont k ts he.enc.base.cq he.enc.base.ce hready hxB hxT
        have hres := hanswer fuel
        have hW := hwork fuel
        simp only [Nat.zero_ne_one, ite_false] at hres hW
        refine ⟨soIter blank ts B ++ T, u, D2, q2, E2, P2, g2,
          hx, ?_, he2, hok2, hfit2, hstop2, ?_, ?_, ?_, ?_⟩
        · rw [applyActs_append, soIter_effect ts he.enc.base.cq he.enc.base.ce B]
          exact hu
        · rw [hW]; omega
        · intro p2 hh; exact hanswer2 p2 (by rw [← hres]; exact hh)
        · rw [hres]; exact hflag2
        · rw [List.length_append, soIter_length, hW, Nat.mul_add]
          omega
    · have hres : secondOuter (x.drop s) k first r (fuel + 1) p q = none := by
        rw [secondOuter, if_neg hp]
      have hW : secondOuterWork (x.drop s) k first r (fuel + 1) p q = 0 := by
        rw [secondOuterWork, if_neg hp]
      refine ⟨[], ts, D, q, 0, p, g, SO_RUN_R_stop_enc hend hmark k he hfit (by tauto),
        rfl, he, hok, hfit, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hW]; omega
      · intro p2 hh; rw [hres] at hh; contradiction
      · rw [hres]; rfl
      · simp only [List.length_nil, hW, Nat.mul_zero, Nat.zero_add, le_refl]

/-- info: 'PalPeg.GSPreProg.SO_RUN_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SO_RUN_R_spec

end PalPeg.GSPreProg
