import PalPeg.GSPreprocessProg34

/-! # Complete finite second search, with ordinary output tapes -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def SECOND_SEARCH (k : ℕ) : Prog A9 Cond9 := .seq (SECOND_OUTER_R k) (NORMALIZE_R k)

theorem SECOND_SEARCH_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s first S fuel p q D : ℕ) (hk : 0 < k) (hf : 0 < first) (hs : s ≤ x.length)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g)
    (hfit : s + p + q ≤ x.length) (hbound : (x.drop s).length ≤ p + fuel) :
    ∃ L D' E' P' g', ExecA Terminal blank endSym mark (SECOND_SEARCH k) ts L ∧
      EncS blank startSym endSym mark x s (s + P')
        ⟨D', 0, E', P', first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r P' 0 ⟨D', 0, E', P', first, S, r⟩ g' ∧
      s + P' ≤ x.length ∧
      P' ≤ p + q + secondOuterWork (x.drop s) k first r fuel p q ∧
      (∀ p2, secondOuter (x.drop s) k first r fuel p q = some p2 → P' = p2) ∧
      E' = (if (secondOuter (x.drop s) k first r fuel p q).isSome then 1 else 0) ∧
      L.length ≤ soRRate k * secondOuterWork (x.drop s) k first r fuel p q +
        soRPotential k * q + 13 := by
  obtain ⟨L1, u, D1, q1, E1, P1, g1, hx1, hu, he1, hok1, hfit1, hstop,
    hsize, hanswer, hflag, hc1⟩ := SO_RUN_R_spec (Terminal := Terminal)
    hend hmark k r s first S hk hf hs fuel p q D g ts he hok hfit hbound
  obtain ⟨L2, hx2, hu2, hc2⟩ := SECOND_OUTER_R_finish k ts u he1.enc.base.cq he1.enc.base.ce
    L1 hx1 hu
  have hE1 : E1 ≤ 1 := by rw [hflag]; split <;> omega
  obtain ⟨L3, D3, g3, hx3, he3, hok3, hc3⟩ := NORMALIZE_R_spec (Terminal := Terminal)
    hmark k r s P1 q1 D1 E1 first S hk g1 u he1 hok1 hfit1 hE1 hstop
  refine ⟨L2 ++ L3, D3, E1, P1, g3,
    execA_seq hx2 (by rw [hu2]; exact hx3), ?_, hok3, by omega,
    by omega, hanswer, hflag, ?_⟩
  · rw [applyActs_append, hu2]; exact he3
  · have hpot : 21 * q1 ≤ soRPotential k * q1 :=
      Nat.mul_le_mul_right q1 (by unfold soRPotential; omega)
    rw [List.length_append, hc2]
    omega

/-- The abstract work bound pays for the complete concrete search, including
    restoration of all probed counters and normalization of the output heads. -/
theorem SECOND_SEARCH_linear (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s first S fuel p q D : ℕ) (hk : 3 ≤ k) (hf : 0 < first) (hs : s ≤ x.length)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g)
    (hp : 0 < p) (hfit : s + p + q ≤ x.length)
    (hbound : (x.drop s).length ≤ p + fuel) :
    ∃ L D' E' P' g', ExecA Terminal blank endSym mark (SECOND_SEARCH k) ts L ∧
      EncS blank startSym endSym mark x s (s + P')
        ⟨D', 0, E', P', first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r P' 0 ⟨D', 0, E', P', first, S, r⟩ g' ∧
      s + P' ≤ x.length ∧
      (∀ p2, secondOuter (x.drop s) k first r fuel p q = some p2 → P' = p2) ∧
      E' = (if (secondOuter (x.drop s) k first r fuel p q).isSome then 1 else 0) ∧
      L.length ≤ (soRRate k * (2 * k + 5) + soRPotential k) *
        (x.drop s).length + soRRate k * (k + 2) + 13 := by
  obtain ⟨L, D', E', P', g', hx, he', hok', hfit', _, ha, hf', hc⟩ :=
    SECOND_SEARCH_spec (Terminal := Terminal) hend hmark k r s first S fuel p q D
      (by omega) hf hs g ts he hok hfit hbound
  have hpq : p + q ≤ (x.drop s).length := by rw [List.length_drop]; omega
  have hw := secondOuterWork_le (x.drop s) k first r hk hf fuel p q hp
    (by omega) (by omega) (by intro _; exact hpq)
  have hw' : secondOuterWork (x.drop s) k first r fuel p q ≤
      (2 * k + 5) * (x.drop s).length + (k + 2) := by nlinarith
  have hwc := Nat.mul_le_mul_left (soRRate k) hw'
  have hqc := Nat.mul_le_mul_left (soRPotential k) (show q ≤ (x.drop s).length by omega)
  refine ⟨L, D', E', P', g', hx, he', hok', hfit', ha, hf', ?_⟩
  nlinarith

/-- info: 'PalPeg.GSPreProg.SECOND_SEARCH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECOND_SEARCH_spec

end PalPeg.GSPreProg
