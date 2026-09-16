import PalPeg.GSPreprocessProg26

/-! # Semantic invariants for both second-phase branches -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem sAbort_iffR (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {k r s p q D E F S : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g) :
    sAbort endSym (orcAB blank mark) ts ↔ AbortAt x k p r s q := by
  have hh := sAbort_iffS (orc := orcAB blank mark) hend
    (fun _ _ _ _ _ _ _ _ h ho => orcAB_spec hmark h ho) he.enc hok
  exact hh

theorem soReady_encR_iff (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s p q D E F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hfit : s + p + q ≤ x.length)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, R⟩ g ts) :
    condOf9 endSym mark .soReady
      (fun j => (getT (applyActs blank (soProbe blank) ts) j).focus) = true ↔
      E = 0 ∧ p < (x.drop s).length := by
  have hh := soReady_enc_iff hend hmark hfit he.enc
  exact hh

theorem PERIOD_R_signed_spec (hmark : mark ≠ blank) (k r s p q D first S : ℕ)
    (hk : 0 < k) (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g)
    (hcmp : k * first ≤ q ∧ q ≤ r) :
    ∃ L D' g', ExecA Terminal blank endSym mark (PERIOD_R k) ts L ∧
      EncR blank startSym endSym mark x (s + (q - first))
        (s + (p + first) + (q - first))
        ⟨D', q - first, 0, p + first, first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r (p + first) (q - first)
        ⟨D', q - first, 0, p + first, first, S, r⟩ g' ∧
      L.length ≤ first * (3 * k + 17) + 8 := by
  have hfq : first ≤ q := (Nat.le_mul_of_pos_left first hk).trans hcmp.1
  have he0 : EncR blank startSym endSym mark x ((s + (q - first)) + first)
      (s + p + q) ⟨D, (q - first) + first, 0, p, first, S, r⟩ g ts := by
    have hq : q - first + first = q := by omega
    simpa only [Nat.add_assoc, hq] using he
  obtain ⟨ha, hb⟩ := (signedOK_iff k r p q _ _).mp hok
  obtain ⟨L, D', bn', hx, he1, hb1, hc⟩ := PERIOD_R_spec (Terminal := Terminal)
    hmark k first (s + (q - first)) (s + p + q) D (q - first) p S r
    ((k - 1) * p) (q + 1) g ts he0 hb (by omega)
  have hpq : s + p + q = s + (p + first) + (q - first) := by omega
  rw [hpq] at he1
  refine ⟨L, D', ⟨g.ap, g.an, bn'⟩, hx, he1, ?_, hc⟩
  apply (signedOK_iff k r (p + first) (q - first) _ _).mpr
  constructor
  · have hh : (p + first) + (q - first) = p + q := by omega
    rw [hh]; exact ha
  · obtain ⟨eb1, eb2⟩ := hb1
    dsimp only at eb1 eb2
    have hmul : (k - 1) * (p + first) = (k - 1) * p + (k - 1) * first := by ring
    have hk1 : k - 1 + 1 = k := by omega
    have hy : k * first = (k - 1) * first + first := by
      calc k * first = (k - 1 + 1) * first := by rw [hk1]
           _ = (k - 1) * first + first := by ring
    constructor <;> dsimp only <;> omega

theorem RESET_R_signed_spec (hmark : mark ≠ blank) (k r s p q D first S : ℕ)
    (hk : 0 < k) (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length) :
    ∃ L D' g', ExecA Terminal blank endSym mark (RESET_R k) ts L ∧
      EncR blank startSym endSym mark x (s + 0) (s + (p + shiftNoPeriod q k) + 0)
        ⟨D', 0, 0, p + shiftNoPeriod q k, first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r (p + shiftNoPeriod q k) 0
        ⟨D', 0, 0, p + shiftNoPeriod q k, first, S, r⟩ g' ∧
      L.length ≤ 19 * q + 7 + (3 * k + 7) * shiftNoPeriod q k := by
  obtain ⟨ha, hb⟩ := (signedOK_iff k r p q _ _).mp hok
  obtain ⟨L, D', g', hx, he1, ha1, hb1, hc⟩ := RESET_R_spec (Terminal := Terminal)
    hmark k r s p q D first S r hk g ts he hfit ha hb
  refine ⟨L, D', g', hx, ?_, ?_, hc⟩
  · simpa only [Nat.add_zero, Nat.add_assoc] using EncR_of_EncS he1 rfl
  · apply (signedOK_iff k r (p + shiftNoPeriod q k) 0 _ _).mpr
    exact ⟨ha1, hb1⟩

/-- info: 'PalPeg.GSPreProg.PERIOD_R_signed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PERIOD_R_signed_spec

end PalPeg.GSPreProg
