import PalPeg.GSPreprocessProg23

/-! # Finite second-phase reset with reach-difference rewind

The reset is assembled from counter-driven rewind and shift programs. Its
only numerical program parameter is the fixed exponent `k`.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def RESET_R (k : ℕ) : Prog A9 Cond9 :=
  .seq (REWIND_R k) (.seq MAX_ONE (SHIFT_SIGNED k))

theorem RESET_R_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k r s p q D F S R : ℕ) (hk : 0 < k)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, 0, p, F, S, R⟩ g ts)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length)
    (ha : SgnA r (p + q) g)
    (hb : SgnB ((k - 1) * p) (q + 1) ⟨D, q, 0, p, F, S, R⟩ g) :
    ∃ L D' g', ExecA Terminal blank endSym mark (RESET_R k) ts L ∧
      EncS blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
        ⟨D', 0, 0, p + shiftNoPeriod q k, F, S, R⟩ g' (applyActs blank L ts) ∧
      SgnA r (p + shiftNoPeriod q k) g' ∧
      SgnB ((k - 1) * (p + shiftNoPeriod q k)) 1
        ⟨D', 0, 0, p + shiftNoPeriod q k, F, S, R⟩ g' ∧
      L.length ≤ 19 * q + 7 + (3 * k + 7) * shiftNoPeriod q k := by
  obtain ⟨L1, D1, g1, hx1, he1, ha1, hb1, hc1⟩ :=
    REWIND_R_spec (Terminal := Terminal) hmark k q s (s + p) D 0 p F S R
      r p ((k - 1) * p) 1 hk g ts he ha (by simpa only [Nat.add_comm 1 q] using hb)
  let t1 := applyActs blank L1 ts
  let L2 := maxOneActs blank mark t1
  let t2 := applyActs blank L2 t1
  have hex2 : ExecA Terminal blank endSym mark MAX_ONE t1 L2 := MAX_ONE_exec t1
  have hm : max 1 (0 + stays k q 0) = shiftNoPeriod q k := by
    rw [stays_zero k hk q, Nat.zero_add]
    rfl
  have he2 : EncS blank startSym endSym mark x s (s + p)
      ⟨D1, 0, shiftNoPeriod q k, p, F, S, R⟩ g1 t2 := by
    have hh := maxOneS_enc hmark he1
    simpa only [hm] using hh
  have hb2 : SgnB ((k - 1) * p) 1 ⟨D1, 0, shiftNoPeriod q k, p, F, S, R⟩ g1 := hb1
  obtain ⟨L3, hx3, heff3, hc3⟩ := SHIFT_SIGNED_spec (Terminal := Terminal) hmark k
    (shiftNoPeriod q k) s (s + p) D1 0 p F S R r p ((k - 1) * p) 1 g1 t2 he2 hfit ha1 hb2
  obtain ⟨D3, ap3, an3, bn3, he3, ha3, hb3⟩ := shiftLoopS_enc hmark k
    (shiftNoPeriod q k) s (s + p) D1 0 0 p F S R r p ((k - 1) * p) 1 g1 t2
    (by simpa only [Nat.zero_add] using he2) hfit ha1 hb2
  have hmB : (k - 1) * p + (k - 1) * shiftNoPeriod q k =
      (k - 1) * (p + shiftNoPeriod q k) := by ring
  rw [hmB] at hb3
  refine ⟨L1 ++ (L2 ++ L3), D3, ⟨ap3, an3, bn3⟩,
    execA_seq hx1 (execA_seq hex2 hx3), ?_, ha3, hb3, ?_⟩
  · simp only [applyActs_append]
    change EncS blank startSym endSym mark x _ _ _ _ (applyActs blank L3 t2)
    rw [heff3]
    exact he3
  · have hc2 := maxOneActs_length_le blank mark t1
    simp only [List.length_append]
    change L1.length + (L2.length + L3.length) ≤ _
    dsimp only [L2]
    nlinarith

/-- info: 'PalPeg.GSPreProg.RESET_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RESET_R_spec

end PalPeg.GSPreProg
