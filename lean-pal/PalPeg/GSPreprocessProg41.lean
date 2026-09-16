import PalPeg.GSPreprocessProg40

/-! # Complete finite first-phase reset -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def FIRST_RESET (k : ℕ) : Prog A9 Cond9 :=
  .seq (FIRST_REWIND k) (.seq MAX_ONE (FIRST_SHIFT k))

theorem FIRST_RESET_spec (hmark : mark ≠ blank) (k s p q F S R : ℕ)
    (hk : 0 < k) (hq : q ≤ (k - 1) * p) (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x (s + q) (s + p + q)
      ⟨(k - 1) * p - q, q, 0, p, F, S, R⟩ g ts)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length) :
    ∃ L, ExecA Terminal blank endSym mark (FIRST_RESET k) ts L ∧
      EncS blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
        ⟨(k - 1) * (p + shiftNoPeriod q k), 0, 0, p + shiftNoPeriod q k, F, S, R⟩
        ⟨g.ap - shiftNoPeriod q k, g.an, g.bn⟩ (applyActs blank L ts) ∧
      L.length ≤ 10 * q + 7 + (k + 6) * shiftNoPeriod q k := by
  obtain ⟨L1, hx1, he1, hc1⟩ := FIRST_REWIND_spec (Terminal := Terminal)
    hmark k q s (s + p) ((k - 1) * p - q) 0 p F S R hk g ts he
  let t1 := applyActs blank L1 ts
  let L2 := maxOneActs blank mark t1
  let t2 := applyActs blank L2 t1
  have hx2 : ExecA Terminal blank endSym mark MAX_ONE t1 L2 := MAX_ONE_exec t1
  have hm : max 1 (0 + stays k q 0) = shiftNoPeriod q k := by
    rw [stays_zero k hk q, Nat.zero_add]
    rfl
  have hd : (k - 1) * p - q + q = (k - 1) * p := by omega
  have he2 : EncS blank startSym endSym mark x s (s + p)
      ⟨(k - 1) * p, 0, shiftNoPeriod q k, p, F, S, R⟩ g t2 := by
    have hh := maxOneS_enc hmark he1
    simpa only [hm, hd] using hh
  obtain ⟨L3, hx3, he3, hc3⟩ := FIRST_SHIFT_spec (Terminal := Terminal) hmark k
    (shiftNoPeriod q k) s (s + p) ((k - 1) * p) 0 p F S R g t2 he2 hfit
  have hp : (k - 1) * p + (k - 1) * shiftNoPeriod q k =
      (k - 1) * (p + shiftNoPeriod q k) := by ring
  refine ⟨L1 ++ (L2 ++ L3), execA_seq hx1 (execA_seq hx2 hx3), ?_, ?_⟩
  · simp only [applyActs_append]
    simpa only [hp] using he3
  · have hc2 := maxOneActs_length_le blank mark t1
    simp only [List.length_append]
    change L1.length + (L2.length + L3.length) ≤ _
    dsimp only [L2]
    nlinarith

/-- info: 'PalPeg.GSPreProg.FIRST_RESET_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_RESET_spec

end PalPeg.GSPreProg
