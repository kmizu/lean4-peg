import PalPeg.GSPreprocessProg25

/-! # Period shifts maintaining the reach difference -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem OneSgn_normal {R Q : ℕ} (hq : Q ≤ R) (tp : TapeConfiguration sc) :
    OneSgn blank mark R Q tp ↔ Tape.CounterView' blank mark tp (R - Q) := by
  simp only [OneSgn, Nat.not_lt.mpr hq, decide_false, Nat.sub_eq_zero_of_le hq,
    Nat.add_zero, flagCV_normal]

theorem EncR_physical_iff {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hq : c.q ≤ c.r) :
    EncR blank startSym endSym mark x a b c g ts ↔
      EncS blank startSym endSym mark x a b
        ⟨c.d, c.q, c.e, c.p, c.f, c.s, c.r - c.q⟩ g ts := by
  constructor
  · intro h
    exact ⟨⟨h.enc.base.v1, h.enc.base.v2, h.enc.base.cd, h.enc.base.cq,
      h.enc.base.ce, h.enc.base.cp, h.enc.base.cf, h.enc.base.cs,
      (OneSgn_normal hq ts.Cr).mp h.diff⟩, h.enc.ca, h.enc.cb, h.enc.cc⟩
  · intro h
    exact ⟨⟨⟨h.base.v1, h.base.v2, h.base.cd, h.base.cq, h.base.ce, h.base.cp,
      h.base.cf, h.base.cs, ⟨rfl, rfl, Tape.blanks_nil blank⟩⟩, h.ca, h.cb, h.cc⟩,
      (OneSgn_normal hq ts.Cr).mpr h.base.cr⟩

def PERIOD_R (k : ℕ) : Prog A9 Cond9 := .seq (PERIOD_SIGNED k) ADD_F_R

theorem PERIOD_R_spec (hmark : mark ≠ blank) (k n a b D Q P S R M N : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (a + n) b ⟨D, Q + n, 0, P, n, S, R⟩ g ts)
    (hb : SgnB M N ⟨D, Q + n, 0, P, n, S, R⟩ g) (hq : Q + n ≤ R) :
    ∃ L D' bn', ExecA Terminal blank endSym mark (PERIOD_R k) ts L ∧
      EncR blank startSym endSym mark x a b ⟨D', Q, 0, P + n, n, S, R⟩
        ⟨g.ap, g.an, bn'⟩ (applyActs blank L ts) ∧
      SgnB (M + k * n) N ⟨D', Q, 0, P + n, n, S, R⟩ ⟨g.ap, g.an, bn'⟩ ∧
      L.length ≤ n * (3 * k + 17) + 8 := by
  have he0 := (EncR_physical_iff hq).mp he
  obtain ⟨L1, D', bn', hx1, he1, hb1, hc1⟩ := PERIOD_SIGNED_spec
    (Terminal := Terminal) hmark k n a b D Q P S (R - (Q + n)) M N g ts he0 hb
  obtain ⟨L2, hx2, he2, hc2⟩ := ADD_F_R_spec (Terminal := Terminal) hmark n a b D' Q
    (P + n) S (R - (Q + n)) ⟨g.ap, g.an, bn'⟩ _ he1
  have hr : R - (Q + n) + n = R - Q := by omega
  rw [hr] at he2
  refine ⟨L1 ++ L2, D', bn', execA_seq hx1 hx2, ?_, hb1, ?_⟩
  · rw [applyActs_append]
    exact (EncR_physical_iff (by change Q ≤ R; omega)).mpr he2
  · rw [List.length_append, hc2]
    nlinarith

/-- info: 'PalPeg.GSPreProg.PERIOD_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PERIOD_R_spec

end PalPeg.GSPreProg
