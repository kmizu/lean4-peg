import PalPeg.GSPreprocessProg12

/-! # The second-phase period-shift comparison oracle -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)} {a b D Q P F S R : ℕ} {g : Ctr3} {t u : Tapes sc}

theorem encS_cfq_restore
    (h : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g t)
    (hf : Tape.CounterView' blank mark u.Cf F)
    (hq : Tape.CounterView' blank mark u.Cq Q)
    (he : Tape.CounterView' blank mark u.Ce 0)
    (ho : ∀ j, j ≠ tCf → j ≠ tCq → j ≠ tCe → getT u j = getT t j) :
    EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u := by
  refine ⟨⟨?_, ?_, ?_, hq, he, ?_, hf, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change Tape.SeqView blank (getT u tV1) (pword startSym endSym x) (a + 1)
    rw [ho tV1 (by decide) (by decide) (by decide)]
    exact h.base.v1
  · change Tape.SeqView blank (getT u tV2) (pword startSym endSym x) (b + 1)
    rw [ho tV2 (by decide) (by decide) (by decide)]
    exact h.base.v2
  · change Tape.CounterView' blank mark (getT u tCd) D
    rw [ho tCd (by decide) (by decide) (by decide)]
    exact h.base.cd
  · change Tape.CounterView' blank mark (getT u tCp) P
    rw [ho tCp (by decide) (by decide) (by decide)]
    exact h.base.cp
  · change Tape.CounterView' blank mark (getT u tCs) S
    rw [ho tCs (by decide) (by decide) (by decide)]
    exact h.base.cs
  · change Tape.CounterView' blank mark (getT u tCr) R
    rw [ho tCr (by decide) (by decide) (by decide)]
    exact h.base.cr
  · change Tape.CounterView' blank mark (getT u tCa) g.ap
    rw [ho tCa (by decide) (by decide) (by decide)]
    exact h.ca
  · change Tape.CounterView' blank mark (getT u tCb) g.an
    rw [ho tCb (by decide) (by decide) (by decide)]
    exact h.cb
  · change Tape.CounterView' blank mark (getT u tCc) g.bn
    rw [ho tCc (by decide) (by decide) (by decide)]
    exact h.cc

theorem encS_cqr_restore
    (h : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g t)
    (hq : Tape.CounterView' blank mark u.Cq Q)
    (hr : Tape.CounterView' blank mark u.Cr R)
    (he : Tape.CounterView' blank mark u.Ce 0)
    (ho : ∀ j, j ≠ tCq → j ≠ tCr → j ≠ tCe → getT u j = getT t j) :
    EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u := by
  refine ⟨⟨?_, ?_, ?_, hq, he, ?_, ?_, ?_, hr⟩, ?_, ?_, ?_⟩
  · change Tape.SeqView blank (getT u tV1) (pword startSym endSym x) (a + 1)
    rw [ho tV1 (by decide) (by decide) (by decide)]
    exact h.base.v1
  · change Tape.SeqView blank (getT u tV2) (pword startSym endSym x) (b + 1)
    rw [ho tV2 (by decide) (by decide) (by decide)]
    exact h.base.v2
  · change Tape.CounterView' blank mark (getT u tCd) D
    rw [ho tCd (by decide) (by decide) (by decide)]
    exact h.base.cd
  · change Tape.CounterView' blank mark (getT u tCp) P
    rw [ho tCp (by decide) (by decide) (by decide)]
    exact h.base.cp
  · change Tape.CounterView' blank mark (getT u tCf) F
    rw [ho tCf (by decide) (by decide) (by decide)]
    exact h.base.cf
  · change Tape.CounterView' blank mark (getT u tCs) S
    rw [ho tCs (by decide) (by decide) (by decide)]
    exact h.base.cs
  · change Tape.CounterView' blank mark (getT u tCa) g.ap
    rw [ho tCa (by decide) (by decide) (by decide)]
    exact h.ca
  · change Tape.CounterView' blank mark (getT u tCb) g.an
    rw [ho tCb (by decide) (by decide) (by decide)]
    exact h.cb
  · change Tape.CounterView' blank mark (getT u tCc) g.bn
    rw [ho tCc (by decide) (by decide) (by decide)]
    exact h.cc

def ORC2 (k : ℕ) (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  CMUL_LE tCf tCq k (CMUL_LE tCq tCr 1 yes no) no

theorem ORC2_spec (hmark : mark ≠ blank) (k : ℕ) (hk : 0 < k)
    (h : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g t) :
    ∃ (L : List (Act sc)) (u : Tapes sc),
      applyActs blank L t = u ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u ∧
      L.length ≤ 28 * Q + 25 ∧
      ∀ (yes no : Prog A9 Cond9) (LT : List (Act sc)),
        ExecA Terminal blank endSym mark (if k * F ≤ Q ∧ Q ≤ R then yes else no) u LT →
        ExecA Terminal blank endSym mark (ORC2 k yes no) t (L ++ LT) := by
  obtain ⟨L1, v, hv, hvf, hvq, hve, hvo, hc1, hx1⟩ :=
    CMUL_LE_spec (Terminal := Terminal) (endSym := endSym) ctCf ctCq
      (by change tCf ≠ tCq; decide) (by change tCe ≠ tCf; decide)
      (by change tCe ≠ tCq; decide) hmark k F Q t h.base.cf h.base.cq h.base.ce
  have hvE := encS_cfq_restore h hvf hvq hve hvo
  have hc1' : L1.length ≤ 14 * Q + 11 := hc1.trans (cmul_cost_le_right hk F Q)
  by_cases hF : k * F ≤ Q
  · obtain ⟨L2, u, hu, huq, hur, hue, huo, hc2, hx2⟩ :=
      CMUL_LE_spec (Terminal := Terminal) (endSym := endSym) ctCq ctCr
        (by change tCq ≠ tCr; decide) (by change tCe ≠ tCq; decide)
        (by change tCe ≠ tCr; decide) hmark 1 Q R v hvE.base.cq hvE.base.cr hvE.base.ce
    have huE := encS_cqr_restore hvE huq hur hue huo
    have hc2' : L2.length ≤ 14 * Q + 14 := hc2.trans (cmul_cost_one_le_left Q R)
    refine ⟨L1 ++ L2, u, ?_, huE, ?_, ?_⟩
    · rw [applyActs_append, hv, hu]
    · rw [List.length_append]
      omega
    · intro yes no LT hLT
      have h2 : ExecA Terminal blank endSym mark (CMUL_LE tCq tCr 1 yes no) v (L2 ++ LT) := by
        apply hx2
        simpa only [Nat.one_mul, hF, true_and] using hLT
      have h1 := hx1 (CMUL_LE tCq tCr 1 yes no) no (L2 ++ LT)
        (by simpa only [if_pos hF] using h2)
      simpa only [ORC2, ctCf, ctCq, List.append_assoc] using h1
  · refine ⟨L1, v, hv, hvE, by omega, ?_⟩
    intro yes no LT hLT
    apply hx1 (CMUL_LE tCq tCr 1 yes no) no LT
    simpa only [if_neg hF, hF, false_and, ite_false] using hLT

theorem ORC2_oracle_spec (hmark : mark ≠ blank) (k : ℕ) (hk : 0 < k)
    (h : EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g t) :
    ∃ (L : List (Act sc)) (u : Tapes sc),
      applyActs blank L t = u ∧
      EncS blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u ∧
      L.length ≤ 28 * Q + 25 ∧
      ∀ (yes no : Prog A9 Cond9) (LT : List (Act sc)),
        ExecA Terminal blank endSym mark (if orc2R k t then yes else no) u LT →
        ExecA Terminal blank endSym mark (ORC2 k yes no) t (L ++ LT) := by
  simpa only [orc2R, fOf_eq h.base, qOf_eq h.base, rOf_eq h.base,
    decide_eq_true_eq] using ORC2_spec (Terminal := Terminal) hmark k hk h

/-- info: 'PalPeg.GSPreProg.ORC2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ORC2_spec

/-- info: 'PalPeg.GSPreProg.ORC2_oracle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ORC2_oracle_spec

end PalPeg.GSPreProg
