import PalPeg.GSPreprocessProg17

/-! # Encodings and an amortization-compatible second-phase oracle -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

/-- A proof-only normal representative for the reach tape. -/
def shadowR (blank mark : Fin sc) (R : ℕ) (ts : Tapes sc) : Tapes sc :=
  { ts with Cr := ⟨List.replicate R blank ++ [mark], blank, []⟩ }

theorem shadowR_get (R : ℕ) (ts : Tapes sc) (j : Fin 12) (hj : j ≠ tCr) :
    getT (shadowR blank mark R ts) j = getT ts j := by
  fin_cases j <;> first | rfl | exact False.elim (hj rfl)

theorem shadowR_applyAct (R : ℕ) (ts : Tapes sc) (a : Act sc)
    (ha : actTape a ≠ tCr) :
    shadowR blank mark R (applyAct blank ts a) =
      applyAct blank (shadowR blank mark R ts) a := by
  cases a <;> first | rfl | exact False.elim (ha rfl)

theorem shadowR_applyActs (R : ℕ) (L : List (Act sc))
    (hL : ∀ a ∈ L, actTape a ≠ tCr) (ts : Tapes sc) :
    shadowR blank mark R (applyActs blank L ts) =
      applyActs blank L (shadowR blank mark R ts) := by
  induction L generalizing ts with
  | nil => rfl
  | cons a L ih =>
    simp only [applyActs, List.foldl_cons]
    rw [show List.foldl (applyAct blank) (applyAct blank ts a) L =
      applyActs blank L (applyAct blank ts a) from rfl]
    rw [ih (fun b hb => hL b (List.mem_cons_of_mem a hb)),
      shadowR_applyAct R ts a (hL a (List.mem_cons_self ..))]
    rfl

/-- All original counters except `Cr` keep their old meanings. `Cr` holds `r-q`. -/
structure EncR (blank startSym endSym mark : Fin sc) (x : List (Fin sc))
    (a b : ℕ) (c : Ctr) (g : Ctr3) (ts : Tapes sc) : Prop where
  enc : EncS blank startSym endSym mark x a b c g (shadowR blank mark c.r ts)
  diff : OneSgn blank mark c.r c.q ts.Cr

theorem EncR_of_EncS {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (h : EncS blank startSym endSym mark x a b c g ts) (hq : c.q = 0) :
    EncR blank startSym endSym mark x a b c g ts := by
  refine ⟨⟨⟨h.base.v1, h.base.v2, h.base.cd, h.base.cq, h.base.ce,
    h.base.cp, h.base.cf, h.base.cs, ?_⟩, h.ca, h.cb, h.cc⟩, ?_⟩
  · exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · rw [hq]
    exact OneSgn_zero.mpr h.base.cr

theorem EncR_to_EncS {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (h : EncR blank startSym endSym mark x a b c g ts) (hq : c.q = 0) :
    EncS blank startSym endSym mark x a b c g ts := by
  refine ⟨⟨h.enc.base.v1, h.enc.base.v2, h.enc.base.cd, h.enc.base.cq, h.enc.base.ce,
    h.enc.base.cp, h.enc.base.cf, h.enc.base.cs, ?_⟩, h.enc.ca, h.enc.cb, h.enc.cc⟩
  have hd := h.diff
  rw [hq] at hd
  exact OneSgn_zero.mp hd

theorem EncR_cfq_restore {a b D Q P F S R : ℕ} {g : Ctr3} {ts u : Tapes sc}
    (h : EncR blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g ts)
    (hf : Tape.CounterView' blank mark u.Cf F)
    (hq : Tape.CounterView' blank mark u.Cq Q)
    (he : Tape.CounterView' blank mark u.Ce 0)
    (ho : ∀ j, j ≠ tCf → j ≠ tCq → j ≠ tCe → getT u j = getT ts j) :
    EncR blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u := by
  refine ⟨encS_cfq_restore h.enc hf hq he ?_, ?_⟩
  · intro j hf hq he
    by_cases hj : j = tCr
    · subst j; rfl
    · rw [shadowR_get R u j hj, shadowR_get R ts j hj]
      exact ho j hf hq he
  · have hr := ho tCr (by decide) (by decide) (by decide)
    change u.Cr = ts.Cr at hr
    rw [hr]
    exact h.diff

/-- Test `q≤r` in constant time, then compare `k*first≤q` and restore its operands. -/
def ORC2_FAST (k : ℕ) (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .ite (.notMark tCr) (CMUL_LE tCf tCq k yes no) no

theorem cmul_cost_le_left (k a b : ℕ) :
    scaledGroups k a b * (4 * k + 10) +
      3 * min k (b - k * scaledGroups k a b) + 11 ≤ (4 * k + 10) * a + 3 * k + 11 := by
  have hg := (scaledGroups_spec k a b).1
  have hm := Nat.min_le_left k (b - k * scaledGroups k a b)
  nlinarith

theorem ORC2_FAST_spec (hmark : mark ≠ blank) (k : ℕ) (hk : 0 < k)
    {a b D Q P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (h : EncR blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g ts) :
    ∃ (L : List (Act sc)) (u : Tapes sc),
      applyActs blank L ts = u ∧
      EncR blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ g u ∧
      L.length ≤ (if k * F ≤ Q ∧ Q ≤ R then (4 * k + 10) * F + 3 * k + 11
        else 14 * Q + 11) ∧
      ∀ (yes no : Prog A9 Cond9) (LT : List (Act sc)),
        ExecA Terminal blank endSym mark (if k * F ≤ Q ∧ Q ≤ R then yes else no) u LT →
        ExecA Terminal blank endSym mark (ORC2_FAST k yes no) ts (L ++ LT) := by
  have hr := OneSgn_nonneg (endSym := endSym) ctCr hmark h.diff
  by_cases hR : Q ≤ R
  · have htest : condOf9 endSym mark (.notMark tCr)
        (fun j => (getT ts j).focus) = true := hr.mpr hR
    obtain ⟨L, u, hu, hf, hq, he, ho, hc, hx⟩ :=
      CMUL_LE_spec (Terminal := Terminal) (endSym := endSym) ctCf ctCq
        (by change tCf ≠ tCq; decide) (by change tCe ≠ tCf; decide)
        (by change tCe ≠ tCq; decide) hmark k F Q ts h.enc.base.cf h.enc.base.cq h.enc.base.ce
    refine ⟨L, u, hu, EncR_cfq_restore h hf hq he ho, ?_, ?_⟩
    · by_cases hF : k * F ≤ Q
      · rw [if_pos ⟨hF, hR⟩]
        exact hc.trans (cmul_cost_le_left k F Q)
      · rw [if_neg (fun hh => hF hh.1)]
        exact hc.trans (cmul_cost_le_right hk F Q)
    · intro yes no LT hLT
      apply execA_ite_pos htest
      apply hx
      simpa only [hR, and_true] using hLT
  · refine ⟨[], ts, rfl, h, by simp, ?_⟩
    intro yes no LT hLT
    have htest : condOf9 endSym mark (.notMark tCr)
        (fun j => (getT ts j).focus) = false := Bool.eq_false_iff.mpr (fun hh => hR (hr.mp hh))
    apply execA_ite_neg htest
    simpa only [hR, and_false, ite_false, List.nil_append] using hLT

/-- info: 'PalPeg.GSPreProg.ORC2_FAST_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ORC2_FAST_spec

end PalPeg.GSPreProg
