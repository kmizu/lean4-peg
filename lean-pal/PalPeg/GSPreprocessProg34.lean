import PalPeg.GSPreprocessProg33

/-! # Restore the ordinary output representation without changing the result flag -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def CE_CASE (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .seq (.act (tCe, .blk, .left))
    (.ite (.notMark tCe) (.seq (.act (tCe, .keep, .right)) yes)
      (.seq (.act (tCe, .keep, .right)) no))

def ceCaseTest (blank : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce (probe blank ts.Ce) .right]

theorem ceCaseTest_restore (ts : Tapes sc) {e : ℕ}
    (he : Tape.CounterView' blank mark ts.Ce e) :
    applyActs blank (ceCaseTest blank ts) ts = ts := ct_probe_restore ctCe ts he

theorem CE_CASE_exec (hmark : mark ≠ blank) (ts : Tapes sc) {e : ℕ}
    (he : Tape.CounterView' blank mark ts.Ce e) (yes no : Prog A9 Cond9)
    (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (if e = 0 then no else yes) ts L) :
    ExecA Terminal blank endSym mark (CE_CASE yes no) ts (ceCaseTest blank ts ++ L) := by
  have hr := ceCaseTest_restore ts he
  have hrx (P : Prog A9 Cond9) (hP : ExecA Terminal blank endSym mark P ts L) :
      ExecA Terminal blank endSym mark (.seq (.act (tCe, .keep, .right)) P)
        (applyAct blank ts (Act.Ce blank .left)) ([Act.Ce (probe blank ts.Ce) .right] ++ L) := by
    apply execA_seq (execA_ct_keep ctCe .right _)
    change ExecA Terminal blank endSym mark P (applyActs blank (ceCaseTest blank ts) ts) L
    rw [hr]; exact hP
  have hz := probe_iff hmark he
  apply execA_seq (execA_ct_put ctCe .left ts)
  by_cases he0 : e = 0
  · apply execA_ite_neg
    · change decide (probe blank ts.Ce ≠ mark) = false
      simp only [hz.mpr he0, ne_eq, not_true_eq_false, decide_false]
    · apply hrx; simpa only [if_pos he0] using hx
  · apply execA_ite_pos
    · change decide (probe blank ts.Ce ≠ mark) = true
      exact decide_eq_true (fun hh => he0 (hz.mp hh))
    · apply hrx; simpa only [if_neg he0] using hx

def NORMALIZE_R (k : ℕ) : Prog A9 Cond9 := CE_CASE (SUCCESS_NORMALIZE_R k) .skip

theorem NORMALIZE_R_spec (hmark : mark ≠ blank) (k r s p q D E first S : ℕ)
    (hk : 0 < k) (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, first, S, r⟩ g)
    (hfit : s + p + q ≤ x.length) (hflag : E ≤ 1)
    (hstop : E = 0 → (x.drop s).length ≤ p) :
    ∃ L D' g', ExecA Terminal blank endSym mark (NORMALIZE_R k) ts L ∧
      EncS blank startSym endSym mark x s (s + p)
        ⟨D', 0, E, p, first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r p 0 ⟨D', 0, E, p, first, S, r⟩ g' ∧ L.length ≤ 21 * q + 9 := by
  have ht := ceCaseTest_restore ts he.enc.base.ce
  by_cases he0 : E = 0
  · have hq : q = 0 := by
      have hh := hstop he0
      rw [List.length_drop] at hh
      omega
    subst q
    have hes := EncR_to_EncS he rfl
    refine ⟨ceCaseTest blank ts ++ [], D, g,
      CE_CASE_exec hmark ts he.enc.base.ce _ _ [] (by rw [if_pos he0]; exact execA_skip),
      ?_, hok, ?_⟩
    · rw [List.append_nil, ht]
      simpa only [Nat.add_zero] using hes
    · simp [ceCaseTest]
  · have he1 : E = 1 := by omega
    subst E
    obtain ⟨L, D', g', hx, he', hok', hc⟩ := SUCCESS_NORMALIZE_R_spec
      (Terminal := Terminal) hmark k r s p q D first S hk g ts he hok
    refine ⟨ceCaseTest blank ts ++ L, D', g',
      CE_CASE_exec hmark ts he.enc.base.ce _ _ L (by simpa using hx), ?_, hok', ?_⟩
    · rw [applyActs_append, ht]; exact he'
    · simp only [List.length_append, ceCaseTest, List.length_cons, List.length_nil]
      omega

/-- info: 'PalPeg.GSPreProg.NORMALIZE_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NORMALIZE_R_spec

end PalPeg.GSPreProg
