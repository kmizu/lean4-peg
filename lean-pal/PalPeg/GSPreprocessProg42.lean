import PalPeg.GSPreprocessProg41

/-! # A complete finite first-search iteration -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def CD_CASE (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .seq (.act (tCd, .blk, .left))
    (.ite (.notMark tCd) (.seq (.act (tCd, .keep, .right)) yes)
      (.seq (.act (tCd, .keep, .right)) no))

def cdCaseTest (blank : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  [Act.Cd blank .left, Act.Cd (probe blank ts.Cd) .right]

theorem cdCaseTest_restore (ts : Tapes sc) {d : ℕ}
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    applyActs blank (cdCaseTest blank ts) ts = ts := ct_probe_restore ctCd ts hd

theorem CD_CASE_exec (hmark : mark ≠ blank) (ts : Tapes sc) {d : ℕ}
    (hd : Tape.CounterView' blank mark ts.Cd d) (yes no : Prog A9 Cond9)
    (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (if d = 0 then no else yes) ts L) :
    ExecA Terminal blank endSym mark (CD_CASE yes no) ts (cdCaseTest blank ts ++ L) := by
  have hr := cdCaseTest_restore ts hd
  have hrx (P : Prog A9 Cond9) (hP : ExecA Terminal blank endSym mark P ts L) :
      ExecA Terminal blank endSym mark (.seq (.act (tCd, .keep, .right)) P)
        (applyAct blank ts (Act.Cd blank .left)) ([Act.Cd (probe blank ts.Cd) .right] ++ L) := by
    apply execA_seq (execA_ct_keep ctCd .right _)
    change ExecA Terminal blank endSym mark P (applyActs blank (cdCaseTest blank ts) ts) L
    rw [hr]; exact hP
  have hz := probe_iff hmark hd
  apply execA_seq (execA_ct_put ctCd .left ts)
  by_cases hd0 : d = 0
  · apply execA_ite_neg
    · change decide (probe blank ts.Cd ≠ mark) = false
      simp only [hz.mpr hd0, ne_eq, not_true_eq_false, decide_false]
    · apply hrx; simpa only [if_pos hd0] using hx
  · apply execA_ite_pos
    · change decide (probe blank ts.Cd ≠ mark) = true
      exact decide_eq_true (fun hh => hd0 (hz.mp hh))
    · apply hrx; simpa only [if_neg hd0] using hx

def FIRST_BODY (k : ℕ) : Prog A9 Cond9 := .seq FIRST_SCAN (CD_CASE (FIRST_RESET k) .skip)

theorem FIRST_BODY_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k s p F S R : ℕ) (hk : 0 < k) (hs : s ≤ x.length) (hp : s + p < x.length)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ g ts) :
    let q := firstInner (x.drop s) k p ((x.drop s).length + 1) 0
    let δ := shiftNoPeriod q k
    ∃ L, ExecA Terminal blank endSym mark (FIRST_BODY k) ts L ∧
      (if q = (k - 1) * p then
        EncS blank startSym endSym mark x (s + q) (s + p + q)
          ⟨0, q, 0, p, F, S, R⟩ g (applyActs blank L ts)
      else EncS blank startSym endSym mark x s (s + p + δ)
          ⟨(k - 1) * (p + δ), 0, 0, p + δ, F, S, R⟩
          ⟨g.ap - δ, g.an, g.bn⟩ (applyActs blank L ts)) ∧
      L.length ≤ (k + 30) * (1 + firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0) := by
  dsimp only
  let q := firstInner (x.drop s) k p ((x.drop s).length + 1) 0
  let W := firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0
  have hi := mSteps_firstInner (k := k) (p := p) hs ((x.drop s).length + 1) 0
    ((k - 1) * p) (by omega) (by omega)
  have hj := mSteps_le_mWork x ((x.drop s).length + 1) (s + 0) (s + p + 0) ((k - 1) * p)
  have hqW : q ≤ W := by dsimp [q, W]; omega
  obtain ⟨L1, hx1, he1, _, hfit, hq, hc1⟩ := FIRST_SCAN_firstInner
    (Terminal := Terminal) hend hmark k s p 0 0 F S R g ts hs (by omega) (by omega)
    (by simpa only [Nat.add_zero, Nat.sub_zero] using he)
  let t1 := applyActs blank L1 ts
  have he1' : EncS blank startSym endSym mark x (s + q) (s + p + q)
      ⟨(k - 1) * p - q, q, 0, p, F, S, R⟩ g t1 := he1
  by_cases hmatch : q = (k - 1) * p
  · have hd0 : (k - 1) * p - q = 0 := by omega
    have hx2 := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t1 he1'.base.cd
      (FIRST_RESET k) .skip [] (by rw [if_pos hd0]; exact execA_skip)
    refine ⟨L1 ++ (cdCaseTest blank t1 ++ []), execA_seq hx1 hx2, ?_, ?_⟩
    · rw [if_pos hmatch]
      simp only [applyActs_append, List.append_nil]
      change EncS blank startSym endSym mark x _ _ _ _ (applyActs blank (cdCaseTest blank t1) t1)
      rw [cdCaseTest_restore t1 he1'.base.cd]
      simpa only [hd0] using he1'
    · simp only [List.length_append, List.length_nil, cdCaseTest, List.length_cons]
      dsimp only [W] at hqW
      nlinarith
  · have hd0 : (k - 1) * p - q ≠ 0 := by change q ≤ _ at hq; omega
    have hδ := shiftNoPeriod_le_succ hk q
    have hfit' : s + p + shiftNoPeriod q k ≤ x.length := by
      by_cases hq0 : q = 0
      · rw [hq0, shiftNoPeriod_zero hk]; omega
      · have := shiftNoPeriod_le_of_pos hk (show 0 < q by omega)
        change s + p + q ≤ x.length at hfit
        omega
    obtain ⟨L2, hx2, he2, hc2⟩ := FIRST_RESET_spec (Terminal := Terminal) hmark k s p q F S R
      hk hq g t1 he1' hfit'
    have hxc := CD_CASE_exec hmark t1 he1'.base.cd (FIRST_RESET k) .skip L2
      (by rw [if_neg hd0]; exact hx2)
    refine ⟨L1 ++ (cdCaseTest blank t1 ++ L2), execA_seq hx1 hxc, ?_, ?_⟩
    · rw [if_neg hmatch]
      simp only [applyActs_append]
      change EncS blank startSym endSym mark x _ _ _ _
        (applyActs blank L2 (applyActs blank (cdCaseTest blank t1) t1))
      rw [cdCaseTest_restore t1 he1'.base.cd]
      exact he2
    · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
      have hmul := Nat.mul_le_mul_left (k + 6) hδ
      have hmulW := Nat.mul_le_mul_left (k + 21) hqW
      change L1.length ≤ 5 * W at hc1
      change L1.length + (2 + L2.length) ≤ (k + 30) * (1 + W)
      nlinarith

end PalPeg.GSPreProg
