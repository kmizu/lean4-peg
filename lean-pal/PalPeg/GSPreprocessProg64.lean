import PalPeg.GSPreprocessProg63

/-! # Finite branching and strict progress for decomposition -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}


theorem strip_second_progress (k : ℕ) (hk : 3 ≤ k) {s p m p2 : ℕ}
    (hs : s ≤ x.length) (hfp : firstPeriod (x.drop s) k = some (p, m))
    (hsp : secondPeriod (x.drop s) k p
      (extendReach (x.drop s) p (x.length + 1) m) = some p2) :
    s < stripLoop2 x k p2 (x.length + 1) s ∧
      stripLoop2 x k p2 (x.length + 1) s ≤ x.length := by
  obtain ⟨hleast, hm⟩ := firstPeriod_some (x.drop s) k hk hfp
  subst m
  have hr := extendReach_spec (x.drop s) p (x.length + 1) (k * p) (by simp; omega)
    (Nat.le_mul_of_pos_left p (by omega)) hleast.1.2.1 hleast.1.2.2
  obtain ⟨hsec, _⟩ := secondPeriod_some (x.drop s) k p
    (extendReach (x.drop s) p (x.length + 1) (k * p)) p2 hk hleast hr.2.2.1 hr.2.1 hsp
  have hle : p ≤ p2 := hleast.2 _ (kRep_of_second hsec)
  have hne : p ≠ p2 := by
    intro heq
    subst p2
    exact not_second_reach hr.2 hsec
  have hlt : p < p2 := lt_of_le_of_ne hle hne
  have hge := stripLoop2_ge x k p2 (x.length + 1) s
  have hstop := stripLoop2_spec x k p2 hk (x.length + 1) s hs (by omega)
  have hsne : s ≠ stripLoop2 x k p2 (x.length + 1) s :=
    fun heq => hstop p hlt (heq ▸ hleast.1)
  exact ⟨by omega, stripLoop2_le x k p2 hk (x.length + 1) s hs⟩

/-- info: 'PalPeg.GSPreProg.strip_second_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strip_second_progress

def DECOMP_STOP : Prog A9 Cond9 := .seq SWAP (.act (tCe, .blk, .right))

theorem DECOMP_STOP_spec (hmark : mark ≠ blank) {s P F R : ℕ} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x s (s + P)
      ⟨0, 0, 0, P, F, s, R⟩ ⟨0, 0, 0⟩ ts) :
    ∃ L, ExecA Terminal blank endSym mark DECOMP_STOP ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 1, F, 0, s, R⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧ L.length = 3 * P + 3 * F + 9 := by
  obtain ⟨L, hx, h, hl⟩ := SWAP_spec (Terminal := Terminal) hmark (Q := 0) (by simpa using he)
  refine ⟨_, execA_seq hx (execA_ct_put ctCe .right _), ?_, ?_⟩
  · rw [applyActs_append]
    exact ceFlagS_enc h
  · simp only [List.length_append, List.length_cons, List.length_nil, hl]
    omega

def DECOMP_BODY (k : ℕ) : Prog A9 Cond9 :=
  .seq (STEP_SEARCH k) (CE_CASE (.seq DRST (STRIP k)) DECOMP_STOP)

def decompBodyRate (k : ℕ) : ℕ := stepRate k + stripRate k + 2 * k + 30

theorem DECOMP_BODY_no_first (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts)
    (hfp : firstPeriod (x.drop s) k = none) :
    ∃ L, ExecA Terminal blank endSym mark (DECOMP_BODY k) ts L ∧
      EncS blank startSym endSym mark x s s ⟨0, 0, 1, 0, 0, s, 0⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ decompBodyRate k * decomposeStepWork x k s + 9 * k + 200 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := STEP_SEARCH_failure (Terminal := Terminal) hend hmark k hk hs he hfp
  obtain ⟨L2, hx2, h2, hl2⟩ := DECOMP_STOP_spec (Terminal := Terminal) hmark (P := 0) (by simpa using h1)
  let u := applyActs blank L1 ts
  have hc := CE_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark u h1.base.ce
    (.seq DRST (STRIP k)) DECOMP_STOP L2 (by exact hx2)
  refine ⟨_, execA_seq hx1 hc, ?_, ?_⟩
  · rw [applyActs_append, applyActs_append, ceCaseTest_restore u h1.base.ce]
    exact h2
  · simp only [List.length_append, ceCaseTest, List.length_cons, List.length_nil, hl2]
    have hr : stepRate k ≤ decompBodyRate k := by unfold decompBodyRate; omega
    have hm := Nat.mul_le_mul_right (decomposeStepWork x k s) hr
    omega

/-- info: 'PalPeg.GSPreProg.DECOMP_BODY_no_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMP_BODY_no_first

theorem DECOMP_BODY_no_second (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s p m : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts)
    (hfp : firstPeriod (x.drop s) k = some (p, m))
    (hsp : secondPeriod (x.drop s) k p (extendReach (x.drop s) p (x.length + 1) m) = none) :
    ∃ L, ExecA Terminal blank endSym mark (DECOMP_BODY k) ts L ∧
      EncS blank startSym endSym mark x s s
        ⟨0, 0, 1, p, 0, s, extendReach (x.drop s) p (x.length + 1) m⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ decompBodyRate k * decomposeStepWork x k s + 9 * k + 200 := by
  obtain ⟨L1, E, P, hx1, h1, _, hP, _, hE, hl1⟩ := STEP_SEARCH_success
    (Terminal := Terminal) hend hmark k hk hs he hfp
  simp only [hsp, Option.isSome_none, Bool.false_eq_true, if_false] at hE
  subst E
  obtain ⟨L2, hx2, h2, hl2⟩ := DECOMP_STOP_spec (Terminal := Terminal) hmark h1
  let u := applyActs blank L1 ts
  have hc := CE_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark u h1.base.ce
    (.seq DRST (STRIP k)) DECOMP_STOP L2 (by exact hx2)
  refine ⟨_, execA_seq hx1 hc, ?_, ?_⟩
  · rw [applyActs_append, applyActs_append, ceCaseTest_restore u h1.base.ce]
    exact h2
  · simp only [List.length_append, ceCaseTest, List.length_cons, List.length_nil, hl2]
    have hw := firstOuter_success_work (x.drop s) k (x.drop s).length (by omega)
      ((x.drop s).length + 1) 1 p m hfp
    have hstep : decomposeStepWork x k s =
        firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
        (extendReachWork (x.drop s) p (x.length + 1) m +
          secondOuterWork (x.drop s) k p (extendReach (x.drop s) p (x.length + 1) m)
            ((x.drop s).length + 1) 1 0) := by simp only [decomposeStepWork, hfp]
    rw [hstep] at hl1 ⊢
    unfold decompBodyRate
    nlinarith only [hl1, hw.1, hP, Nat.zero_le (stripRate k), Nat.zero_le (stepRate k)]

/-- info: 'PalPeg.GSPreProg.DECOMP_BODY_no_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMP_BODY_no_second

theorem DECOMP_BODY_continue (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s p m p2 : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts)
    (hfp : firstPeriod (x.drop s) k = some (p, m))
    (hsp : secondPeriod (x.drop s) k p (extendReach (x.drop s) p (x.length + 1) m) = some p2) :
    let t := stripLoop2 x k p2 (x.length + 1) s
    ∃ L, ExecA Terminal blank endSym mark (DECOMP_BODY k) ts L ∧
      EncS blank startSym endSym mark x t t ⟨0, 0, 0, 0, 0, t, 0⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧ s < t ∧ t ≤ x.length ∧
      L.length ≤ decompBodyRate k *
        (decomposeStepWork x k s + stripLoop2Work x k p2 (x.length + 1) s) + 9 * k + 200 := by
  obtain ⟨L1, E, P, hx1, h1, _, hP, hans, hE, hl1⟩ := STEP_SEARCH_success
    (Terminal := Terminal) hend hmark k hk hs he hfp
  have hPeq := hans p2 hsp
  subst P
  simp only [hsp, Option.isSome_some, if_true] at hE
  subst E
  obtain ⟨L2, hx2, h2, hl2⟩ := DRST_spec (Terminal := Terminal) hmark (Q := 0) (by simpa using h1)
  obtain ⟨L3, hx3, h3, hl3⟩ := STRIP_spec (Terminal := Terminal) hend hmark k p2 hk
    (x.length + 1) (by omega) (by omega) h2
  let u := applyActs blank L1 ts
  have hc := CE_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark u h1.base.ce
    (.seq DRST (STRIP k)) DECOMP_STOP (L2 ++ L3) (by exact execA_seq hx2 hx3)
  have ht := strip_second_progress k hk (by omega) hfp hsp
  refine ⟨_, execA_seq hx1 hc, ?_, ht.1, ht.2, ?_⟩
  · rw [applyActs_append, applyActs_append, ceCaseTest_restore u h1.base.ce, applyActs_append]
    exact h3
  · simp only [List.length_append, ceCaseTest, List.length_cons, List.length_nil, hl2]
    have hw := firstOuter_success_work (x.drop s) k (x.drop s).length (by omega)
      ((x.drop s).length + 1) 1 p m hfp
    have hm := (firstPeriod_some (x.drop s) k hk hfp).2
    have hr := extendReach_work_span (x.drop s) p (x.length + 1) m
    have hstep : decomposeStepWork x k s =
        firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
        (extendReachWork (x.drop s) p (x.length + 1) m +
          secondOuterWork (x.drop s) k p (extendReach (x.drop s) p (x.length + 1) m)
            ((x.drop s).length + 1) 1 0) := by simp only [decomposeStepWork, hfp]
    rw [hstep] at hl1 ⊢
    have hkw := Nat.mul_le_mul_left k hw.1
    unfold decompBodyRate
    nlinarith only [hl1, hl3, hw.1, hkw, hP, hr.2, hm,
      Nat.zero_le (stripRate k), Nat.zero_le (stepRate k)]

/-- info: 'PalPeg.GSPreProg.DECOMP_BODY_continue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMP_BODY_continue
end PalPeg.GSPreProg
