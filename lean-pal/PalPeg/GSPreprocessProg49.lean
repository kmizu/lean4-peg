import PalPeg.GSPreprocessProg48

/-! # Success branch of the finite first phase -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def FIRST_PHASE (bounded : Bool) (k : ℕ) : Prog A9 Cond9 :=
  .seq (FIRST_SEARCH bounded k) (CD_CASE .skip LOAD_EXTEND)

theorem FIRST_PHASE_success (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s F S A B fuel p m : ℕ)
    (hk : 2 ≤ k) (hs : s < x.length) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, 0⟩
      ⟨foBound bounded bound 0, A, B⟩ ts)
    (hbound : (x.drop s).length ≤ 1 + fuel)
    (hans : firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1 = some (p, m)) :
    let r := extendReach (x.drop s) p (x.length + 1) m
    ∃ L, ExecA Terminal blank endSym mark (FIRST_PHASE bounded k) ts L ∧
      EncS blank startSym endSym mark x (s + (r - p)) (s + r)
        ⟨0, 0, 0, p, F, S, r⟩ ⟨foBound bounded bound p, A, B⟩ (applyActs blank L ts) ∧
      L.length ≤ (k - 1) + 16 + foRate k * firstOuterWork (x.drop s) k
        (foLimit bounded bound (x.drop s).length) fuel 1 + 3 * ((k - 1) * p) + 7 * p +
          3 * extendReachWork (x.drop s) p (x.length + 1) m := by
  dsimp only
  obtain ⟨L₁, P, Q, hx₁, he₁, hp, hsize, hflag, hanswer, _, hl₁⟩ :=
    FIRST_SEARCH_spec (Terminal := Terminal) hend hmark bounded bound k s F S 0 A B fuel
      hk hs ts he hbound
  obtain ⟨rfl, hm⟩ := hanswer p m hans
  have hq : Q = (k - 1) * P := by simpa only [hans, Option.isSome_some, if_true] using hflag
  have hd : (k - 1) * P - Q = 0 := by omega
  have he₁' := he₁
  rw [hd] at he₁'
  obtain ⟨L₂, hx₂, he₂, hl₂⟩ := LOAD_EXTEND_spec (Terminal := Terminal)
    hend hmark (x.length + 1) (s + Q) (s + P + Q) 0 P Q F S _ _ he₁'
      (by omega) (by omega)
  let t₁ := applyActs blank L₁ ts
  have hx₃ := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t₁ he₁'.base.cd
    .skip LOAD_EXTEND L₂ (by simpa using hx₂)
  have hr := cdCaseTest_restore t₁ he₁'.base.cd
  have hc := rSteps_extendReach (x := x) (p := P) (s := s) (by omega)
    (x.length + 1) Q (pat_le he₁'.base.v2)
  rw [hm] at hc
  have hfin : applyActs blank (L₁ ++ (cdCaseTest blank t₁ ++ L₂)) ts =
      applyActs blank L₂ t₁ := by
    rw [applyActs_append, applyActs_append]
    change applyActs blank L₂ (applyActs blank (cdCaseTest blank t₁) t₁) = _
    rw [hr]
  refine ⟨L₁ ++ (cdCaseTest blank t₁ ++ L₂), execA_seq hx₁ hx₃, ?_, ?_⟩
  · rw [hfin]
    have ha : s + Q + rSteps x (x.length + 1) (s + Q) (s + P + Q) =
        s + (extendReach (x.drop s) P (x.length + 1) m - P) := by omega
    have hb : s + P + Q + rSteps x (x.length + 1) (s + Q) (s + P + Q) =
        s + extendReach (x.drop s) P (x.length + 1) m := by omega
    have hc' : Q + P + rSteps x (x.length + 1) (s + Q) (s + P + Q) =
        extendReach (x.drop s) P (x.length + 1) m := by omega
    simpa only [ha, hb, hc'] using he₂
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    rw [hc.2, hq] at hl₂
    omega

theorem FIRST_PHASE_failure (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s F S A B fuel : ℕ)
    (hk : 2 ≤ k) (hs : s < x.length) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, 0⟩
      ⟨foBound bounded bound 0, A, B⟩ ts)
    (hbound : (x.drop s).length ≤ 1 + fuel)
    (hans : firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1 = none) :
    ∃ L P, ExecA Terminal blank endSym mark (FIRST_PHASE bounded k) ts L ∧
      EncS blank startSym endSym mark x s (s + P)
        ⟨(k - 1) * P, 0, 0, P, F, S, 0⟩ ⟨foBound bounded bound P, A, B⟩
        (applyActs blank L ts) ∧
      0 < P ∧ s + P ≤ x.length ∧
      P ≤ 1 + firstOuterWork (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1 ∧
      ¬ foGuard blank endSym mark bounded (applyActs blank L ts) ∧
      L.length ≤ (k - 1) + 10 + foRate k * firstOuterWork (x.drop s) k
        (foLimit bounded bound (x.drop s).length) fuel 1 := by
  obtain ⟨L₁, P, Q, hx₁, he₁, hp, hsize, hflag, _, hstop, hl₁⟩ :=
    FIRST_SEARCH_spec (Terminal := Terminal) hend hmark bounded bound k s F S 0 A B fuel
      hk hs ts he hbound
  have hq : Q = 0 := by
    rw [hans] at hflag
    simpa using hflag
  clear hflag
  subst Q
  simp only [Nat.add_zero, Nat.sub_zero] at he₁
  have hd : (k - 1) * P ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by omega) hp)
  let t₁ := applyActs blank L₁ ts
  have hx₂ := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark t₁ he₁.base.cd
    .skip LOAD_EXTEND [] (by rw [if_neg hd]; exact execA_skip)
  have hr := cdCaseTest_restore t₁ he₁.base.cd
  have hf : applyActs blank (L₁ ++ (cdCaseTest blank t₁ ++ [])) ts = t₁ := by
    simp only [List.append_nil, applyActs_append]
    exact hr
  refine ⟨L₁ ++ (cdCaseTest blank t₁ ++ []), P, execA_seq hx₁ hx₂, ?_, hp,
    pat_le he₁.base.v2, hsize, ?_, ?_⟩
  · rw [hf]; exact he₁
  · rw [hf]; exact hstop
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.FIRST_PHASE_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_PHASE_failure

/-- info: 'PalPeg.GSPreProg.FIRST_PHASE_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_PHASE_success

end PalPeg.GSPreProg
