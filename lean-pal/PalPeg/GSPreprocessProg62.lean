import PalPeg.GSPreprocessProg61

/-! # Boundary facts for the finite stripping loop -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

theorem stripLoop2_at_end {α : Type} [DecidableEq α] (x : List α)
    (k F fuel : ℕ) : stripLoop2 x k F fuel x.length = x.length := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [stripLoop2, firstOuter]

theorem stripLoop2Work_at_end {α : Type} [DecidableEq α] (x : List α)
    (k F fuel : ℕ) : stripLoop2Work x k F fuel x.length = 0 := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [stripLoop2Work, firstOuter, firstOuterWork]

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem STRIP_RUN_ready_enc (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s F : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts) :
    probe blank ts.Ce = mark ∧ soCond blank endSym mark ts := by
  apply (soReady_iff ts).mp
  apply (soReady_enc_iff hend hmark (s := s) (p := 0) (q := 0) (E := 0) (by omega)
    (by simpa using he)).mpr
  constructor
  · rfl
  · simpa only [List.length_drop] using Nat.sub_pos_of_lt hs

/-- info: 'PalPeg.GSPreProg.STRIP_RUN_ready_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_RUN_ready_enc

theorem STRIP_RUN_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k F : ℕ) (hk : 3 ≤ k) (fuel : ℕ) {s : ℕ} {ts : Tapes sc}
    (hs : s ≤ x.length) (hf : x.length ≤ s + fuel)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts) :
    let t := stripLoop2 x k F fuel s
    let W := stripLoop2Work x k F fuel s
    ∃ L u P E, ExecA Terminal blank endSym mark (STRIP_RUN k)
        (applyActs blank (soProbe blank) ts) L ∧
      applyActs blank L (applyActs blank (soProbe blank) ts) =
        applyActs blank (soProbe blank) u ∧
      EncS blank startSym endSym mark x t (t + P)
        ⟨(k - 1) * P, 0, E, P, F, t, 0⟩ ⟨F - P, 0, 0⟩ u ∧
      t + P ≤ x.length ∧ E ≤ 1 ∧ (E ≠ 0 ∨ t + P = x.length) ∧
      P ≤ 1 + W ∧ L.length ≤ (stripRate k + 6) * W + k + 19 := by
  induction fuel generalizing s ts with
  | zero =>
    have hs' : s = x.length := by omega
    subst s
    refine ⟨[], ts, 0, 0, ?_, rfl, ?_, by simp [stripLoop2], by omega, ?_, by simp [stripLoop2Work], ?_⟩
    · exact STRIP_RUN_stop_enc hend hmark k (s := x.length) (P := 0) (by omega) (by simpa using he) (Or.inr (by omega))
    · simpa [stripLoop2] using he
    · exact Or.inr (by simp [stripLoop2])
    · simp [stripLoop2Work]
  | succ fuel ih =>
    by_cases hs' : s = x.length
    · subst s
      refine ⟨[], ts, 0, 0, ?_, rfl, ?_, ?_, by omega, ?_, ?_, ?_⟩
      · exact STRIP_RUN_stop_enc hend hmark k (s := x.length) (P := 0) (by omega) (by simpa using he) (Or.inr (by omega))
      · simpa only [stripLoop2_at_end, Nat.add_zero, Nat.mul_zero, Nat.sub_zero] using he
      · simp only [stripLoop2_at_end, Nat.add_zero, le_refl]
      · exact Or.inr (by simp only [stripLoop2_at_end, Nat.add_zero])
      · simp only [stripLoop2Work_at_end]; omega
      · simp only [stripLoop2Work_at_end, Nat.mul_zero, List.length_nil]; omega
    · have hslt : s < x.length := by omega
      have hc := STRIP_RUN_ready_enc hend hmark hslt he
      cases hfp : firstOuter (x.drop s) k F (x.length + 1) 1 with
      | none =>
        obtain ⟨L, P, hx, hu, hp, hfit, hsize, hl⟩ :=
          STRIP_FLAG_STEP_failure (Terminal := Terminal) hend hmark k hk hslt he hfp
        have hn := STRIP_RUN_stop_enc (Terminal := Terminal) hend hmark k hfit hu (Or.inl (by omega))
        have hx' := STRIP_RUN_cont k ts he.base.cq he.base.ce hc hx hn
        refine ⟨soIter blank ts L, applyActs blank L ts, P, 1, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
        · simpa only [List.append_nil] using hx'
        · exact soIter_effect ts he.base.cq he.base.ce L
        · simpa only [stripLoop2, hfp] using hu
        · simpa only [stripLoop2, hfp] using hfit
        · exact Or.inl (by omega)
        · simpa only [stripLoop2Work, hfp, Nat.add_zero] using hsize
        · rw [soIter_length]
          simp only [stripLoop2Work, hfp, Nat.add_zero]
          have hr : foRate k ≤ stripRate k + 6 := by unfold stripRate; omega
          have hm := Nat.mul_le_mul_right (firstOuterWork (x.drop s) k F (x.length + 1) 1) hr
          omega
      | some pm =>
        rcases pm with ⟨p, m⟩
        obtain ⟨L, hx, hu, hlt, hle, hl⟩ :=
          STRIP_FLAG_STEP_success (Terminal := Terminal) hend hmark k hk hslt he hfp
        obtain ⟨T, u, P, E, ht, heff, henc, hfit, hE, hstop, hP, hlen⟩ :=
          ih hle (by omega) hu
        have hx' := STRIP_RUN_cont k ts he.base.cq he.base.ce hc hx ht
        refine ⟨soIter blank ts L ++ T, u, P, E, hx', ?_, ?_, ?_, hE, ?_, ?_, ?_⟩
        · rw [applyActs_append, soIter_effect ts he.base.cq he.base.ce L]
          exact heff
        · simpa only [stripLoop2, hfp] using henc
        · simpa only [stripLoop2, hfp] using hfit
        · simpa only [stripLoop2, hfp] using hstop
        · simp only [stripLoop2Work, hfp]
          exact hP.trans (Nat.add_le_add_left
            ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)) 1)
        · rw [List.length_append, soIter_length]
          simp only [stripLoop2Work, hfp]
          have hw := firstOuterWork_pos (x.drop s) k F (x.length + 1) 1 p m hfp
          nlinarith only [hl, hlen, hw]

/-- info: 'PalPeg.GSPreProg.STRIP_RUN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_RUN_spec

theorem STRIP_CORE_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k F : ℕ) (hk : 3 ≤ k) (fuel : ℕ) {s : ℕ} {ts : Tapes sc}
    (hs : s ≤ x.length) (hf : x.length ≤ s + fuel)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts) :
    let t := stripLoop2 x k F fuel s
    let W := stripLoop2Work x k F fuel s
    ∃ L P E, ExecA Terminal blank endSym mark (STRIP_CORE k) ts L ∧
      EncS blank startSym endSym mark x t (t + P)
        ⟨(k - 1) * P, 0, E, P, F, t, 0⟩ ⟨F - P, 0, 0⟩ (applyActs blank L ts) ∧
      t + P ≤ x.length ∧ E ≤ 1 ∧ (E ≠ 0 ∨ t + P = x.length) ∧
      P ≤ 1 + W ∧ L.length ≤ (stripRate k + 6) * W + k + 23 := by
  obtain ⟨L, u, P, E, hx, hu, henc, hfit, hE, hstop, hP, hlen⟩ :=
    STRIP_RUN_spec (Terminal := Terminal) hend hmark k F hk fuel hs hf he
  obtain ⟨T, ht, heff, hcost⟩ := STRIP_CORE_finish k ts u henc.base.cq henc.base.ce L hx hu
  refine ⟨T, P, E, ht, ?_, hfit, hE, hstop, hP, ?_⟩
  · rw [heff]; exact henc
  · omega

/-- info: 'PalPeg.GSPreProg.STRIP_CORE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_CORE_spec
end PalPeg.GSPreProg
