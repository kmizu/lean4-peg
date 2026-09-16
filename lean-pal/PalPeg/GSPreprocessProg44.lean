import PalPeg.GSPreprocessProg43

/-! # Complete finite first-search loop and its work bound -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def foLimit (bounded : Bool) (bound n : ℕ) : ℕ := if bounded then bound else n

def foRate (k : ℕ) : ℕ := k + 40

theorem firstInner_le_work (v : List (Fin sc)) (k p fuel q : ℕ) :
    firstInner v k p fuel q ≤ q + firstInnerWork v k p fuel q := by
  induction fuel generalizing q with
  | zero => simp [firstInner, firstInnerWork]
  | succ fuel ih =>
    simp only [firstInner, firstInnerWork]
    split
    · have := ih (q + 1); omega
    · omega

theorem foGuard_limit_iff (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s p F S R A B : ℕ) (hk : 2 ≤ k) (hp : 0 < p)
    (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩
      ⟨foBound bounded bound p, A, B⟩ ts) :
    foGuard blank endSym mark bounded ts ↔
      p < (x.drop s).length ∧ p < foLimit bounded bound (x.drop s).length := by
  rw [foGuard_normal_iff hend hmark bounded bound k s p F S R A B hk hp ts he]
  cases bounded <;> simp [foLimit]

theorem FO_RUN_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s F S R A B : ℕ) (hk : 2 ≤ k) (hs : s ≤ x.length) :
    ∀ (fuel p : ℕ) (ts : Tapes sc), 0 < p →
    EncS blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩
      ⟨foBound bounded bound p, A, B⟩ ts → (x.drop s).length ≤ p + fuel →
    ∃ L u P Q,
      ExecA Terminal blank endSym mark (FO_RUN bounded k) (applyActs blank (sProbe blank) ts) L ∧
      applyActs blank L (applyActs blank (sProbe blank) ts) = applyActs blank (sProbe blank) u ∧
      EncS blank startSym endSym mark x (s + Q) (s + P + Q)
        ⟨(k - 1) * P - Q, Q, 0, P, F, S, R⟩ ⟨foBound bounded bound P, A, B⟩ u ∧
      0 < P ∧
      P ≤ p + firstOuterWork (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p ∧
      Q = (if (firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p).isSome
        then (k - 1) * P else 0) ∧
      (∀ p' m, firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p = some (p', m) →
        P = p' ∧ P + Q = m) ∧
      ¬ foGuard blank endSym mark bounded u ∧
      L.length ≤ foRate k * firstOuterWork (x.drop s) k
        (foLimit bounded bound (x.drop s).length) fuel p := by
  intro fuel
  induction fuel with
  | zero =>
    intro p ts hp he hbound
    have hstop : ¬ foGuard blank endSym mark bounded ts := by
      rw [foGuard_limit_iff hend hmark bounded bound k s p F S R A B hk hp ts he]
      omega
    refine ⟨[], ts, p, 0, FO_RUN_stop bounded k ts hstop, rfl, ?_, hp, ?_, ?_, ?_, hstop, ?_⟩
    · simpa only [Nat.add_zero, Nat.sub_zero] using he
    · simp [firstOuterWork]
    · simp [firstOuter]
    · intro p' m h; simp [firstOuter] at h
    · simp [firstOuterWork]
  | succ fuel ih =>
    intro p ts hp he hbound
    let lim := foLimit bounded bound (x.drop s).length
    have hgiff := foGuard_limit_iff hend hmark bounded bound k s p F S R A B hk hp ts he
    by_cases hg : p < (x.drop s).length ∧ p < lim
    · have hc : foGuard blank endSym mark bounded ts := hgiff.mpr hg
      have hsp : s + p < x.length := by
        have hh := hg.1
        rw [List.length_drop] at hh
        omega
      let q := firstInner (x.drop s) k p ((x.drop s).length + 1) 0
      let W := firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0
      obtain ⟨L1, hx1, he1, hc1⟩ := FIRST_BODY_spec (Terminal := Terminal)
        hend hmark k s p F S R (by omega) hs hsp ⟨foBound bounded bound p, A, B⟩ ts he
      have hc1' : L1.length ≤ (k + 30) * (1 + W) := hc1
      by_cases hm : q = (k - 1) * p
      · rw [if_pos hm] at he1
        have he1' : EncS blank startSym endSym mark x (s + (k - 1) * p)
            (s + p + (k - 1) * p) ⟨0, (k - 1) * p, 0, p, F, S, R⟩
            ⟨foBound bounded bound p, A, B⟩ (applyActs blank L1 ts) := by
          simpa only [← hm] using he1
        have hstop : ¬ foGuard blank endSym mark bounded (applyActs blank L1 ts) := by
          rw [foGuard_enc_iff hend hmark bounded he1']
          simp
        have hans : firstOuter (x.drop s) k lim (fuel + 1) p = some (p, p + (k - 1) * p) := by
          rw [firstOuter, if_pos hg, if_pos hm]
        have hw : firstOuterWork (x.drop s) k lim (fuel + 1) p = 1 + W := by
          rw [firstOuterWork, if_pos hg, if_pos hm]
          omega
        refine ⟨foIter blank ts L1 ++ [], applyActs blank L1 ts, p, (k - 1) * p,
          FO_RUN_cont bounded k ts he.ca he.base.cd hc hx1 (FO_RUN_stop bounded k _ hstop),
          ?_, ?_, hp, ?_, ?_, ?_, hstop, ?_⟩
        · rw [List.append_nil, foIter_effect ts he.ca he.base.cd]
        · simpa only [Nat.sub_self] using he1'
        · change p ≤ p + firstOuterWork (x.drop s) k lim (fuel + 1) p
          omega
        · change (k - 1) * p = if (firstOuter (x.drop s) k lim (fuel + 1) p).isSome then _ else _
          rw [hans]; rfl
        · intro p' m h
          rw [hans] at h
          have hh := Option.some.inj h
          exact ⟨(Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩
        · change (foIter blank ts L1 ++ []).length ≤ foRate k * firstOuterWork (x.drop s) k lim (fuel + 1) p
          rw [List.append_nil, foIter_length, hw]
          unfold foRate
          nlinarith
      · rw [if_neg hm] at he1
        let δ := shiftNoPeriod q k
        have hδ : 0 < δ := shiftNoPeriod_pos q k
        have hqW : q ≤ W := by
          have hh := firstInner_le_work (x.drop s) k p ((x.drop s).length + 1) 0
          simpa only [Nat.zero_add] using hh
        have hδW : δ ≤ 1 + W := by
          have hh := shiftNoPeriod_le_succ (show 0 < k by omega) q
          omega
        have heNext : EncS blank startSym endSym mark x s (s + (p + δ))
            ⟨(k - 1) * (p + δ), 0, 0, p + δ, F, S, R⟩
            ⟨foBound bounded bound (p + δ), A, B⟩ (applyActs blank L1 ts) := by
          simpa only [foBound_shift, Nat.add_assoc] using he1
        obtain ⟨L2, u, P, Q, hx2, hu, he2, hp2, hsize, hflag, hanswer, hstop, hc2⟩ :=
          ih (p + δ) (applyActs blank L1 ts) (by omega) heNext (by omega)
        have hans : firstOuter (x.drop s) k lim (fuel + 1) p =
            firstOuter (x.drop s) k lim fuel (p + δ) := by
          rw [firstOuter, if_pos hg, if_neg hm]
        have hw : firstOuterWork (x.drop s) k lim (fuel + 1) p =
            1 + W + firstOuterWork (x.drop s) k lim fuel (p + δ) := by
          rw [firstOuterWork, if_pos hg, if_neg hm]
        refine ⟨foIter blank ts L1 ++ L2, u, P, Q,
          FO_RUN_cont bounded k ts he.ca he.base.cd hc hx1 hx2, ?_, he2, hp2, ?_, ?_, ?_, hstop, ?_⟩
        · rw [applyActs_append, foIter_effect ts he.ca he.base.cd, hu]
        · change P ≤ p + firstOuterWork (x.drop s) k lim (fuel + 1) p
          rw [hw]
          dsimp only [lim, δ] at hsize hδW ⊢
          omega
        · change Q = if (firstOuter (x.drop s) k lim (fuel + 1) p).isSome then _ else _
          rw [hans]; exact hflag
        · intro p' m h
          rw [hans] at h
          exact hanswer p' m h
        · change (foIter blank ts L1 ++ L2).length ≤ foRate k * firstOuterWork (x.drop s) k lim (fuel + 1) p
          rw [List.length_append, foIter_length, hw]
          unfold foRate at *
          nlinarith
    · have hstop : ¬ foGuard blank endSym mark bounded ts := fun hh => hg (hgiff.mp hh)
      have hans : firstOuter (x.drop s) k lim (fuel + 1) p = none := by rw [firstOuter, if_neg hg]
      have hw : firstOuterWork (x.drop s) k lim (fuel + 1) p = 0 := by rw [firstOuterWork, if_neg hg]
      refine ⟨[], ts, p, 0, FO_RUN_stop bounded k ts hstop, rfl, ?_, hp, ?_, ?_, ?_, hstop, ?_⟩
      · simpa only [Nat.add_zero, Nat.sub_zero] using he
      · change p ≤ p + firstOuterWork (x.drop s) k lim (fuel + 1) p
        omega
      · change 0 = if (firstOuter (x.drop s) k lim (fuel + 1) p).isSome then _ else _
        rw [hans]; rfl
      · intro p' m h
        rw [hans] at h
        cases h
      · change 0 ≤ foRate k * firstOuterWork (x.drop s) k lim (fuel + 1) p
        omega

end PalPeg.GSPreProg
