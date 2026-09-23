import PalPeg.ScaMatcherLoop
import PalPeg.GSDrained

/-!
# The matcher's main loop, one segment at a time

`seg` unifies the loop-head cases of `ScaMatcherLoop`: from a loop head encoding the verifier
state `z` with the next letter arrived, the guarded head VM reaches the loop head of `vStep^[d] z`
(`d = 1` for a hit that does not complete `v` and for a mismatch, `d = 2` for a hit that completes
`v`: the report, then the shift). The step count is paid by the potential
`Φ = (k+1)·pos + q` (`GSScan.Phi`): `n + 35·Φ(z) ≤ 35·Φ(z')` for `k ≤ 8`. The output grows exactly
when `vStep z` carries a `match` event (`GSDrained.matchEvent`), by the end of the occurrence, and
then the run passes the `match` state within 11 steps with `B` on that end.
-/
set_option autoImplicit false
namespace PalPeg.ScaMatcherRun
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe PalPeg.ScaMatcherLoop

variable {ρ : String → Bool}

/-- A shift moves by at least one cell and gives back at most `k` cells per cell moved. -/
theorem shift_facts {k p₁ r q : ℕ} (hk : 1 ≤ k) (hper : k * p₁ ≤ q ∧ q ≤ r → 1 ≤ p₁) :
    1 ≤ PalPeg.gsShift k p₁ r q ∧ q ≤ PalPeg.gsNextQ k p₁ r q + k * PalPeg.gsShift k p₁ r q ∧
      PalPeg.gsNextQ k p₁ r q ≤ q := by
  unfold PalPeg.gsShift PalPeg.gsNextQ
  split_ifs with hc
  · have hp := hper hc
    have : p₁ ≤ k * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
    refine ⟨hp, ?_, by omega⟩
    omega
  · have hb := (PalPeg.ceilDiv_bounds (q := q) (k := k) (by omega)).1
    refine ⟨le_max_left _ _, ?_, by omega⟩
    have : k * PalPeg.ceilDiv q k ≤ k * max 1 (PalPeg.ceilDiv q k) :=
      Nat.mul_le_mul_left _ (le_max_right _ _)
    omega

/-- The verifier step, as the loop sees it. -/
abbrev VS (x T : List (Fin 2)) (k s p₁ r : ℕ) : PalPeg.VState → PalPeg.VState :=
  PalPeg.vStep (x.take s) (x.drop s) k p₁ r T

/-- **One segment of the main loop.** -/
theorem seg (hρ : Orient ρ) (x T : List (Fin 2)) (m k s p₁ r : ℕ) (hk : 2 ≤ k) (hk8 : k ≤ 8)
    (pe ok : Bool) (z : PalPeg.VState) (v : HVM) (h : AtHead x T m k s p₁ r pe ok z v)
    (hen : z.1.pos + z.1.q < m)
    (hdl : PalPeg.GSReportDeadline.DeadlineInv (x.take s) (x.drop s) T z)
    (hps : v.patternSize = x.length)
    (hnoper : pe = false → x.length - s < k * p₁) (hp1 : pe = true → 1 ≤ p₁) :
    ∃ d n v' ok', 1 ≤ d ∧ d ≤ 2 ∧
      n + 35 * PalPeg.Phi k z.1 ≤ 35 * PalPeg.Phi k ((VS x T k s p₁ r)^[d] z).1 ∧
      PalPeg.Phi k z.1 < PalPeg.Phi k ((VS x T k s p₁ r)^[d] z).1 ∧
      iterS x.length ρ n v = some v' ∧ AtHead x T m k s p₁ r pe ok' ((VS x T k s p₁ r)^[d] z) v' ∧
      v'.outputs = v.outputs ++
        (if PalPeg.GSDrained.matchEvent (x.take s) (x.drop s) (VS x T k s p₁ r z) = true
          then [(((VS x T k s p₁ r z).1.pos + (x.length - s) : ℕ) : ℤ)] else []) ∧
      (PalPeg.GSDrained.matchEvent (x.take s) (x.drop s) (VS x T k s p₁ r z) = true →
        ∃ n₁ u, n₁ ≤ 11 ∧ n₁ < n ∧ iterS x.length ρ n₁ v = some u ∧ u.outputs = v.outputs ∧
          (∃ c, u.ctl = .pending c (.«match» "B")) ∧
          u.pos "B" = x.length + (VS x T k s p₁ r z).1.pos + (x.length - s)) ∧
      (d = 2 → (VS x T k s p₁ r z).1.q = x.length - s) := by
  obtain ⟨⟨pos, q⟩, c⟩ := z
  simp only at hen
  have hqv : q < x.length - s := h.qv
  have hsx := h.sx
  have hut : (x.take s).length = s := by simp [List.length_take]; omega
  have hvl : (x.drop s).length = x.length - s := by simp
  have hper : ∀ q', q' ≤ x.length - s → k * p₁ ≤ q' ∧ q' ≤ r → 1 ≤ p₁ := by
    intro q' hq' hc
    cases pe with
    | true => exact hp1 rfl
    | false => have := hnoper rfl; omega
  by_cases hhit : T[pos + q]? = (x.drop s)[q]?
  · have hvs1 : VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c) =
        (⟨pos, q + 1⟩, PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c)) := by
      have hq : q ≠ (x.drop s).length := by rw [hvl]; omega
      simp only [VS, PalPeg.vStep, PalPeg.scanStep, hq, if_false, hhit, if_true]
    by_cases hmore : q + 1 < x.length - s
    · obtain ⟨n, ok', v', hn, hrun, hout, hat⟩ :=
        step_hit x T m k s p₁ r pe ok _ v hρ h hen hhit hmore
      have hme : PalPeg.GSDrained.matchEvent (x.take s) (x.drop s)
          (VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c)) = false := by
        rw [hvs1]; simp [PalPeg.GSDrained.matchEvent, hvl]; omega
      refine ⟨1, n, v', ok', le_rfl, by norm_num, ?_, ?_, hrun, hat, ?_, fun h' => absurd h' (by simp [hme]),
        fun h => absurd h (by norm_num)⟩
      · show n + 35 * PalPeg.Phi k ⟨pos, q⟩ ≤ 35 * PalPeg.Phi k (VS x T k s p₁ r _).1
        rw [hvs1]; simp only [PalPeg.Phi]; omega
      · show PalPeg.Phi k ⟨pos, q⟩ < PalPeg.Phi k (VS x T k s p₁ r _).1
        rw [hvs1]; simp only [PalPeg.Phi]; omega
      · rw [hout, hme]; simp
    · have hlast : q + 1 = x.length - s := by omega
      obtain ⟨n, v', hn, hrun, hout, hmatch, hat⟩ :=
        step_report x T m k s p₁ r hk pe ok _ v hρ h hen hhit hlast hdl hps hnoper hp1
      have hme : PalPeg.GSDrained.matchEvent (x.take s) (x.drop s)
          (VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c)) =
          decide ((PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c)).2 = s) := by
        show PalPeg.GSDrained.matchEvent _ _ (PalPeg.vStep _ _ k p₁ r T _) = _
        rw [show PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c) =
          VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c) from rfl, hvs1]
        simp [PalPeg.GSDrained.matchEvent, hvl, hut, hlast]
      obtain ⟨hs1, hs2, hs3⟩ := shift_facts (k := k) (p₁ := p₁) (r := r) (q := x.length - s)
        (by omega) (hper _ le_rfl)
      have hvs2 : (VS x T k s p₁ r (VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c))).1 =
          ⟨pos + PalPeg.gsShift k p₁ r (x.length - s), PalPeg.gsNextQ k p₁ r (x.length - s)⟩ := by
        rw [hvs1]
        simp only [VS, PalPeg.vStep_fst, PalPeg.scanStep, hvl, ← hlast, if_true]
      refine ⟨2, n, v', true, by norm_num, le_rfl, ?_, ?_, hrun, hat, ?_, ?_, fun _ => by rw [hvs1]; exact hlast⟩
      · show n + 35 * PalPeg.Phi k ⟨pos, q⟩ ≤
          35 * PalPeg.Phi k (VS x T k s p₁ r (VS x T k s p₁ r _)).1
        rw [hvs2]; simp only [PalPeg.Phi]
        set sh := PalPeg.gsShift k p₁ r (x.length - s)
        set nq := PalPeg.gsNextQ k p₁ r (x.length - s)
        have hS : k * sh ≤ 8 * sh := Nat.mul_le_mul_right _ hk8
        rw [show (k + 1) * (pos + sh) = (k + 1) * pos + k * sh + sh by ring]
        omega
      · show PalPeg.Phi k ⟨pos, q⟩ < PalPeg.Phi k (VS x T k s p₁ r (VS x T k s p₁ r _)).1
        rw [hvs2]; simp only [PalPeg.Phi]
        rw [show (k + 1) * (pos + PalPeg.gsShift k p₁ r (x.length - s)) =
          (k + 1) * pos + k * PalPeg.gsShift k p₁ r (x.length - s) +
            PalPeg.gsShift k p₁ r (x.length - s) by ring]
        omega
      · rw [hout, hme]
        by_cases hc : (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c)).2 = s
        · rw [if_pos hc, decide_eq_true hc, if_pos rfl, hvs1]
        · rw [if_neg hc, decide_eq_false hc]; simp
      · intro hm
        rw [hme] at hm
        obtain ⟨n₁, u, hn₁, hlt, hr₁, ho₁, hc₁, hB₁⟩ := hmatch (of_decide_eq_true hm)
        refine ⟨n₁, u, hn₁, hlt, hr₁, ho₁, hc₁, ?_⟩
        rw [hB₁, hvs1]
  · -- a mismatch
    obtain ⟨n, v', hn, hrun, hout, hat⟩ :=
      step_miss x T m k s p₁ r (by omega) pe ok _ v hρ h hen hhit hnoper
    have hvs1 : VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c) =
        (⟨pos + PalPeg.gsShift k p₁ r q, PalPeg.gsNextQ k p₁ r q⟩, 0) := by
      have hq : q ≠ (x.drop s).length := by rw [hvl]; omega
      simp only [VS, PalPeg.vStep, PalPeg.scanStep, hq, if_false, hhit]
    obtain ⟨hs1, hs2, hs3⟩ := shift_facts (k := k) (p₁ := p₁) (r := r) (q := q) (by omega)
      (hper _ (by omega))
    have hme : PalPeg.GSDrained.matchEvent (x.take s) (x.drop s)
        (VS x T k s p₁ r ((⟨pos, q⟩ : PalPeg.ScanState), c)) = false := by
      rw [hvs1]; simp [PalPeg.GSDrained.matchEvent, hvl]; omega
    refine ⟨1, n, v', true, le_rfl, by norm_num, ?_, ?_, hrun, hat, ?_,
      fun h' => absurd h' (by simp [hme]), fun h => absurd h (by norm_num)⟩
    · show n + 35 * PalPeg.Phi k ⟨pos, q⟩ ≤ 35 * PalPeg.Phi k (VS x T k s p₁ r _).1
      rw [hvs1]; simp only [PalPeg.Phi]
      set sh := PalPeg.gsShift k p₁ r q
      set nq := PalPeg.gsNextQ k p₁ r q
      have hS : k * sh ≤ 8 * sh := Nat.mul_le_mul_right _ hk8
      rw [show (k + 1) * (pos + sh) = (k + 1) * pos + k * sh + sh by ring]
      simp only at hn
      omega
    · show PalPeg.Phi k ⟨pos, q⟩ < PalPeg.Phi k (VS x T k s p₁ r _).1
      rw [hvs1]; simp only [PalPeg.Phi]
      rw [show (k + 1) * (pos + PalPeg.gsShift k p₁ r q) =
        (k + 1) * pos + k * PalPeg.gsShift k p₁ r q + PalPeg.gsShift k p₁ r q by ring]
      omega
    · rw [hout, hme]; simp

end PalPeg.ScaMatcherRun
