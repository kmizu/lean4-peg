import PalPeg.PassSum3

/-!
# 1 パスの周期和：UP ステップへの還元（PassSum5）

`stripLoop2Periods` の 1 パスの総和 `Σⱼ pⱼ` を、**UP ステップで飛び上がった周期の総和**
だけで抑える無条件の不等式を与える。

`PassSum` の `step_dichotomy` により、連続する 2 反復の周期は

* DOWN：`(k-1) * pⱼ₊₁ < pⱼ`（次の窓が今の周期領域に収まる）、または
* UP  ：`(k-1) * pⱼ ≤ pⱼ₊₁`（収まらない）

のいずれかであった。DOWN だけなら等比級数で `Σ pⱼ ≤ (k-1)/(k-2) * p₀` になる。
本ファイルはこれを **UP を許した形に一般化**する：

`stripLoop2UpPeriods`（UP ステップで到達した周期 `pⱼ₊₁` だけを足すカウンタ）に対し

```
(k-2) * stripLoop2Periods x k b fuel s ≤ (k-1) * (p₀ + stripLoop2UpPeriods x k b fuel s)
```

が**無条件**（`4 ≤ k` のみ）に成り立つ（`passPeriods_le_up`）。
したがって未解決の `PassSumLinear`（= `EndToEnd2.PassPeriodSum`）は

> **1 パスの UP ステップで到達した周期の総和が `bound` に線形**

に完全に帰着する（`passSumLinear_of_upSum`）。とくに UP ステップが 1 つも無いパス
（`AllDown`）については `k = 8` で `C₁ = 2` の線形上界が **sorry なしで従う**
（`passSumLinear_of_allDown_eight`）。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## §0 次の走査位置 -/

/-- 1 反復ぶんの前進後の絶対位置（`stripLoop2` の前進規則）。 -/
abbrev nextPos (x : List α) (k : ℕ) (s p : ℕ) : ℕ :=
  s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)

/-- 走査位置は `x.length` を超えない。 -/
theorem nextPos_le (x : List α) (k bound : ℕ) (hk : 3 ≤ k) {s p m : ℕ}
    (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m)) :
    nextPos x k s p ≤ x.length := by
  obtain ⟨hleast, -, hkr, hR⟩ := stripLoop2_step_data x k bound hk hs hfo
  have hvlen : (x.drop s).length = x.length - s := by simp
  have hrle : extendReach (x.drop s) p (x.length + 1) (k * p) ≤ x.length - s := by
    have := hR.1; omega
  have hp : 0 < p := hleast.1.1
  have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
  simp only [nextPos]
  omega

/-! ## §1 `firstOuter` が失敗する位置では総和は 0 -/

theorem stripLoop2Periods_of_none (x : List α) (k bound : ℕ) {s : ℕ}
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = none) :
    ∀ fuel, stripLoop2Periods x k bound fuel s = 0 := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => rw [stripLoop2Periods, hfo]

/-! ## §2 UP ステップの周期カウンタ -/

/-- 1 パスのうち **UP ステップ**（`(k-1) * pⱼ ≤ pⱼ₊₁`）で到達した周期 `pⱼ₊₁` の総和。 -/
def stripLoop2UpPeriods (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          (match firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
            | none => 0
            | some (q, _) => if (k - 1) * p ≤ q then q else 0)
          + stripLoop2UpPeriods x k bound fuel (nextPos x k s p)

/-! ## §3 主定理：DOWN の等比級数と UP の分離 -/

/-- **無条件の主不等式**。1 パスの周期和は「最初の周期」と「UP で到達した周期の総和」
だけで抑えられる：`(k-2) * Σ pⱼ ≤ (k-1) * (p₀ + Σ_UP pⱼ)`。

DOWN ステップは `(k-1) * pⱼ₊₁ < pⱼ` なので等比級数として吸収され、UP ステップだけが
右辺に残る。 -/
theorem passPeriods_le_up (x : List α) (k bound : ℕ) (hk : 4 ≤ k) :
    ∀ (fuel s p m : ℕ), s ≤ x.length →
      firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m) →
      (k - 2) * stripLoop2Periods x k bound fuel s
        ≤ (k - 1) * (p + stripLoop2UpPeriods x k bound fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s p m _ _; simp [stripLoop2Periods, stripLoop2UpPeriods]
  | succ fuel ih =>
    intro s p m hs hfo
    have hp : 0 < p := (stripLoop2_step_data x k bound (by omega) hs hfo).1.1.1
    have hs'le : nextPos x k s p ≤ x.length := nextPos_le x k bound (by omega) hs hfo
    rw [stripLoop2Periods, stripLoop2UpPeriods, hfo]
    simp only []
    rcases hfo' : firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
      _ | ⟨q, m'⟩
    · simp only []
      have hz : stripLoop2Periods x k bound fuel (nextPos x k s p) = 0 :=
        stripLoop2Periods_of_none x k bound hfo' fuel
      rw [hz]
      have hmul : (k - 2) * p ≤ (k - 1) * p := Nat.mul_le_mul_right p (by omega)
      have e1 : (k - 2) * (p + 0) = (k - 2) * p := by ring
      have e2 : (k - 1) * (p + (0 + stripLoop2UpPeriods x k bound fuel (nextPos x k s p)))
          = (k - 1) * p
            + (k - 1) * stripLoop2UpPeriods x k bound fuel (nextPos x k s p) := by ring
      omega
    · simp only []
      have hrec := ih (nextPos x k s p) q m' hs'le hfo'
      set P' := stripLoop2Periods x k bound fuel (nextPos x k s p) with hP'
      set U' := stripLoop2UpPeriods x k bound fuel (nextPos x k s p) with hU'
      have e1 : (k - 2) * (p + P') = (k - 2) * p + (k - 2) * P' := by ring
      have e3 : (k - 1) * (q + U') = (k - 1) * q + (k - 1) * U' := by ring
      have hmul : (k - 2) * p ≤ (k - 1) * p := Nat.mul_le_mul_right p (by omega)
      by_cases hup : (k - 1) * p ≤ q
      · rw [if_pos hup]
        have e2 : (k - 1) * (p + (q + U'))
            = (k - 1) * p + (k - 1) * q + (k - 1) * U' := by ring
        omega
      · rw [if_neg hup]
        have hdi := stripLoop2_step_dichotomy x k bound hk hs hfo hfo'
        have hdown : (k - 1) * q < p := by
          rcases hdi with h | h
          · exact h
          · exact absurd h hup
        have hk2 : (k - 1) * p = (k - 2) * p + p := by
          have h : k - 1 = (k - 2) + 1 := by omega
          rw [h]; ring
        have e2 : (k - 1) * (p + (0 + U')) = (k - 1) * p + (k - 1) * U' := by ring
        omega

/-- 系：`firstOuter` が `p` を返す位置からの周期和の陽な上界。 -/
theorem passPeriods_le_up' (x : List α) (k bound : ℕ) (hk : 4 ≤ k) {fuel s p m : ℕ}
    (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m)) :
    (k - 2) * stripLoop2Periods x k bound fuel s
      ≤ (k - 1) * (bound + stripLoop2UpPeriods x k bound fuel s) := by
  have hlt := firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo
  have h := passPeriods_le_up x k bound hk fuel s p m hs hfo
  have hmono : (k - 1) * (p + stripLoop2UpPeriods x k bound fuel s)
      ≤ (k - 1) * (bound + stripLoop2UpPeriods x k bound fuel s) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## §4 `PassSumLinear` への還元 -/

/-- **UP 周期和が線形なら `PassSumLinear`**。残る課題は `hUp` ただ一つになる。 -/
theorem passSumLinear_of_upSum (x : List α) (k C : ℕ) (hk : 4 ≤ k)
    (hUp : ∀ b s : ℕ, stripLoop2UpPeriods x k b (x.length + 1) s ≤ C * b) :
    PassSumLinear x k ((k - 1) * (C + 1)) := by
  intro b s
  by_cases hs : s ≤ x.length
  · rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [stripLoop2Periods_of_none x k b hfo]; exact Nat.zero_le _
    · have h := passPeriods_le_up' x k b hk (fuel := x.length + 1) hs hfo
      have hu := hUp b s
      have hmono : (k - 1) * (b + stripLoop2UpPeriods x k b (x.length + 1) s)
          ≤ (k - 1) * (b + C * b) := Nat.mul_le_mul_left _ (by omega)
      have e : (k - 1) * (b + C * b) = ((k - 1) * (C + 1)) * b := by ring
      have hk2 : 1 ≤ k - 2 := by omega
      have hmul : stripLoop2Periods x k b (x.length + 1) s
          ≤ (k - 2) * stripLoop2Periods x k b (x.length + 1) s :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  · have hnil : x.drop s = ([] : List α) := by
      apply List.drop_eq_nil_of_le; omega
    have hfo : firstOuter (x.drop s) k b (x.length + 1) 1 = none := by
      rw [hnil]
      cases (x.length + 1) with
      | zero => rfl
      | succ f => rw [firstOuter]; simp
    rw [stripLoop2Periods_of_none x k b hfo]; exact Nat.zero_le _

/-! ## §5 UP ステップの無いパス -/

/-- 1 パスに UP ステップが現れない（すべての隣接ステップが DOWN）。 -/
def AllDown (x : List α) (k bound : ℕ) : Prop :=
  ∀ (s p m q m' : ℕ), s ≤ x.length →
    firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m) →
    firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 = some (q, m') →
    (k - 1) * q < p

/-- `AllDown` なら UP カウンタは 0。 -/
theorem stripLoop2UpPeriods_eq_zero_of_allDown (x : List α) (k bound : ℕ) (hk : 4 ≤ k)
    (h : AllDown x k bound) :
    ∀ (fuel s : ℕ), s ≤ x.length → stripLoop2UpPeriods x k bound fuel s = 0 := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ fuel ih =>
    intro s hs
    rw [stripLoop2UpPeriods]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · rfl
    · simp only []
      have hp : 0 < p := (stripLoop2_step_data x k bound (by omega) hs hfo).1.1.1
      have hs'le : nextPos x k s p ≤ x.length := nextPos_le x k bound (by omega) hs hfo
      have hrest := ih (nextPos x k s p) hs'le
      rcases hfo' : firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
        _ | ⟨q, m'⟩
      · simp only []; omega
      · simp only []
        have hq : 0 < q :=
          (stripLoop2_step_data x k bound (by omega) hs'le hfo').1.1.1
        have hdown := h s p m q m' hs hfo hfo'
        have hnot : ¬ (k - 1) * p ≤ q := by
          intro hcon
          have h1 : (k - 1) * ((k - 1) * p) ≤ (k - 1) * q := Nat.mul_le_mul_left _ hcon
          have h2 : (k - 1) * ((k - 1) * p) = ((k - 1) * (k - 1)) * p := by ring
          have hsq : 3 * 1 ≤ (k - 1) * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
          have h3 : 3 * p ≤ ((k - 1) * (k - 1)) * p := Nat.mul_le_mul_right p (by omega)
          omega
        rw [if_neg hnot]
        omega

/-- **UP の無いパスに対する `PassSumLinear`（`k = 8`, `C₁ = 2`）**。

`(k-2) * Σ ≤ (k-1) * p₀ < (k-1) * bound` なので `6 * Σ ≤ 7 * bound ≤ 12 * bound`。 -/
theorem passSumLinear_of_allDown_eight (x : List α)
    (h : ∀ b : ℕ, AllDown x 8 b) : PassSumLinear x 8 2 := by
  intro b s
  by_cases hs : s ≤ x.length
  · rcases hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [stripLoop2Periods_of_none x 8 b hfo]; exact Nat.zero_le _
    · have hz : stripLoop2UpPeriods x 8 b (x.length + 1) s = 0 :=
        stripLoop2UpPeriods_eq_zero_of_allDown x 8 b (by omega) (h b) (x.length + 1) s hs
      have hmain := passPeriods_le_up' x 8 b (by omega) (fuel := x.length + 1) hs hfo
      rw [hz] at hmain
      simp only [Nat.add_zero] at hmain
      omega
  · have hnil : x.drop s = ([] : List α) := by
      apply List.drop_eq_nil_of_le; omega
    have hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 = none := by
      rw [hnil]
      cases (x.length + 1) with
      | zero => rfl
      | succ f => rw [firstOuter]; simp
    rw [stripLoop2Periods_of_none x 8 b hfo]; exact Nat.zero_le _

end PalPeg
