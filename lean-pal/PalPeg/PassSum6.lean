import PalPeg.PassSum5
import PalPeg.EndToEnd2

/-!
# 1 パスの周期和：UP ステップの**本数**への還元（PassSum6）

`PassSum5` は未解決の `PassSumLinear`（= `EndToEnd2.PassPeriodSum`）を

> 1 パスの **UP ステップで到達した周期の総和** `stripLoop2UpPeriods` が `bound` に線形

へ還元した（`passSumLinear_of_upSum`）。本ファイルはこれをさらに

> 1 パスの **UP ステップの本数** `stripLoop2UpCount` が**絶対定数**で抑えられる

へ還元する（`passSumLinear_of_upCount`）。`firstOuter` が返す周期は常に `< bound`
なので、UP で到達した周期はどれも `< bound`。したがって

```
stripLoop2UpPeriods ≤ bound * stripLoop2UpCount
```

が無条件に成り立つ（`upPeriods_le_bound_mul_upCount`）。

数値実験（`k = 4, 8`、長さ 23 までの全二値文字列の網羅と、周期ブロックを連結した
構造化ランダム文字列 数百万本）では **1 パスの反復回数そのものが 3 以下**であり、
したがって UP ステップは高々 2 本であった。残る課題はこの
「UP ステップ本数の絶対定数上界」ただ一つになる。

さらに `PassSum5` の `AllDown`（UP が 1 本も無いパス）に対応する双対として、
**すべてのステップが UP のパス**（`AllUp`）についても `k = 8`, `C₁ = 2` の線形上界を
sorry なしで与える（`passSumLinear_of_allUp_eight`）。こちらは
「周期が `(k-1)` 倍ずつ増え、かつ常に `< bound`」という等比級数を
`(k-2) * Σⱼ pⱼ + p₀ ≤ (k-1) * bound` という**前向きに帰納できる不変条件**で表現して
証明する。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## §1 すべてのステップが UP のパス -/

/-- 1 パスの隣接ステップがすべて UP（`(k-1) * pⱼ ≤ pⱼ₊₁`）。
`PassSum5.AllDown` の双対。 -/
def AllUp (x : List α) (k bound : ℕ) : Prop :=
  ∀ (s p m q m' : ℕ), s ≤ x.length →
    firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m) →
    firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 = some (q, m') →
    (k - 1) * p ≤ q

/-- **`AllUp` の不変条件**。周期が `(k-1)` 倍ずつ増え、しかもどれも `< bound` なので、
現在位置から先の周期和は等比級数として

```
(k - 2) * Σⱼ pⱼ + p₀ ≤ (k - 1) * bound
```

を満たす。この形は `fuel` に関する**前向きの**帰納で証明できる（末尾項を参照しない）。 -/
theorem allUp_invariant (x : List α) (k bound : ℕ) (hk : 4 ≤ k) (h : AllUp x k bound) :
    ∀ (fuel s p m : ℕ), s ≤ x.length →
      firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m) →
      (k - 2) * stripLoop2Periods x k bound fuel s + p ≤ (k - 1) * bound := by
  intro fuel
  induction fuel with
  | zero =>
    intro s p m _ hfo
    have hlt := firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo
    have h1 : bound ≤ (k - 1) * bound := Nat.le_mul_of_pos_left _ (by omega)
    simp only [stripLoop2Periods, Nat.mul_zero, Nat.zero_add]
    omega
  | succ fuel ih =>
    intro s p m hs hfo
    have hlt := firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo
    have hs'le : nextPos x k s p ≤ x.length := nextPos_le x k bound (by omega) hs hfo
    rw [stripLoop2Periods, hfo]
    simp only []
    have hexp : (k - 2) * p + p = (k - 1) * p := by
      have hkk : k - 1 = (k - 2) + 1 := by omega
      rw [hkk, Nat.succ_mul]
    rcases hfo' : firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
      _ | ⟨q, m'⟩
    · have hz : stripLoop2Periods x k bound fuel (nextPos x k s p) = 0 :=
        stripLoop2Periods_of_none x k bound hfo' fuel
      rw [hz]
      have hmono : (k - 1) * p ≤ (k - 1) * bound := Nat.mul_le_mul_left _ (by omega)
      have e : (k - 2) * (p + 0) = (k - 2) * p := by ring
      omega
    · have hrec := ih (nextPos x k s p) q m' hs'le hfo'
      have hup := h s p m q m' hs hfo hfo'
      set T := stripLoop2Periods x k bound fuel (nextPos x k s p) with hT
      have e : (k - 2) * (p + T) = (k - 2) * p + (k - 2) * T := by ring
      omega

/-- **UP しか無いパスに対する `PassSumLinear`（`k = 8`, `C₁ = 2`）**。

`6 * Σⱼ pⱼ + p₀ ≤ 7 * bound` から `Σⱼ pⱼ ≤ 2 * bound`。 -/
theorem passSumLinear_of_allUp_eight (x : List α)
    (h : ∀ b : ℕ, AllUp x 8 b) : PassSumLinear x 8 2 := by
  intro b s
  by_cases hs : s ≤ x.length
  · rcases hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [stripLoop2Periods_of_none x 8 b hfo]; exact Nat.zero_le _
    · have hinv := allUp_invariant x 8 b (by omega) (h b) (x.length + 1) s p m hs hfo
      omega
  · have hnil : x.drop s = ([] : List α) := by
      apply List.drop_eq_nil_of_le; omega
    have hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 = none := by
      rw [hnil]
      cases (x.length + 1) with
      | zero => rfl
      | succ f => rw [firstOuter]; simp
    rw [stripLoop2Periods_of_none x 8 b hfo]; exact Nat.zero_le _

/-! ## §2 UP ステップの本数 -/

/-- 1 パスのうち **UP ステップ**（`(k-1) * pⱼ ≤ pⱼ₊₁`）の本数。
`stripLoop2UpPeriods` の「重み `pⱼ₊₁`」を「重み `1`」に置き換えたもの。 -/
def stripLoop2UpCount (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          (match firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
            | none => 0
            | some (q, _) => if (k - 1) * p ≤ q then 1 else 0)
          + stripLoop2UpCount x k bound fuel (nextPos x k s p)

/-- **無条件**：`firstOuter` の返す周期は常に `< bound` なので、UP で到達した周期の
総和は「UP の本数 × bound」で抑えられる。 -/
theorem upPeriods_le_bound_mul_upCount (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ),
      stripLoop2UpPeriods x k bound fuel s ≤ bound * stripLoop2UpCount x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; simp [stripLoop2UpPeriods, stripLoop2UpCount]
  | succ fuel ih =>
    intro s
    rw [stripLoop2UpPeriods, stripLoop2UpCount]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp
    · simp only []
      have hrest := ih (nextPos x k s p)
      rcases hfo' : firstOuter (x.drop (nextPos x k s p)) k bound (x.length + 1) 1 with
        _ | ⟨q, m'⟩
      · simp only [Nat.zero_add]
        exact hrest
      · simp only []
        have hq := firstOuter_lt_bound (x.drop (nextPos x k s p)) k bound
          (x.length + 1) 1 q m' hfo'
        by_cases hup : (k - 1) * p ≤ q
        · rw [if_pos hup, if_pos hup]
          have e : bound * (1 + stripLoop2UpCount x k bound fuel (nextPos x k s p))
              = bound + bound * stripLoop2UpCount x k bound fuel (nextPos x k s p) := by ring
          omega
        · rw [if_neg hup, if_neg hup]
          have e : bound * (0 + stripLoop2UpCount x k bound fuel (nextPos x k s p))
              = bound * stripLoop2UpCount x k bound fuel (nextPos x k s p) := by ring
          omega

/-! ## §3 `PassSumLinear` の UP 本数への還元 -/

/-- **UP ステップの本数が定数なら `PassSumLinear`**。`PassSum5.passSumLinear_of_upSum`
と `upPeriods_le_bound_mul_upCount` の合成。 -/
theorem passSumLinear_of_upCount (x : List α) (k n₀ : ℕ) (hk : 4 ≤ k)
    (hCnt : ∀ b s : ℕ, stripLoop2UpCount x k b (x.length + 1) s ≤ n₀) :
    PassSumLinear x k ((k - 1) * (n₀ + 1)) := by
  refine passSumLinear_of_upSum x k n₀ hk ?_
  intro b s
  have h1 := upPeriods_le_bound_mul_upCount x k b (x.length + 1) s
  have h2 : b * stripLoop2UpCount x k b (x.length + 1) s ≤ b * n₀ :=
    Nat.mul_le_mul_left _ (hCnt b s)
  have e : b * n₀ = n₀ * b := by ring
  omega

/-! ## §4 `k = 8` の主張 -/

/-- **`k = 8` の `PassPeriodSum`（UP 本数 `≤ 2` を仮定）**。

数値実験では 1 パスの反復回数は常に `≤ 3`（したがって UP ステップは `≤ 2`）であった。
その仮定のもとで `C₁ = 21` の線形上界が従う。 -/
theorem passPeriodSum_eight_of_upCount
    (hCnt : ∀ (x : List (Fin 2)) (b s : ℕ),
      stripLoop2UpCount x 8 b (x.length + 1) s ≤ 2) :
    EndToEnd2.PassPeriodSum 8 21 := by
  intro x b s
  have h := passSumLinear_of_upCount x 8 2 (by omega) (fun b s => hCnt x b s) b s
  simpa using h

/-- 一般の `n₀` 版。 -/
theorem passPeriodSum_eight_of_upCount' (n₀ : ℕ)
    (hCnt : ∀ (x : List (Fin 2)) (b s : ℕ),
      stripLoop2UpCount x 8 b (x.length + 1) s ≤ n₀) :
    EndToEnd2.PassPeriodSum 8 (7 * (n₀ + 1)) := by
  intro x b s
  have h := passSumLinear_of_upCount x 8 n₀ (by omega) (fun b s => hCnt x b s) b s
  simpa using h

end PalPeg
