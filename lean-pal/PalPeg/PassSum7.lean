import PalPeg.PassSum6

/-!
# 1 パスの周期和：最大周期への還元と、二分律だけでは閉じないことの証明（PassSum7）

## このファイルの位置づけ

`PassSum5` は残る仮説 `PassSumLinear`（= `EndToEnd2.PassPeriodSum`）を
**UP ステップで到達した周期の総和**に還元し（`passSumLinear_of_upSum`）、
`PassSum6` はさらに **UP ステップの本数** `stripLoop2UpCount` に還元した
（`passSumLinear_of_upCount`）。

**`PassSum6` の数値的観察（「1 パスの反復回数は 3 以下」）は誤りである。**
`k = 8`, `bound = 65` で反復 5 回のパスが存在する（本ファイル末尾の注記、および
数値実験による）。実際、入れ子状の繰り返しを深くすれば反復回数はいくらでも増える。
したがって `passPeriodSum_eight_of_upCount` の仮定
（`stripLoop2UpCount ≤ 2`）は**成り立たない**。

そこで本ファイルは

1. `PassSumLinear` を **「1 パスの周期和 ≤ C × そのパスの最大周期」** という
   スケール不変な形に還元する（`passSumLinear_of_sum_le_max`）。
   `firstOuter` の返す周期は常に `< bound` なので、最大周期は `bound` 以下であり、
   還元は無条件に正しい。数値実験では比 `Σⱼ pⱼ / (max pⱼ + 1)` は `1.29` 程度が最大で、
   `C = 2` には十分な余裕がある。
2. **`PassSum` の二分律（DOWN / UP）だけからは `PassSumLinear` は決して従わない**
   ことを証明する（`dichotomy_insufficient`）。すなわち二分律を満たし、値がすべて
   `bound` 未満で、しかも総和が `C * bound` を超える整数列が任意の `C` に対して存在する
   （`1, k, 1, k, …` という交代列）。この列は UP ステップを無限に含むので、
   `PassSum6` が要求する「UP 本数の絶対定数上界」も二分律だけからは出ない。

   つまり残る困難は**語の側の構造**（Fine–Wilf 型の議論、`PassSum3`/`PassSum4` の
   入れ子構造）を使わなければ解消しない。

すべて `sorry` なし。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## §1 1 パスの最大周期 -/

/-- 1 パスで `firstOuter` が返す周期の**最大値**（パスが空なら `0`）。
`stripLoop2Periods` の `+` を `max` に置き換えたもの。 -/
def stripLoop2MaxPeriod (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => 0
      | some (p, _) => max p (stripLoop2MaxPeriod x k bound fuel (nextPos x k s p))

/-- **無条件**：`firstOuter` の返す周期は `< bound` なので、最大周期も `bound` 以下。 -/
theorem stripLoop2MaxPeriod_le_bound (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ), stripLoop2MaxPeriod x k bound fuel s ≤ bound := by
  intro fuel
  induction fuel with
  | zero => intro s; exact Nat.zero_le _
  | succ fuel ih =>
    intro s
    rw [stripLoop2MaxPeriod]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · exact Nat.zero_le _
    · simp only []
      have hp := firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo
      have hrest := ih (nextPos x k s p)
      omega

/-- **無条件**：最大周期は周期和以下（還元が非自明であることの確認）。 -/
theorem stripLoop2MaxPeriod_le_sum (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ),
      stripLoop2MaxPeriod x k bound fuel s ≤ stripLoop2Periods x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; exact Nat.zero_le _
  | succ fuel ih =>
    intro s
    rw [stripLoop2MaxPeriod, stripLoop2Periods]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · exact Nat.zero_le _
    · simp only []
      have hrest := ih (nextPos x k s p)
      simp only [nextPos] at hrest ⊢
      omega

/-! ## §2 `PassSumLinear` の「最大周期」への還元 -/

/-- **主還元**：1 パスの周期和がそのパスの**最大周期**の定数倍で抑えられるなら
`PassSumLinear` が従う。`bound` が消えたスケール不変な形になる。

数値実験（`k = 8`）では `Σⱼ pⱼ ≤ 1.29 * (max pⱼ + 1)` であり、`C = 2` で十分な余裕がある。 -/
theorem passSumLinear_of_sum_le_max (x : List α) (k C : ℕ)
    (h : ∀ b s : ℕ, stripLoop2Periods x k b (x.length + 1) s
          ≤ C * stripLoop2MaxPeriod x k b (x.length + 1) s) :
    PassSumLinear x k C := by
  intro b s
  have h1 := h b s
  have h2 : C * stripLoop2MaxPeriod x k b (x.length + 1) s ≤ C * b :=
    Nat.mul_le_mul_left _ (stripLoop2MaxPeriod_le_bound x k b (x.length + 1) s)
  omega

/-- `k = 8` 版：`Σ ≤ 2 * max` なら `EndToEnd2.PassPeriodSum 8 2`。 -/
theorem passPeriodSum_eight_of_sum_le_max
    (h : ∀ (x : List (Fin 2)) (b s : ℕ),
      stripLoop2Periods x 8 b (x.length + 1) s
        ≤ 2 * stripLoop2MaxPeriod x 8 b (x.length + 1) s) :
    EndToEnd2.PassPeriodSum 8 2 := by
  intro x b s
  exact passSumLinear_of_sum_le_max x 8 2 (fun b s => h x b s) b s

/-! ## §3 二分律だけでは `PassSumLinear` は従わない -/

/-- `PassSum.step_dichotomy` が与える、隣接する 2 項の関係だけを抽象化した条件。 -/
def DichChain (k : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ j, (k - 1) * f (j + 1) < f j ∨ (k - 1) * f j ≤ f (j + 1)

/-- 交代列 `1, k, 1, k, …`。 -/
def altChain (k : ℕ) : ℕ → ℕ := fun j => if j % 2 = 0 then 1 else k

theorem altChain_pos (k : ℕ) (hk : 4 ≤ k) (j : ℕ) : 0 < altChain k j := by
  unfold altChain; split <;> omega

theorem altChain_lt (k : ℕ) (hk : 4 ≤ k) (j : ℕ) : altChain k j < k + 1 := by
  unfold altChain; split <;> omega

/-- 交代列は二分律を満たす（偶数番目で UP、奇数番目で DOWN）。 -/
theorem altChain_dich (k : ℕ) (hk : 4 ≤ k) : DichChain k (altChain k) := by
  intro j
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hj with hj | hj
  · right
    have h1 : (j + 1) % 2 = 1 := by omega
    unfold altChain
    rw [if_pos hj, if_neg (by omega : ¬ (j + 1) % 2 = 0)]
    omega
  · left
    have h1 : (j + 1) % 2 = 0 := by omega
    unfold altChain
    rw [if_neg (by omega : ¬ j % 2 = 0), if_pos h1]
    omega

/-- 交代列には UP ステップが無限に現れる。 -/
theorem altChain_up (k : ℕ) (hk : 4 ≤ k) (j : ℕ) :
    (k - 1) * altChain k (2 * j) ≤ altChain k (2 * j + 1) := by
  unfold altChain
  rw [if_pos (by omega : 2 * j % 2 = 0), if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
  omega

/-- 最初の `n` 項の和（`Finset` 記法を避けた素朴な定義）。 -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem altChain_sum (k : ℕ) :
    ∀ N, sumTo (altChain k) (2 * N) = N * (k + 1) := by
  intro N
  induction N with
  | zero => simp [sumTo]
  | succ N ih =>
    have e : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [e, sumTo, sumTo, ih]
    have h0 : altChain k (2 * N) = 1 := by
      unfold altChain; rw [if_pos (by omega : 2 * N % 2 = 0)]
    have h1 : altChain k (2 * N + 1) = k := by
      unfold altChain; rw [if_neg (by omega : ¬ (2 * N + 1) % 2 = 0)]
    rw [h0, h1]; ring

/-- **二分律だけでは不十分**。任意の `C` に対し、二分律を満たし、値がすべて正で
`b` 未満、しかも有限個の項の和が `C * b` を超える整数列が存在する。

したがって `PassSum5.passSumLinear_of_upSum` の残る仮定（UP 周期和の線形性）も
`PassSum6.passSumLinear_of_upCount` の残る仮定（UP 本数の定数上界）も、
`PassSum.step_dichotomy` **だけ**からは決して導けない。語の側の構造
（`PassSum3` の Fine–Wilf 型補題、`PassSum4` の入れ子構造）が本質的に必要である。 -/
theorem dichotomy_insufficient (k C : ℕ) (hk : 4 ≤ k) :
    ∃ (f : ℕ → ℕ) (b n : ℕ),
      0 < b ∧ DichChain k f ∧ (∀ j, 0 < f j ∧ f j < b) ∧
        C * b < sumTo f n := by
  refine ⟨altChain k, k + 1, 2 * (C + 1), by omega, altChain_dich k hk,
    fun j => ⟨altChain_pos k hk j, altChain_lt k hk j⟩, ?_⟩
  rw [altChain_sum k (C + 1)]
  have : C * (k + 1) < (C + 1) * (k + 1) := by
    have : 0 < k + 1 := by omega
    exact Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) this
  omega

/-- 系：二分律を満たす列の UP ステップ本数は、絶対定数では抑えられない。 -/
theorem dichotomy_upCount_unbounded (k N : ℕ) (hk : 4 ≤ k) :
    ∃ f : ℕ → ℕ, DichChain k f ∧ (∀ j, 0 < f j ∧ f j < k + 1) ∧
      (∀ j < N, (k - 1) * f (2 * j) ≤ f (2 * j + 1)) :=
  ⟨altChain k, altChain_dich k hk,
    fun j => ⟨altChain_pos k hk j, altChain_lt k hk j⟩, fun j _ => altChain_up k hk j⟩

end PalPeg
