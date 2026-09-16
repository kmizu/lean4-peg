import PalPeg.GSDecompose2Work

/-!
# 1 パス内の連続する run の構造（`Σⱼ pⱼ ≤ C₁ * T` に向けた段階補題）

`stripLoop2` の 1 パスで現れる run 開始位置 `a₀ < a₁ < …`（`aⱼ₊₁ = aⱼ + rⱼ - k*pⱼ + 1`）に
ついて、**隣接する 2 つの run の関係を完全に決定する**補題を与える。

主結果（すべて `sorry` なし）：

* `step_window_subset_iff`：次の run の窓 `Wⱼ₊₁ = [aⱼ₊₁, aⱼ₊₁ + k*pⱼ₊₁)` が今の周期領域
  `Rⱼ = [aⱼ, aⱼ + rⱼ)` に収まるのは **`pⱼ₊₁ < pⱼ` のとき、かつそのときに限る**。
* `step_dichotomy`：したがって `(k-1) * pⱼ₊₁ < pⱼ`（DOWN）か `(k-1) * pⱼ ≤ pⱼ₊₁`（UP）の
  いずれか。とくに `pⱼ₊₁ ≠ pⱼ`（`step_period_ne`）。
* `step_down_reach`：DOWN のとき次の到達域は `rⱼ₊₁ < pⱼ + pⱼ₊₁`。
* `step_down_shrink`：DOWN のとき `Rⱼ₊₁ ⊊ Rⱼ`（右端が真に減る）。
* `step_down_advance`：DOWN のとき前進量は `dⱼ₊₁ ≤ pⱼ - (k-1) * pⱼ₊₁ < pⱼ`。
* `step_up_grow`：UP のとき右端は `k*(k-2)*pⱼ` 以上増える。

これらは (A) `child_period_bound` / (B) `sibling_overlap_lt` / `dvd_of_inner_window` の
直接の帰結であり、`GSDecompose2` 末尾のコメントが求めている入れ子木の骨格にあたる。
`Σⱼ pⱼ ≤ C₁ * T` そのものはまだ得られていない（ファイル末尾の注記を参照）。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## 1 反復ぶんのデータ（`GSDecompose2.strip_step_data` の公開版） -/

/-- `stripLoop2` の 1 反復で `firstOuter` が返す `p` は最小の `k`-繰り返し周期で、
`extendReach` はその到達域を与える。 -/
theorem stripLoop2_step_data (x : List α) (k bound : ℕ) (hk : 3 ≤ k) {s p m : ℕ}
    (hs : s ≤ x.length) (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m)) :
    IsLeastKRep (x.drop s) k p ∧ p < bound ∧
      k * p ≤ extendReach (x.drop s) p (x.length + 1) (k * p) ∧
      ReachOf (x.drop s) p (extendReach (x.drop s) p (x.length + 1) (k * p)) := by
  have hbelow : ∀ p', p' < 1 → ¬ KRep (x.drop s) k p' := by
    intro p' hp'; rintro ⟨h1, -, -⟩; omega
  obtain ⟨hleast, -⟩ :=
    firstOuter_some (x.drop s) k bound hk (x.length + 1) 1 p m (by omega) hbelow hfo
  refine ⟨hleast, firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo, ?_⟩
  have hvlen : (x.drop s).length = x.length - s := by simp
  exact extendReach_spec (x.drop s) p (x.length + 1) (k * p) (by omega)
    (Nat.le_mul_of_pos_left p (by omega)) hleast.1.2.1 hleast.1.2.2

/-! ## 隣接する 2 つの run

以下 `w` は現在位置から見た接尾辞、`p` は最小 `k`-繰り返し周期、`r` はその到達域、
`d = r - k*p + 1` が `stripLoop2` の前進量、`q` は次の位置 `w.drop d` の最小周期。 -/

section Step

variable {w : List α} {k p q r r' d : ℕ}

/-- 窓の包含は前進量の定義から純算術的に決まる：`d + k*q ≤ r ↔ q < p`
（`d` は前進量、すなわち `k*p + d = r + 1`）。 -/
theorem step_window_subset_iff (hk : 4 ≤ k) (_hp : 0 < p) (hd : k * p + d = r + 1) :
    (d + k * q ≤ r ↔ q < p) := by
  have h1 : k * q < k * p ↔ q < p := by
    constructor
    · intro h
      by_contra hc
      exact absurd (Nat.mul_le_mul_left k (show p ≤ q by omega)) (by omega)
    · intro h
      have h2 : k * (q + 1) ≤ k * p := Nat.mul_le_mul_left k (by omega)
      rw [Nat.mul_add, Nat.mul_one] at h2
      omega
  omega

/-- **DOWN の場合**（`q < p`）：子の周期は `(k-1) * q < p` を満たす（(A) の言い換え）。 -/
theorem step_down_period (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p) :
    (k - 1) * q < p := by
  have hp : 0 < p := hleast.1.1
  exact child_period_bound hk hleast hR hkr hq
    ((step_window_subset_iff (q := q) hk hp hd).mpr hlt) (by omega)

/-- **UP の場合**（`p ≤ q`）：`(k-1) * p ≤ q`（(B) の言い換え）。 -/
theorem step_up_period (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hge : p ≤ q) :
    (k - 1) * p ≤ q := by
  have hp : 0 < p := hleast.1.1
  have hkp : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hnfit : r < d + k * q := by
    by_contra hc
    exact absurd ((step_window_subset_iff (q := q) hk hp hd).mp (by omega)) (by omega)
  have hov := sibling_overlap_lt hk hleast hR hkr hq (by omega) hnfit
  have h2 : (k - 1) * p + p = k * p := by
    rw [← Nat.succ_mul]; congr 1; omega
  omega

/-- **二分法**：隣接する run の周期は「`(k-1)` 倍以上縮む」か「`(k-1)` 倍以上伸びる」か。 -/
theorem step_dichotomy (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) :
    (k - 1) * q < p ∨ (k - 1) * p ≤ q := by
  by_cases h : q < p
  · exact Or.inl (step_down_period hk hd hleast hR hkr hq h)
  · exact Or.inr (step_up_period hk hd hleast hR hkr hq (by omega))

/-- 隣接する run の周期は必ず異なる。 -/
theorem step_period_ne (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) : q ≠ p := by
  rintro rfl
  have hp : 0 < q := hleast.1.1
  have h := step_up_period hk hd hleast hR hkr hq (le_refl _)
  have h3 : 2 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
  omega

/-- **DOWN の到達域**：`q < p` なら次の到達域は `p + q` 未満。
（そうでなければ `dvd_of_inner_window` から `p ∣ q`、つまり `p ≤ q` になってしまう。） -/
theorem step_down_reach (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (_hkq : k * q ≤ r') :
    r' < p + q := by
  have hp : 0 < p := hleast.1.1
  have hqpos : 0 < q := hq.1.1
  have h1 : 2 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hfit : d + (p + q) ≤ r := by omega
  by_contra hcon
  have hwin : HasPeriod ((w.drop d).take (p + q)) q :=
    hasPeriod_take_of_le hR'.2.1 (by omega)
  have hdvd : p ∣ q :=
    dvd_of_inner_window (by omega) hleast hR hkr hqpos hfit (le_refl _) hwin
  exact absurd (Nat.le_of_dvd hqpos hdvd) (by omega)

/-- **DOWN では領域が真に縮む**：右端 `d + r'` は `r` より真に小さい。 -/
theorem step_down_shrink (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') :
    d + r' < r := by
  have hp : 0 < p := hleast.1.1
  have h := step_down_reach hk hd hleast hR hkr hq hlt hR' hkq
  have h1 : 2 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  omega

/-- **DOWN では前進量も小さい**：次の前進量 `r' - k*q + 1` は `p - (k-1)*q` 以下。 -/
theorem step_down_advance (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') :
    r' - k * q + 1 ≤ p - (k - 1) * q := by
  have h := step_down_reach hk hd hleast hR hkr hq hlt hR' hkq
  have hgrow := step_down_period hk hd hleast hR hkr hq hlt
  have h2 : (k - 1) * q + q = k * q := by rw [← Nat.succ_mul]; congr 1; omega
  omega

/-- **UP では右端が大きく伸びる**：`(d + r') - r ≥ k*(k-2)*p + 1`。 -/
theorem step_up_grow (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hge : p ≤ q) (hkq : k * q ≤ r') :
    r + (k * (k - 2) * p + 1) ≤ d + r' := by
  have hp : 0 < p := hleast.1.1
  have hgrow := step_up_period hk hd hleast hR hkr hq hge
  have h1 : k * ((k - 1) * p) ≤ k * q := Nat.mul_le_mul_left k hgrow
  have h2 : k * ((k - 1) * p) = k * (k - 2) * p + k * p := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [hk1]; ring
  omega

end Step

/-! ## `stripLoop2` の 2 反復への適用 -/

/-- `stripLoop2` の連続する 2 反復に対する二分法。次の位置は
`s' = s + (r - k*p + 1)`（`r` は `extendReach` が返す到達域）。 -/
theorem stripLoop2_step_dichotomy (x : List α) (k bound : ℕ) (hk : 4 ≤ k) {s p m q m' : ℕ}
    (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m))
    (hfo' : firstOuter
        (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
        k bound (x.length + 1) 1 = some (q, m')) :
    (k - 1) * q < p ∨ (k - 1) * p ≤ q := by
  obtain ⟨hleast, -, hkr, hR⟩ := stripLoop2_step_data x k bound (by omega) hs hfo
  set r := extendReach (x.drop s) p (x.length + 1) (k * p) with hrdef
  have hp : 0 < p := hleast.1.1
  have hkp : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hvlen : (x.drop s).length = x.length - s := by simp
  have hrle : r ≤ x.length - s := by have := hR.1; omega
  have hs' : s + (r - k * p + 1) ≤ x.length := by omega
  obtain ⟨hqleast, -, -, -⟩ := stripLoop2_step_data x k bound (by omega) hs' hfo'
  have hEq : (x.drop s).drop (r - k * p + 1) = x.drop (s + (r - k * p + 1)) := by
    rw [List.drop_drop, Nat.add_comm]
  rw [← hEq] at hqleast
  exact step_dichotomy hk (d := r - k * p + 1) (by omega) hleast hR hkr hqleast

/-- `stripLoop2` の連続する 2 反復の周期は必ず異なる。 -/
theorem stripLoop2_step_period_ne (x : List α) (k bound : ℕ) (hk : 4 ≤ k) {s p m q m' : ℕ}
    (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m))
    (hfo' : firstOuter
        (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
        k bound (x.length + 1) 1 = some (q, m')) :
    q ≠ p := by
  have hp : 0 < p := (stripLoop2_step_data x k bound (by omega) hs hfo).1.1.1
  rintro rfl
  have h3 : 2 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
  rcases stripLoop2_step_dichotomy x k bound hk hs hfo hfo' with h | h <;> omega

/-! ## 残る課題

上の二分法だけでは `Σⱼ pⱼ ≤ C₁ * T` は出ない。実際、抽象的な列
`p, p/(k-1), p, p/(k-1), …` は二分法・`Σⱼ dⱼ < T`・`(k-1)*pⱼ < T` をすべて満たすが
`Σⱼ pⱼ = Θ(T²/k)` になる。したがって隣接でない対 `(j, j+2)` 以降の情報が必須である。

`step_down_advance` はその第一歩で、DOWN のあと `aⱼ₊₂ - aⱼ₊₁ < pⱼ` なので `aⱼ₊₂` はまだ
`Rⱼ` の内側にあり、(A)/(B) を対 `(j, j+2)` に適用できる。そこから
`(k-1)*pⱼ₊₂ < pⱼ` または `pⱼ₊₂ ≥ (k-2)*pⱼ - 1` が出るので、上の振動列は排除される。

数値実験（`k = 4`、`x = Q^k`、`Q` は原始的、`bound = |Q| = T`）では、`T ≤ 24` の全探索と
`T ≤ 60` の構造化探索の範囲で `Σⱼ pⱼ / T ≤ 0.40` であり、run 数も 3 以下だった。
`C₁ = 4*k` は十分に余裕のある定数と思われる。 -/

end PalPeg
