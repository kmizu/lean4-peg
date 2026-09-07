import PalPeg.PassSum

/-!
# 1 パス内の「2 手先」の構造（`Σⱼ pⱼ ≤ C₁ * T` に向けた第 2 段）

`PalPeg.PassSum` は隣接する 2 つの run の関係（`step_dichotomy` など）を完全に決定した。
しかしそこの「残る課題」で指摘されているとおり、隣接の情報だけでは
`Σⱼ pⱼ ≤ C₁ * T` は出ない：抽象列 `p, p/(k-1), p, p/(k-1), …` が二分法をすべて
満たしてしまうからである。

このファイルは **対 `(j, j+2)`** の情報を確立し、その振動列を排除する。

主結果（すべて `sorry` なし）：

* `step_down_next_pos_lt`：DOWN のあとの位置 `d + d'` はまだ親の周期領域 `Rⱼ` の内側。
* `step_down_then`：**DOWN `j → j+1` のあとは
  `(k-1) * pⱼ₊₂ < pⱼ`（真の孫）か `(k-2) * pⱼ ≤ pⱼ₊₂`（親を大きく飛び越す UP）の
  いずれか**。中間の値（とくに `pⱼ₊₂ = pⱼ`）は起こりえない。
* `step_down_then_ne`：したがって DOWN のあと `pⱼ₊₂ ≠ pⱼ`。
* `stripLoop2_step2_down_then` / `stripLoop2_step2_period_ne`：`stripLoop2` の連続する
  3 反復への適用。

証明の骨子（`step_down_then`）：親 run を `w`（周期 `p`、到達域 `r`、`k*p + d = r + 1`）、
子を `w.drop d`（周期 `q < p`、到達域 `r'`、`k*q + d' = r' + 1`）とすると、
`step_down_advance` から `d' ≤ p - (k-1)*q ≤ p` なので `t := d + d'` はまだ `r` 未満。
そこで孫の窓 `[t, t + k*q'')` について場合分けする：

* 窓が `Rⱼ` に収まるなら (A) `child_period_bound` で `(k-1)*q'' < p`
  （`q'' = p` は `t ≤ d - 1 < t` を導くので起こりえない）；
* 収まらないなら (B) `sibling_overlap_lt` で `r - t < p + q''`。ここで
  `r - t = k*p - 1 - d' ≥ (k-1)*p - 1` なので `(k-2)*p ≤ q''`。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

section Step2

variable {w : List α} {k p q q' r r' d d' : ℕ}

/-- DOWN のあとの次の開始位置 `d + d'` は、まだ親の周期領域 `[0, r)` の内側にある。 -/
theorem step_down_next_pos_lt (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') (hd' : k * q + d' = r' + 1) :
    d + d' < r := by
  have hp : 0 < p := hleast.1.1
  have hadv := step_down_advance hk hd hleast hR hkr hq hlt hR' hkq
  have hkp : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  omega

/-- **2 手先の二分法**。DOWN（`q < p`）のあとの周期 `q'` は、`p` の `1/(k-1)` 未満まで
落ちるか、逆に `(k-2)*p` 以上まで跳ね上がるかのどちらかで、その中間はない。 -/
theorem step_down_then (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') (hd' : k * q + d' = r' + 1)
    (hq' : IsLeastKRep (w.drop (d + d')) k q') :
    (k - 1) * q' < p ∨ (k - 2) * p ≤ q' := by
  have hp : 0 < p := hleast.1.1
  have hqpos : 0 < q := hq.1.1
  have hq'pos : 0 < q' := hq'.1.1
  have hkp : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hadv := step_down_advance hk hd hleast hR hkr hq hlt hR' hkq
  have hkq1 : (k - 1) * q + q = k * q := by rw [← Nat.succ_mul]; congr 1; omega
  have hd'le : d' ≤ p := by omega
  have hd1 : 1 ≤ d' := by omega
  have hpos := step_down_next_pos_lt hk hd hleast hR hkr hq hlt hR' hkq hd'
  by_cases hfit : d + d' + k * q' ≤ r
  · -- 孫の窓は親の領域に収まる：(A) が使える
    refine Or.inl (child_period_bound hk hleast hR hkr hq' hfit ?_)
    rintro rfl
    -- `q' = p` なら `d + d' + k*p ≤ k*p + d - 1`、つまり `d' ≤ -1`
    omega
  · -- 収まらない：(B) の重なり評価
    have hov := sibling_overlap_lt hk hleast hR hkr hq' (by omega) (by omega)
    have hkp1 : (k - 1) * p + p = k * p := by rw [← Nat.succ_mul]; congr 1; omega
    have hkp2 : (k - 2) * p + p = (k - 1) * p := by
      have h : k - 1 = (k - 2) + 1 := by omega
      rw [h, Nat.succ_mul]
    omega

/-- DOWN のあとの周期は元の周期と一致しない（`p, p/(k-1), p, …` 型の振動の排除）。 -/
theorem step_down_then_ne (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') (hd' : k * q + d' = r' + 1)
    (hq' : IsLeastKRep (w.drop (d + d')) k q') :
    q' ≠ p := by
  rintro rfl
  have hp : 0 < q' := hleast.1.1
  have h1 : 2 * q' ≤ (k - 1) * q' := Nat.mul_le_mul_right q' (by omega)
  have h2 : 2 * q' ≤ (k - 2) * q' := Nat.mul_le_mul_right q' (by omega)
  rcases step_down_then hk hd hleast hR hkr hq hlt hR' hkq hd' hq' with h | h <;> omega

end Step2

/-! ## `stripLoop2` の 3 反復への適用 -/

/-- `stripLoop2` の連続する 3 反復への `step_down_then` の適用。
位置は `s`、`s₁ = s + d`、`s₂ = s₁ + d'`（`d`, `d'` は各段の前進量）。 -/
theorem stripLoop2_step2_down_then (x : List α) (k bound : ℕ) (hk : 4 ≤ k)
    {s p m q m' q' m'' : ℕ} (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m))
    (hfo' : firstOuter
        (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
        k bound (x.length + 1) 1 = some (q, m'))
    (hlt : q < p)
    (hfo'' : firstOuter
        (x.drop ((s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1))
          + (extendReach
              (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
              q (x.length + 1) (k * q) - k * q + 1)))
        k bound (x.length + 1) 1 = some (q', m'')) :
    (k - 1) * q' < p ∨ (k - 2) * p ≤ q' := by
  obtain ⟨hleast, -, hkr, hR⟩ := stripLoop2_step_data x k bound (by omega) hs hfo
  set r := extendReach (x.drop s) p (x.length + 1) (k * p) with hrdef
  set d := r - k * p + 1 with hddef
  have hp : 0 < p := hleast.1.1
  have hkp : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hvlen : (x.drop s).length = x.length - s := by simp
  have hrle : r ≤ x.length - s := by have := hR.1; omega
  have hs1 : s + d ≤ x.length := by omega
  obtain ⟨hqleast, -, hkq, hR'⟩ := stripLoop2_step_data x k bound (by omega) hs1 hfo'
  set r' := extendReach (x.drop (s + d)) q (x.length + 1) (k * q) with hr'def
  set d' := r' - k * q + 1 with hd'def
  have hq : 0 < q := hqleast.1.1
  have hkqpos : 0 < k * q := Nat.mul_pos (by omega) hq
  have hvlen1 : (x.drop (s + d)).length = x.length - (s + d) := by simp
  have hr'le : r' ≤ x.length - (s + d) := by have := hR'.1; omega
  have hs2 : s + d + d' ≤ x.length := by omega
  obtain ⟨hq'least, -, -, -⟩ := stripLoop2_step_data x k bound (by omega) hs2 hfo''
  -- 接尾辞の同一視
  have hEq1 : (x.drop s).drop d = x.drop (s + d) := by rw [List.drop_drop, Nat.add_comm]
  have hEq2 : (x.drop s).drop (d + d') = x.drop (s + d + d') := by
    rw [List.drop_drop]; congr 1; omega
  rw [← hEq1] at hqleast hR'
  rw [← hEq2] at hq'least
  exact step_down_then (w := x.drop s) hk (d := d) (by omega) hleast hR hkr hqleast hlt
    hR' hkq (by omega) hq'least

/-- DOWN の直後の 2 手先の周期は元に戻らない。 -/
theorem stripLoop2_step2_period_ne (x : List α) (k bound : ℕ) (hk : 4 ≤ k)
    {s p m q m' q' m'' : ℕ} (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m))
    (hfo' : firstOuter
        (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
        k bound (x.length + 1) 1 = some (q, m'))
    (hlt : q < p)
    (hfo'' : firstOuter
        (x.drop ((s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1))
          + (extendReach
              (x.drop (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))
              q (x.length + 1) (k * q) - k * q + 1)))
        k bound (x.length + 1) 1 = some (q', m'')) :
    q' ≠ p := by
  have hp : 0 < p := (stripLoop2_step_data x k bound (by omega) hs hfo).1.1.1
  rintro rfl
  have h1 : 2 * q' ≤ (k - 1) * q' := Nat.mul_le_mul_right q' (by omega)
  have h2 : 2 * q' ≤ (k - 2) * q' := Nat.mul_le_mul_right q' (by omega)
  rcases stripLoop2_step2_down_then x k bound hk hs hfo hfo' hlt hfo'' with h | h <;> omega

/-! ## 現状と残る課題

`step_down_then` により、run 開始位置の列 `p₀, p₁, …` は次の 3 種類の遷移しか持たない：

* UP：`(k-1) * pⱼ ≤ pⱼ₊₁`（`step_up_period`）；
* DOWN：`(k-1) * pⱼ₊₁ < pⱼ`（`step_down_period`）で、そのあとは
  さらに DOWN（`(k-1) * pⱼ₊₂ < pⱼ₊₁ < pⱼ/(k-1)`）か、
  **`(k-2) * pⱼ ≤ pⱼ₊₂` の大きな UP**（`step_down_then`）。

とくに `PassSum` 末尾の反例列 `p, p/(k-1), p, p/(k-1), …` は排除された
（`step_down_then_ne`）。したがって「極大値」の列 `P₁, P₂, …`（DOWN 直前の値）は
`Pᵢ₊₁ ≥ (k-2) * Pᵢ` を満たす**降下が 1 段のときには**幾何級数的に増大し、
`pⱼ < bound = T` と合わせて `Σⱼ pⱼ ≤ ((k-1)/(k-3)) * T` を与える。

**まだ足りない点**（正直な評価）。降下が 2 段以上続く場合、`step_down_then` を
最後の DOWN に当てても得られるのは `pⱼ₊₂ ≥ (k-2) * pⱼ₊₁` であって、降下の起点 `Pᵢ`
との比較にはならない。すなわち

```
P → P/(k-1) → … → m → (k-2)(k-1)m → … → P → …
```

という「深い V 字」を何度も繰り返す抽象列は、UP/DOWN 二分法・`step_down_then`・
`Σⱼ dⱼ < T`・`pⱼ < T` をすべて満たしたまま `Σⱼ pⱼ = Θ(T²/log T)` になりうる。
ポテンシャル `E = aⱼ + rⱼ`（`step_up_grow` / `step_down_shrink`）も、
DOWN の下落 `≤ k*pⱼ - k*pⱼ₊₁ - 1` と UP の上昇 `≥ k*pⱼ₊₁ - k*pⱼ + 1` が
1 サイクルあたり差 `2` しか生まないので、この列を排除できない。

したがって残る本質は、深い V 字が**語の側で**起こりえないこと（降下後の着地位置では
`Pᵢ/(k-1)` 未満の周期がもう始まらない、という「着地補題」）であり、それには
`T`-周期性を使う新しい議論が要る。ここでは形式化していない。 -/

end PalPeg
