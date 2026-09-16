import Mathlib.Tactic.Linarith
import PalPeg.PassSum3

/-!
# 同じ親のもとでの「子の周期の成長」（`Σⱼ pⱼ ≤ C₁ * T` に向けた第 4 段）

`PalPeg.PassSum3` は語の側の局所構造 (F1)–(F3) を確立したが、その末尾で
残る困難として次を挙げていた：

> `(F3)` の "long descendant" を経て親の領域を出たあとの着地位置
> `a_{c'} = E_ℓ - k*p_ℓ + 1` と、もとの子 `c` の周期 `p_c` との間に関係がつかない。

このファイルはその関係をつける。**主結果 `children_growth_down`**：

親 `j`（周期 `P`、到達域 `R`）の子 `c`（周期 `p`、到達域 `r`）について、
`c` の部分木に降りた軌道が `c` の領域 `R_c` を出て次の子 `c'`（周期 `p'`）に着地する
とき、

```
(k - 2) * p < (k - 1) * p'
```

が成り立つ。すなわち **同じ親の連続する 2 つの子の周期は `(k-2)/(k-1)` 倍より
真に大きくなる**。`k = 4` なら `p' > (2/3) * p`。

## 証明の骨子

`c` を原点にとる（`w = x.drop a_c`）。

* `c` の最初の子（＝ `stripLoop2` の次の位置）は `d = r - k*p + 1` にあり、
  DOWN なら `step_down_period` から `(k-1) * p₁ < p`、
  `step_down_reach` から `r₁ < p + p₁`。したがって
  `E₁ = d + r₁ < d + p + p₁ = r - (k-1)*p + p₁ + 1`。
* `c` の部分木の中では右端 `E` は単調非増加（`step_down_shrink`）なので、
  最後の子孫 `ℓ` について `E_ℓ ≤ E₁`。
* 着地位置は `e' = E_ℓ - k*p_ℓ + 1`（`hstart`）。
* `c'` は `R_c` に収まらない（`hexit`：`r < e' + k*p'`）。

この 4 つを合わせると `k*p + k*p_ℓ < r₁ + 2 + k*p'`、`p_ℓ ≥ 1` と
`r₁ < p + p₁`、`(k-1)*p₁ < p` から `(k-2)*p < (k-1)*p'` が出る
（`children_growth_arith`）。評価は最悪ケースでちょうど等号すれすれで、
`(k-2)/(k-1)` という係数はこの議論の限界である。

補助として次も置く：

* `sibling_period_ge_of_not_fit`：窓が親の領域に収まらないなら `(k-1)*p ≤ q`
  （(B) の言い換え）。ℓ から `c'` への (B) の適用に使う。
* `children_growth_up`：最初の子がすでに `R_c` を出る場合（UP）は
  `(k-1)*p ≤ p'` なのでより強い。
* `children_growth_of_next`：上の 2 つの場合分けをまとめたもの。

すべて `sorry` なし。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

section ChildrenGrowth

variable {w : List α} {k p p₁ pl p' q r r₁ rl d e0 tl e' : ℕ}

/-! ## 純算術の核 -/

/-- 位置の連鎖だけからくる線形不等式（`children_growth_arith` の骨組み）。
`A = k*p`（親の窓）、`B = k*p_ℓ`（最後の子孫の窓）、`C = k*p'`（着地先の窓）。 -/
theorem exit_position_ineq {A B C d r r₁ tl rl e' : ℕ}
    (hd : A + d = r + 1) (hmono : tl + rl ≤ d + r₁)
    (hstart : e' + B = tl + rl + 1) (hexit : r < e' + C) :
    A + B < r₁ + 2 + C := by omega

/-- **核となる算術補題**。`children_growth_down` の数値的な中身。

仮定：`(k-1)*p₁ < p`（(A) 子の周期の上界）、`r₁ < p + p₁`（DOWN の到達域）、
`k*p + d = r + 1`（前進量）、`tl + rl ≤ d + r₁`（右端の単調性）、
`e' + k*pl = tl + rl + 1`（着地位置）、`r < e' + k*p'`（`R_c` からの脱出）。 -/
theorem children_growth_arith (hk : 4 ≤ k) (hpl : 0 < pl)
    (hchild : (k - 1) * p₁ < p) (hreach : r₁ < p + p₁)
    (hd : k * p + d = r + 1) (hmono : tl + rl ≤ d + r₁)
    (hstart : e' + k * pl = tl + rl + 1) (hexit : r < e' + k * p') :
    (k - 2) * p < (k - 1) * p' := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 from by omega]
  rw [show m + 4 - 1 = m + 3 from by omega] at hchild ⊢
  -- (1) 位置の連鎖
  have hkey : (m + 4) * p + (m + 4) * pl < r₁ + 2 + (m + 4) * p' :=
    exit_position_ineq hd hmono hstart hexit
  -- (2) `pl ≥ 1`
  have hpl' : (m + 4) * 1 ≤ (m + 4) * pl := Nat.mul_le_mul_left _ hpl
  rw [Nat.mul_one] at hpl'
  -- (3) まとめて
  have hE1 : (m + 4) * p + (m + 4) < p + p₁ + 1 + (m + 4) * p' := by omega
  nlinarith [hE1, hchild, hE1.le, Nat.zero_le p, Nat.zero_le p', Nat.zero_le p₁,
    Nat.zero_le m, Nat.mul_le_mul_left (m + 3) hE1.le]

/-! ## 意味論版 -/

/-- **(B) の言い換え**。次の窓が親の周期領域に収まらないなら周期は `(k-1)` 倍以上。 -/
theorem sibling_period_ge_of_not_fit (hk : 4 ≤ k) (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hnfit : r < d + k * q) :
    (k - 1) * p ≤ q := by
  have hp : 0 < p := hleast.1.1
  refine step_up_period hk hd hleast hR hkr hq ?_
  by_contra hlt
  exact absurd ((step_window_subset_iff (q := q) hk hp hd).mpr (by omega)) (by omega)

/-- **主定理（DOWN の場合）：同じ親の連続する子の周期の成長**。

`w = x.drop a_c` を子 `c` の位置から見た接尾辞、`p` をその最小 `k`-繰り返し周期、
`r` を到達域とする。`c` の最初の子（位置 `d = r - k*p + 1`、周期 `p₁ < p`、到達域 `r₁`）
に降りた軌道が、最後の子孫 `ℓ`（位置 `tl`、到達域 `rl`、周期 `pl`）を経て
`e' = tl + rl - k*pl + 1` に着地し、そこから始まる run の窓が `R_c = [0, r)` を
出る（`r < e' + k*p'`）とき、

```
(k - 2) * p < (k - 1) * p'
```

`hmono`（`tl + rl ≤ d + r₁`）は「`c` の部分木の中では右端が単調非増加」という
`step_down_shrink` の反復であり、降下列の側の情報として仮定する。 -/
theorem children_growth_down (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hd : k * p + d = r + 1)
    (h₁ : IsLeastKRep (w.drop d) k p₁) (hlt₁ : p₁ < p)
    (hR₁ : ReachOf (w.drop d) p₁ r₁) (hkq₁ : k * p₁ ≤ r₁)
    (hpl : 0 < pl) (hmono : tl + rl ≤ d + r₁)
    (hstart : e' + k * pl = tl + rl + 1) (hexit : r < e' + k * p') :
    (k - 2) * p < (k - 1) * p' :=
  children_growth_arith hk hpl
    (step_down_period hk hd hleast hR hkr h₁ hlt₁)
    (step_down_reach hk hd hleast hR hkr h₁ hlt₁ hR₁ hkq₁)
    hd hmono hstart hexit

/-- **主定理（UP の場合）**。`c` の直後の run がすでに `R_c` を出るなら、その周期は
`(k-1)*p` 以上（`step_up_period`）。とくに `(k-2)*p ≤ (k-1)*p'`。 -/
theorem children_growth_up (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hd : k * p + d = r + 1)
    (h' : IsLeastKRep (w.drop d) k p') (hge : p ≤ p') :
    (k - 2) * p ≤ (k - 1) * p' := by
  have hp : 0 < p := hleast.1.1
  have h := step_up_period hk hd hleast hR hkr h' hge
  have h1 : (k - 2) * p ≤ (k - 1) * p := Nat.mul_le_mul_right p (by omega)
  have h2 : (k - 1) * p ≤ (k - 1) * p' := Nat.mul_le_mul_left _ hge
  omega

/-- **場合分けをまとめた版**。`c` の最初の子が `R_c` の中に収まる（DOWN）なら
降下列のデータを使い、収まらない（UP）ならその run 自身が `c'` である。
いずれにせよ `(k-2)*p ≤ (k-1)*p'`。 -/
theorem children_growth_of_next (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hd : k * p + d = r + 1)
    (h₁ : IsLeastKRep (w.drop d) k p₁)
    (hR₁ : ReachOf (w.drop d) p₁ r₁) (hkq₁ : k * p₁ ≤ r₁)
    (hdown : p₁ < p →
      0 < pl ∧ tl + rl ≤ d + r₁ ∧ e' + k * pl = tl + rl + 1 ∧ r < e' + k * p')
    (hup : p ≤ p₁ → p' = p₁) :
    (k - 2) * p ≤ (k - 1) * p' := by
  by_cases hlt : p₁ < p
  · obtain ⟨hpl, hmono, hstart, hexit⟩ := hdown hlt
    exact le_of_lt
      (children_growth_down hk hleast hR hkr hd h₁ hlt hR₁ hkq₁ hpl hmono hstart hexit)
  · have hge : p ≤ p₁ := by omega
    have hpe : p' = p₁ := hup hge
    subst hpe
    exact children_growth_up hk hleast hR hkr hd h₁ hge

end ChildrenGrowth

end PalPeg
