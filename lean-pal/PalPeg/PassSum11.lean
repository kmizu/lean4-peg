import PalPeg.PassSum10

/-!
# 消費量補題の残余：跨ぎ run の中の「第 1 子のコピー」（PassSum11）

`PassSum9` の `## 要約` が残していた穴は次の 2 つだった。

* **残り (1)**：`r₁ = L`（第 1 子の run の右端が跨ぎ量 `L = E_j - p_c` とちょうど
  一致する「巡回」配置）
* **残り (2)**：`q₁ < P` かつ `r₁ < P + q₁`（第 1 子の run が `P` に比べて短い）

本ファイルは **残り (1) を（`t + q₁ ≤ r₁` の下で）閉じる**。使うのは
`deep_crossing_*` の割り切り論法ではなく、`runEnd_up_step_le` と同じ
「`P`-周期 run の中に現れた `q`-周期因子を左へ伝播させる」論法である。

## 主定理 `crossing_copy_contradiction`

領域 `w`（原点 `a_{c+1}`、`w.take Rc` は `p_c`-周期）で

* 第 1 子の run `[0, r₁)` は `q₁`-周期で、右端に破れ `w[r₁ - q₁] ≠ w[r₁]`、
* 子孫 `j` の run `[t, t + r')` は `P`-周期（`t ≤ p_c`、`q₁ ≤ P`）、
* 跨ぎが `P + q₁` 以上：`p_c + (P + q₁) ≤ t + r'`、
* 第 1 子の run も `P + q₁` 以上の長さ：`P + q₁ ≤ r₁`

のとき、領域の `p_c`-周期性により run `j` の内部（オフセット `p_c - t`）に
第 1 子の先頭 `w.take (P + q₁)` のコピーが現れる。これは長さ `P + q₁` の
`q₁`-周期因子なので `period_factor_propagate` により
**`[t, p_c + P)` 全体が `q₁`-周期**になる。ところが `t + q₁ ≤ r₁ < p_c + P` なら
破れ `w[r₁ - q₁] ≠ w[r₁]` がこの区間の内側にあるので矛盾する。

`deep_crossing_glue_contradiction` は重なり条件 `t + P ≤ r₁` を要求していたが、
本定理はそれを `t + q₁ ≤ r₁` に弱める（`q₁ ≤ P` なので真に広い）。とくに
`q₁ = P` の巡回配置 `r₁ = L` でも、`t ≤ r₁ - q₁` である限り違反は起きない。

## 残る穴（本ファイル後）

* `r₁ < P + q₁`（残り (2)、コピーが取れない）
* `r₁ - q₁ < t`（着地位置が第 1 子の破れの直前 `q₁` セル以内にある配置）

数値実験（自己相似語 60,000 本、開始位置も乱択、子孫 8,820 個）：

* 跨ぎ `L = E_j - p_c > 0` は 248 例。**すべて `c` の直接の子**（間接の子孫は 0 例）。
* 跨ぎ量の最大は **`L/p_j = 1.0`**（`p_c = 139`, `p_j = 15`, `t = 4`, `L = 15`）。
  すなわち `E_j < p_c + p_j`（旧 (E)）は等号ぎりぎりで破れるが、
  `L ≥ P + q₁`（本定理がコピーを取るのに必要な深さ）を満たす例は **0 件**。
* 「遅い」子孫（`t ≥ (k-1) * p_j`）の跨ぎは **0 例 / 8,820**（`lateCross = 0`）。
* 消費量比の最大は `C/p_c = 0.988`（`p_c = 1386`, `C = 1370`）。

跨ぎ量を目的関数にした山登り（乱択種 1,853 本 × 900 ステップ、3 系統）でも
`L/p_j` は `1.0` を超えず、`L ≥ P + q₁` の配置は構成できなかった。
-/

namespace PalPeg
namespace PassSum11

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

open PalPeg.PassSum9

/-- **跨ぎ run の中の第 1 子のコピーによる矛盾**。

領域の `p_c`-周期性で `[p_c, p_c + P + q₁)` は `[0, P + q₁)`（`q₁`-周期）のコピーであり、
これは `P`-周期 run `[t, t + r')` の内部にある。`period_factor_propagate` により
`[t, p_c + P)` は `q₁`-周期になるが、そこには第 1 子の run の破れ
`w[r₁ - q₁] ≠ w[r₁]` が含まれるので矛盾。 -/
theorem crossing_copy_contradiction {w : List α} {pc P q1 r1 t r' Rc : ℕ}
    (hq1 : 0 < q1) (hPpos : 0 < P)
    (hreg : HasPeriod (w.take Rc) pc) (hRc : Rc ≤ w.length)
    (hrun1 : HasPeriod (w.take r1) q1) (hbreak1 : w[r1 - q1]? ≠ w[r1]?)
    (ht : t ≤ pc)
    (hlong1 : P + q1 ≤ r1)
    (hcross : pc + (P + q1) ≤ t + r')
    (hrunj : HasPeriod ((w.drop t).take r') P)
    (hr'len : t + r' ≤ w.length)
    (hfitR : pc + (P + q1) ≤ Rc)
    (hlow : t + q1 ≤ r1) (hhigh : r1 < pc + P) : False := by
  -- 領域の周期性でコピーを作る
  have hcopy : (w.drop (0 + pc)).take (P + q1) = (w.drop 0).take (P + q1) :=
    factor_copy_eq hreg hRc (by omega)
  have hfac0 : HasPeriod ((w.drop pc).take (P + q1)) q1 := by
    have h0 : (w.drop pc).take (P + q1) = w.take (P + q1) := by simpa using hcopy
    rw [h0]; exact hasPeriod_take_of_le hrun1 hlong1
  -- run `j` の座標へ移す
  have hshift : (w.drop t).drop (pc - t) = w.drop pc := by
    rw [List.drop_drop]; congr 1; omega
  have hfac : HasPeriod (((w.drop t).drop (pc - t)).take (P + q1)) q1 := by
    rw [hshift]; exact hfac0
  have hdroplen : (w.drop t).length = w.length - t := by simp
  refine factor_period_contradiction (u := w.drop t) (P := P) (q := q1) (s := pc - t)
    (R := r') (e := r1 - t) hrunj hPpos hq1 hfac (by omega) (by omega) (by omega)
    (by omega) ?_
  rw [List.getElem?_drop, List.getElem?_drop,
    show t + (r1 - t - q1) = r1 - q1 from by omega, show t + (r1 - t) = r1 from by omega]
  exact hbreak1

/-- **巡回配置 `r₁ = L` の決着**（`t + q₁ ≤ r₁` の下で）。

`L = E_j - p_c` が第 1 子の run 長 `r₁` にちょうど一致する配置でも、
`P + q₁ ≤ r₁`（コピーが取れる長さ）と `t + q₁ ≤ r₁`（着地が破れより `q₁` 以上手前）
があれば違反は起きない。`r₁ < p_c + P` は `inner_run_lt`（`r₁ < p_c + q₁`）と
`q₁ ≤ P` から従う。 -/
theorem cycling_contradiction {w : List α} {pc P q1 r1 t r' Rc L : ℕ}
    (hq1 : 0 < q1) (hPpos : 0 < P) (hq1P : q1 ≤ P)
    (hreg : HasPeriod (w.take Rc) pc) (hRc : Rc ≤ w.length)
    (hrun1 : HasPeriod (w.take r1) q1) (hbreak1 : w[r1 - q1]? ≠ w[r1]?)
    (hinner : r1 < pc + q1)
    (ht : t ≤ pc)
    (hcyc : r1 = L) (hLj : pc + L = t + r')
    (hdeep : 8 * P ≤ L)
    (hrunj : HasPeriod ((w.drop t).take r') P)
    (hr'len : t + r' ≤ w.length)
    (hfitR : pc + (P + q1) ≤ Rc)
    (hlow : t + q1 ≤ r1) : False := by
  refine crossing_copy_contradiction (Rc := Rc) (r' := r') hq1 hPpos hreg hRc hrun1 hbreak1
    ht (by omega) (by omega) hrunj hr'len hfitR hlow (by omega)

/-- **残る穴の明示**。`crossing_copy_contradiction` の仮定のうち、
数値実験で否定できていない唯一の配置は「コピーが取れない (`r₁ < P + q₁`)」か
「着地が破れの直前 `q₁` セル以内 (`r₁ < t + q₁`)」のいずれかである。 -/
def RemainingGap (P q1 r1 t : ℕ) : Prop := r1 < P + q1 ∨ r1 < t + q1

/-- 上の 2 条件は、`crossing_copy_contradiction` の残りの仮定が揃っていれば
本当に「残り全部」である（対偶の形）。 -/
theorem gap_dichotomy {w : List α} {pc P q1 r1 t r' Rc : ℕ}
    (hq1 : 0 < q1) (hPpos : 0 < P)
    (hreg : HasPeriod (w.take Rc) pc) (hRc : Rc ≤ w.length)
    (hrun1 : HasPeriod (w.take r1) q1) (hbreak1 : w[r1 - q1]? ≠ w[r1]?)
    (ht : t ≤ pc)
    (hcross : pc + (P + q1) ≤ t + r')
    (hrunj : HasPeriod ((w.drop t).take r') P)
    (hr'len : t + r' ≤ w.length)
    (hfitR : pc + (P + q1) ≤ Rc)
    (hhigh : r1 < pc + P) : RemainingGap P q1 r1 t := by
  by_contra hcon
  simp only [RemainingGap, not_or, Nat.not_lt] at hcon
  exact crossing_copy_contradiction hq1 hPpos hreg hRc hrun1 hbreak1 ht hcon.1 hcross
    hrunj hr'len hfitR hcon.2 hhigh

end PassSum11
end PalPeg

section AxiomCheck
#print axioms PalPeg.PassSum11.crossing_copy_contradiction
#print axioms PalPeg.PassSum11.cycling_contradiction
#print axioms PalPeg.PassSum11.gap_dichotomy
end AxiomCheck
