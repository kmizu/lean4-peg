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

数値実験（自己相似語 110,000 本、開始位置も乱択、子孫 **10,162 個**、seed 3 本）：

* 跨ぎ `L = E_j - p_c > 0` は **243 例、すべて `c` の直接の子**（間接の子孫は 0 例）。
* 「遅い」子孫（`t ≥ (k-1) * p_j`）は 862 個あるが、そのうち **跨ぐものは 0 個**。
* 跨ぎ量の最大は `L/p_j = 1.04`（旧 (E) `E_j < p_c + p_j` は僅かに偽）。
  `far_crossing_contradiction` が要求する `p_c + P ≤ r'` を満たす跨ぎは **0 例**、
  `crossing_copy_contradiction` が閉じる形は 243 例中 **192 例**、
  残り 51 例はすべて `r₁ < P + q₁`（`RemainingGap` の第 1 枝）で、
  第 2 枝 `r₁ < t + q₁` に落ちる例は **0 例**。
* `Consumption` の違反 `C - p_c ≥ 0` への最接近は **`-8`**（8 セル足りない）。
* 消費量比の最大は `C/p_c = 0.92`。

## 本ファイル後に残る穴

`far_crossing_contradiction`（§2）は `p_c + P ≤ r'` を**すべて**閉じるので、
`Consumption` の違反に残された形はただ一つ：

> **子孫 `j` の run が短い**：`r' < p_c + P`（`ShortRunGap`）。違反が要求する
> `L ≥ k*P - 1` の下でこれは `t ≥ (k-1) * P`（遅い節点）を**含意**する。
> 同値が証明されているのは閾値ちょうど `L + 1 = k*P` の場合のみ
> （`shortRun_iff_late`）。

すなわち `PassSum9` の `up_violation_early` は本ファイルの
`far_crossing_contradiction` に完全に含まれ、穴は「遅い UP 節点」1 個に一本化された。
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

/-! ## §2 遠い跨ぎ：run が `p_c + P` 以上あれば `c` の run 全体が `P`-周期になる

ここだけ座標を **節点 `c` の run の先頭 `a_c`** にとる（`v = x.drop a_c`）。
`c` の run `[0, rc)` は `p_c`-周期で `k * p_c ≤ rc`、`p_c` はこの位置の最小
`k`-繰り返し周期（`IsLeastKRep v k pc`）である。

子孫 `j` の run を `[s, s + r')`（`P`-周期、`s + r' ≤ rc`）とする。**`p_c + P ≤ r'`**
なら、窓の中に「`p_c` だけ離れた同じ位置」が必ず入るので、区間 `[0, s + r')` 全体が
`P`-周期になる（`v[i] = v[i + p_c]` を繰り返して窓の中へ運び、窓で `+P` し、戻す）。
Fine–Wilf も割り切りも要らない。

`s + r' ≥ k * P` なら `P` は `a_c` における `k`-繰り返し周期なので、最小性から
`p_c ≤ P`。`P < p_c` に矛盾する。

**被覆範囲**：領域座標で `E_j = t + r'`、`L = E_j - p_c` とすると
`p_c + P ≤ r'` は `t ≤ L - P` と同値。`Consumption` の違反は `L ≥ k * P - 1` を
要求するので、この定理は `t ≤ L - P` の全域を閉じる。とくに
`up_violation_early`（`t + 1 ≤ (k-1) * P`）は `L ≥ k*P - 1` の下で
`t ≤ (k-1)*P - 1 ≤ L - P` を満たすので、**本定理に含まれる**。
残るのは `r' < p_c + P`（＝ `E_j < p_c + t + P`、`t > L - P`）だけである。 -/

/-- **遠い跨ぎからの矛盾**。`c` の run（`p_c`-周期、最小 `k`-繰り返し周期 `p_c`）の
内側にある `P`-周期の窓 `[s, s + r')` が `p_c + P ≤ r'` を満たし、その右端が
`k * P` に達するなら、`p_c ≤ P` となって `P < p_c` に矛盾する。 -/
theorem far_crossing_contradiction {v : List α} {k pc P s r' rc : ℕ}
    (hleast : IsLeastKRep v k pc) (hR : ReachOf v pc rc)
    (hPpos : 0 < P) (hPlt : P < pc)
    (hrunj : HasPeriod ((v.drop s).take r') P)
    (hself : pc + P ≤ r') (hfit : s + r' ≤ rc) (hkP : k * P ≤ s + r') : False := by
  have hrcv : rc ≤ v.length := hR.1
  have hreg : HasPeriod (v.take rc) pc := hR.2.1
  have hpcpos : 0 < pc := hleast.1.1
  have hreglen : (v.take rc).length = rc := by rw [List.length_take]; omega
  have hregion : ∀ i, i + pc < rc → v[i]? = v[i + pc]? := by
    intro i hi
    have h := hreg i (by rw [hreglen]; exact hi)
    rwa [List.getElem?_take_of_lt (show i < rc by omega),
      List.getElem?_take_of_lt (show i + pc < rc by omega)] at h
  have hdroplen : (v.drop s).length = v.length - s := by simp
  have hwindow : ∀ m, m + P < r' → v[s + m]? = v[s + m + P]? := by
    intro m hm
    have h := hrunj m (by rw [List.length_take, hdroplen]; omega)
    rw [List.getElem?_take_of_lt (show m < r' by omega),
      List.getElem?_take_of_lt (show m + P < r' by omega),
      List.getElem?_drop, List.getElem?_drop] at h
    rw [show s + m + P = s + (m + P) from by omega]
    exact h
  -- `p_c` ずつ右へ運んで窓の中に入れる
  have key : ∀ n i, s ≤ i + n → i + P < s + r' → v[i]? = v[i + P]? := by
    intro n
    induction n with
    | zero =>
      intro i hs hi
      have h := hwindow (i - s) (by omega)
      rwa [show s + (i - s) = i from by omega] at h
    | succ n ih =>
      intro i hs hi
      by_cases hcase : s ≤ i
      · have h := hwindow (i - s) (by omega)
        rwa [show s + (i - s) = i from by omega] at h
      · have h1 : v[i]? = v[i + pc]? := hregion i (by omega)
        have h2 : v[i + P]? = v[i + P + pc]? := hregion (i + P) (by omega)
        have h3 := ih (i + pc) (by omega) (by omega)
        rw [h1, h2, show i + P + pc = i + pc + P from by omega]
        exact h3
  have hper : HasPeriod (v.take (s + r')) P := by
    intro i hi
    rw [List.length_take] at hi
    rw [List.getElem?_take_of_lt (show i < s + r' by omega),
      List.getElem?_take_of_lt (show i + P < s + r' by omega)]
    exact key s i (by omega) (by omega)
  have hkrep : KRep v k P := ⟨hPpos, by omega, hasPeriod_take_of_le hper (by omega)⟩
  exact absurd (hleast.2 P hkrep) (by omega)

/-- 系（領域座標）：`E_j = t + r'`、`L = E_j - p_c` としたとき、違反が要求する
`k * P ≤ E_j`（絶対座標）と `t ≤ L - P` から矛盾。`s = d + t` は領域先頭 `d` からの
オフセットで、`d + k * p_c = rc + 1`。 -/
theorem far_crossing_region {v : List α} {k pc P d t r' rc : ℕ}
    (hleast : IsLeastKRep v k pc) (hR : ReachOf v pc rc)
    (hPpos : 0 < P) (hPlt : P < pc)
    (hrunj : HasPeriod ((v.drop (d + t)).take r') P)
    (_hd : d + k * pc = rc + 1)
    (hfar : pc + P ≤ r') (hfit : d + t + r' ≤ rc) (hkP : k * P ≤ d + t + r') : False :=
  far_crossing_contradiction hleast hR hPpos hPlt hrunj hfar (by omega) hkP

/-- **残る穴の明示**（`crossing_copy_contradiction` 側）。コピー論法で閉じられない
配置は「コピーが取れない (`r₁ < P + q₁`)」か「着地が第 1 子の破れの直前 `q₁` セル
以内 (`r₁ < t + q₁`)」のいずれかである。 -/
def RemainingGap (P q1 r1 t : ℕ) : Prop := r1 < P + q1 ∨ r1 < t + q1

/-- **本ファイル後に残る穴（最終形）**。`far_crossing_contradiction` は
`p_c + P ≤ r'` の全域を閉じるので、`Consumption` の違反に残された唯一の形は

> 子孫 `j` の run が短い：`r' < p_c + P`（領域座標で `E_j < p_c + t + P`、
> すなわち跨ぎ量 `L = E_j - p_c` に対して `t > L - P`）

である。違反は `L ≥ k * P - 1` を要求するので、これは
`t > (k-1) * P - 1`、つまり「遅い節点」を含意する。逆向きは一般には
従わず、次の同値定理は閾値ちょうどの場合に限定される。 -/
def ShortRunGap (pc P r' : ℕ) : Prop := r' < pc + P

/-- 遅さと短さの同値（違反の閾値 `L = k*P - 1` を代入した形）。 -/
theorem shortRun_iff_late {k pc P t L r' : ℕ} (hk : 4 ≤ k) (_hPpos : 0 < P)
    (hEj : t + r' = pc + L) (hviol : k * P ≤ L + 1) (hL : L + 1 ≤ k * P) :
    ShortRunGap pc P r' ↔ (k - 1) * P ≤ t := by
  have h1 : (k - 1) * P + P = k * P := by rw [← Nat.succ_mul]; congr 1; omega
  constructor <;> intro h <;> simp only [ShortRunGap] at * <;> omega

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
#print axioms PalPeg.PassSum11.far_crossing_contradiction
#print axioms PalPeg.PassSum11.far_crossing_region
#print axioms PalPeg.PassSum11.gap_dichotomy
#print axioms PalPeg.PassSum11.shortRun_iff_late
end AxiomCheck
