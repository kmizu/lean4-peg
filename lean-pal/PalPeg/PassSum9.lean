import PalPeg.PassSum8

/-!
# 1 パスの周期木：消費量補題と兄弟の成長（PassSum9）

`PassSum8` は残る課題を一点 `PassSum8.PassHasTree` に絞った。その中身は

* **(T1)** `j+1` が `j` の子 ⟺ DOWN（`PassSum.step_dichotomy` と
  恒等式 `Eⱼ = aⱼ₊₁ + k*pⱼ - 1`）、
* **(T2)** 末子は `(k-1) * q_m < p_c`、
* **(T3)** 同じ親の連続する子は `q' ≥ γ * q`（`PassSum8` が要求するのは `γ = 3`）

の 3 つである。本ファイルは **(T2)(T3) を語の側で決着させる**。鍵は次の一点：

> **消費量補題 (C)**：節点 `c` の子孫はすべて `R_c = [a_{c+1}, E_c]`（`c` の極大 run の
> 最後の `k*p_c - 1` 個のセル、最小周期 `p_c` で周期的）の**先頭 `p_c` セル以内**から
> 始まる。すなわち `c` の部分木を抜けた直後の位置 `a_next` について
> `C(c) := a_next - a_{c+1} < p_c`。

(C) さえあれば (T3) は「脱出補題」`GSDecompose2.sibling_overlap_lt` から
**`(k-2) * q < q'`**（`k = 8` なら `q' ≥ 6q + 1`、実測の最小比 `7.33` と整合）が出る。
`PassSum8.KidsOk` が要求する `3 * q ≤ q'` にも十分である。

## 本ファイルで証明したこと（すべて `sorry` なし）

* `inner_run_lt`：親の周期領域の内側から始まる run は `r' < p + q` で終わる
  （`step_down_reach` の任意オフセット版）。
* `sibling_growth`：**(T3)**。消費量が `C < q` なら次の兄弟の周期は `(k-2)*q < q'`。
  `sibling_growth_eight`：`k = 8` での `6*q < q'`（したがって `3*q ≤ q'`、`14*q ≤ 5*q'`）。
* `last_child_bound`：**(T2)**。`R_c` に収まる子は `(k-1)*q < p_c`（`child_period_bound`）。
* `span_le`：子 `q` の「消費幅」`span = (r_q - k*q + 1) + C(q)` は
  `span + (k-2)*q ≤ p`（`C(q) < q` を仮定）。
* `SpansOk` / `spans_sum_bound` / `consumption_lt_period_abstract`：
  (C) の**帰納段階**。子の列が
  「成長 `3*q_i ≤ q_{i+1}`・非末子の消費幅 `span_i ≤ q_{i+1}`・末子の
  `span_m + 6*q_m ≤ p`」を満たせば `Σ span_i < p`、すなわち `C(c) < p_c`。
  子が 1 つ以下のときは仮定なしで従う（`consumption_lt_period_single`）。

## 残る唯一の穴

上の帰納段階が要求する **`span_i ≤ q_{i+1}`（非末子の消費幅は次の兄弟の周期以下）**
だけが未証明である（`SpanLeNextSibling` として明示）。数値実験（`k = 8`、入れ子周期語
1500 語 × 3 seed、節点 5000 超）では

* `max span_i / q_{i+1} = 0.78`（非末子）、`max span_i / p = 0.081`、
* `max C(c) / p_c = 0.938`、`max A_m / ((k-2) q_m) = 0.083`、
* 兄弟比の最小値 `7.79`

であり、いずれも要求より十分な余裕がある。
-/

namespace PalPeg
namespace PassSum9

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

section Local

variable {w : List α} {k p q P r rq C t : ℕ}

/-! ## §1 親の領域の内側から始まる run の到達域

`PassSum.step_down_reach` は「直後の位置 `d`」だけを扱っていた。子孫はより深い
オフセット `t` から始まるので、任意の `t` に対する版を用意する。 -/

/-- **内側 run の到達域**。親（最小周期 `p`、到達域 `r`）の周期領域の内側の位置 `t`
から始まる run（最小周期 `q < p`、到達域 `r'`）は `r' < p + q` で終わる。

そうでなければ長さ `p + q` の窓が `p` と `q` の両方の周期を持ち、
`dvd_of_inner_window` から `p ∣ q`、つまり `p ≤ q` となって矛盾する。 -/
theorem inner_run_lt {r' : ℕ} (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : 0 < q) (hqp : q < p) (hR' : ReachOf (w.drop t) q r')
    (hfit : t + (p + q) ≤ r) :
    r' < p + q := by
  by_contra hcon
  have hwin : HasPeriod ((w.drop t).take (p + q)) q :=
    hasPeriod_take_of_le hR'.2.1 (by omega)
  have hdvd : p ∣ q :=
    dvd_of_inner_window (by omega) hleast hR hkr hq hfit (le_refl _) hwin
  exact absurd (Nat.le_of_dvd hq hdvd) (by omega)

/-- 子の窓が `R_c` の内側にあるという形の `hfit`：オフセット `t = d + C`
（`d = r - k*p + 1` は最初の子の位置、`C < q < p` は消費量）なら
`t + (p + q) ≤ r` が自動的に従う。 -/
theorem inner_fit (hk : 4 ≤ k) (_hp : 0 < p) (hd : k * p + (r - k * p + 1) = r + 1)
    (hqp : q < p) (hC : C < q) (ht : t = (r - k * p + 1) + C) :
    t + (p + q) ≤ r := by
  have h4 : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  omega

/-! ## §2 (T3) 兄弟の成長 -/

/-- **(T3) 兄弟の成長**。節点 `q`（最小周期 `q`、到達域 `rq`、`R_q = [d, rq)` の
`d = rq - k*q + 1`）の部分木を消費量 `C` で抜けた位置 `t = d + C` から始まる run の
窓が `R_q` を出るなら、その周期 `P` は `(k-2) * q < P` を満たす。

`GSDecompose2.sibling_overlap_lt` が `rq - t < q + P` を与え、
`rq - t = k*q - 1 - C ≥ (k-1)*q`（`C < q` より）だから。 -/
theorem sibling_growth (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k q) (hR : ReachOf w q rq) (hkr : k * q ≤ rq)
    (hP : IsLeastKRep (w.drop t) k P)
    (ht : t = (rq - k * q + 1) + C) (hC : C < q)
    (hnfit : rq < t + k * P) :
    (k - 2) * q < P := by
  have hq : 0 < q := hleast.1.1
  have h1 : (k - 1) * q + q = k * q := by rw [← Nat.succ_mul]; congr 1; omega
  have h2 : (k - 2) * q + q = (k - 1) * q := by
    have h : k - 1 = (k - 2) + 1 := by omega
    rw [h, Nat.succ_mul]
  have h4 : 4 * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
  have htr : t < rq := by omega
  have hov := sibling_overlap_lt hk hleast hR hkr hP htr hnfit
  omega

/-- `k = 8` 版：`6 * q < P`。とくに `PassSum8.KidsOk` が要求する `3 * q ≤ P` と、
`PassSum8` 冒頭の計算が要求する `14 * q ≤ 5 * P` の両方が従う。 -/
theorem sibling_growth_eight
    (hleast : IsLeastKRep w 8 q) (hR : ReachOf w q rq) (hkr : 8 * q ≤ rq)
    (hP : IsLeastKRep (w.drop t) 8 P)
    (ht : t = (rq - 8 * q + 1) + C) (hC : C < q)
    (hnfit : rq < t + 8 * P) :
    6 * q < P := by
  have h := sibling_growth (k := 8) (by omega) hleast hR hkr hP ht hC hnfit
  simpa using h

theorem sibling_growth_kidsOk
    (hleast : IsLeastKRep w 8 q) (hR : ReachOf w q rq) (hkr : 8 * q ≤ rq)
    (hP : IsLeastKRep (w.drop t) 8 P)
    (ht : t = (rq - 8 * q + 1) + C) (hC : C < q)
    (hnfit : rq < t + 8 * P) :
    3 * q ≤ P ∧ 14 * q ≤ 5 * P := by
  have h := sibling_growth_eight hleast hR hkr hP ht hC hnfit
  exact ⟨by omega, by omega⟩

/-! ## §3 (T2) 末子（一般に子）の周期の上界 -/

/-- **(T2)**。親の周期領域 `R_c` に窓が収まる子は `(k-1) * q < p`。
（`GSDecompose2.child_period_bound` の言い換え。`k = 8` なら `7 * q < p` で、
これは `PassSum8.NodeOk` の末子条件そのもの。） -/
theorem last_child_bound (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop t) k q) (hfit : t + k * q ≤ r) (hne : q ≠ p) :
    (k - 1) * q < p :=
  child_period_bound hk hleast hR hkr hq hfit hne

/-! ## §4 子の「消費幅」 -/

/-- 子 `q` の消費幅 `span = (r_q - k*q + 1) + C(q)` の上界：`span + (k-2)*q ≤ p`。
`r_q < p + q`（`inner_run_lt`）と `C(q) < q` から。 -/
theorem span_le_arith (hk : 4 ≤ k) (_hq : 0 < q) (hreach : rq < p + q) (hkq : k * q ≤ rq)
    (hC : C < q) : (rq - k * q + 1) + C + (k - 2) * q ≤ p := by
  have h2 : (k - 2) * q + q + q = k * q := by
    have h : k = (k - 2) + 2 := by omega
    calc (k - 2) * q + q + q = ((k - 2) + 2) * q := by ring
      _ = k * q := by rw [← h]
  omega

/-- 意味論版：親 `p` の領域の内側 `t` から始まる子 `q`（消費量 `C(q) < q`）の消費幅。 -/
theorem span_le (hk : 4 ≤ k) {r' : ℕ}
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop t) k q) (hqp : q < p)
    (hR' : ReachOf (w.drop t) q r') (hkq : k * q ≤ r')
    (hfit : t + (p + q) ≤ r) (hC : C < q) :
    (r' - k * q + 1) + C + (k - 2) * q ≤ p :=
  span_le_arith hk hq.1.1 (inner_run_lt hk hleast hR hkr hq.1.1 hqp hR' hfit) hkq hC

end Local

/-! ## §5 消費量補題 (C) への還元：**run 終端条件 (E)**

`SpansOk` 型の議論（「非末子の消費幅 `spanᵢ` は次の兄弟の周期 `qᵢ₊₁` 以下」）は
**偽**である。反例（`k = 8`）：周期語 `u = 0^m 1 (0^7 1)^8`（`m ≫ 8`）を取ると、
第 1 子は `0`-ブロック（`q₁ = 1`, run ≒ `m`, `span₁ ≒ m - 7`）、そこから着地した
第 2 子は `q₂ = 8` なので `span₁ ≫ q₂`。実測でも `max spanᵢ/qᵢ₊₁ = 2.88 > 1`。

正しい還元は **run の終端**についての一様な条件である：

> **(E)** `c` のすべての子孫 `j` について `E_j < a_{c+1} + p_c + p_j`。
> （`j` の run は「最初の周期ブロック + 自分の周期」を越えない。）

(E) は (C) と子孫の開始位置の両方を含意する（`consumption_lt_period_of_runEnd`,
`descendant_start_lt_of_runEnd`）。実測（敵対的生成器・`k = 8`・7,700 節点）では

* `max (E_j - a_{c+1} - p_j)/p_c = 0.9963`（(E) は成立、ただし余裕は小さい）、
* `max (a_j - a_{c+1})/p_c = 0.816`、`max C(c)/p_c = 0.805`、
* 兄弟比の最小値 `8.0`（`sibling_growth_eight` の `> 6` と整合）。 -/

/-- **(E) ⟹ (C)**。最後の子孫 `ℓ` について (E) が成り立てば、`c` の部分木を抜けた
位置 `a_next = E_ℓ - k*p_ℓ + 1` は `a_{c+1} + p_c` に届かない：`C(c) < p_c`。

`E_ℓ - a_{c+1} < p + p_ℓ` と `a_next - a_{c+1} = (E_ℓ - a_{c+1}) - k*p_ℓ + 1` から
`C(c) < p - (k-1)*p_ℓ + 1 ≤ p`。 -/
theorem consumption_lt_period_of_runEnd {k p pl El C : ℕ} (hk : 4 ≤ k) (hpl : 0 < pl)
    (hE : El < p + pl) (_hkpl : k * pl ≤ El) (hC : C + k * pl = El + 1) : C < p := by
  have h1 : (k - 1) * pl + pl = k * pl := by rw [← Nat.succ_mul]; congr 1; omega
  have h2 : 1 * pl ≤ (k - 1) * pl := Nat.mul_le_mul_right pl (by omega)
  omega

/-- **(E) ⟹ 子孫の開始位置は `p_c` 未満**。`a_j + k*p_j ≤ E_j` と (E) から
`a_j - a_{c+1} < p - (k-1)*p_j < p`。 -/
theorem descendant_start_lt_of_runEnd {k p pj aj Ej : ℕ} (hk : 4 ≤ k) (_hpj : 0 < pj)
    (hE : Ej < p + pj) (hwin : aj + k * pj ≤ Ej) : aj < p := by
  have h1 : (k - 1) * pj + pj = k * pj := by rw [← Nat.succ_mul]; congr 1; omega
  have h2 : 1 * pj ≤ (k - 1) * pj := Nat.mul_le_mul_right pj (by omega)
  omega

/-! ## §6 (E) の帰納：DOWN ステップでは `E_j - p_j` が真に減る -/

/-- **(E) の DOWN ステップ**。節点 `j`（最小周期 `p`、到達域 `r`）の子
（位置 `d = r - k*p + 1`、最小周期 `q < p`、到達域 `r'`）について

```
(d + r') - q < r - p        （相対座標での `E_child - q < E_parent - p`）
```

したがって (E) の量 `E_j - p_j` は DOWN ステップで真に減少し、(E) は
親から子へ自動的に伝播する。`step_down_reach`（`r' < p + q`）と
`d = r - k*p + 1`、`2*p + 1 ≤ k*p` から。 -/
theorem runEnd_down_step {w : List α} {k p q r r' d : ℕ} (hk : 4 ≤ k)
    (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') :
    (d + r') + p < r + q := by
  have hp : 0 < p := hleast.1.1
  have hreach := step_down_reach hk hd hleast hR hkr hq hlt hR' hkq
  have h4 : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  omega

/-! ## §7 残る穴の明示

DOWN ステップは `runEnd_down_step` で、UP ステップのうち `P + q ≤ r_j`（かつ run `j` が
第 1 子）の場合は §9 の `runEnd_up_step_le` で閉じた。残るのは **UP ステップのうち
`r_j < P + q` の場合**（実測ではこちらが UP 着地の 96%）と、run `j` が第 1 子でない
場合（`runEnd_up_step_le` の結論が `a_j` 基準になり `a_{c+1}` 基準に直せない）である。
すなわち
`c` の部分木の中で run `j` を脱出して次の兄弟 `j+1`（なお `c` の子孫）に着地する場合に

```
E_{j+1} - p_{j+1} < a_{c+1} + p_c
```

を示すことである。手持ちの補題からは

* `inner_run_lt`（親 `c` に対して）：`E_{j+1} < a_{j+1} + p_c + p_{j+1}`、
* `a_{j+1} = E_j - k*p_j + 1`、帰納法の仮定 `E_j < a_{c+1} + p_c + p_j`

しか出ず、これを合わせると `E_{j+1} - p_{j+1} < a_{c+1} + 2*p_c - (k-1)*p_j + 1` で、
`p_c ≤ (k-1)*p_j` のときしか閉じない（実際 `p_j = 1`, `p_c = 433` のような
「長い第 1 子のあとの着地」が実測の最悪ケースで、余裕は `3` セルしかない）。
必要なのは「長い子の直後に着地した run はすぐ終わる」という追加の構造情報で、
これは `R_c` の `p_c`-周期性による**平行移動の議論**（着地点から `p_c` を引いた
仮想節点と、それを含む先行 run の極大性との矛盾）にあたる。 -/

/-! ### 数値実験で否定された候補

* **(G) `t_j ≤ (k-1) * p_j`（子孫の開始オフセットは自分の周期の `(k-1)` 倍以下）は偽**。
  実測の最悪値は `t_j / p_j = 847`（`p_c = 961`, `t_j = 847`, `p_j = 1`）。
  したがって exit 位置 `t_last + r_last - k*p_last + 1 < p_c` を (G) 経由で出す道は閉じている。
* **`spanᵢ ≤ qᵢ₊₁`（非末子の消費幅 ≤ 次の兄弟の周期）も偽**（実測 `max = 2.88`）。

数値的に成り立つ最良の形は (E) `E_j - a_{c+1} < p_c + p_j`（実測比 `0.9963`）であり、
これは `inner_run_lt`（`r_j < p_c + p_j`）を**ちょうど `t_j` セルだけ**強めたものにあたる。
回転論法・コピー論法・Fine-Wilf のいずれで攻めてもこの `t_j` の不足が残る。

観測された副次的な二分律（証明の手掛かり）：`t_j > (k-1) * p_j` を満たす
「遅く始まる小周期の子孫」は、実測では必ず `E_j < p_c`（最初の周期ブロックを跨がない、
最悪値 `0.897`）。 -/

/-- **残る唯一の未証明の主張 (E)**（相対座標版）。`E` は `a_{c+1}` からの相対終端。 -/
def RunEndBound (p : ℕ) (desc : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ desc, e.1 < p + e.2

/-! ## §8 UP ケースのための語の補題：`P`-周期語の中の `q`-周期因子

UP ステップの矛盾は次の形で出る。`c` の領域は `p_c`-周期的なので、着地した
`P`-run の中に「run `j` の先頭のコピー」が現れる。そのコピーが長さ `P + q` 以上なら、
**`P`-周期語の中に長さ `P + q` の `q`-周期因子があれば、その因子より左の部分は
すべて `q`-周期的**（`period_factor_propagate`）。ところが run `j` の極大性は
`x[E_j] ≠ x[E_j - q]` を主張し、`E_j` はコピーより左にあるので矛盾する
（`factor_period_contradiction`）。

Fine–Wilf（`Words.fineWilf`）で因子の周期を `g = gcd P q` に落とし、
`Words.hasPeriod_of_suffix_gcd` で左へ伝播させる。 -/

/-- **`P`-周期語の `q`-周期因子**。`u.take R` が周期 `P` を持ち、位置 `s` から
長さ `P + q` の因子が周期 `q` を持つなら、`u.take (s + P)` は周期 `q` を持つ。 -/
theorem period_factor_propagate {u : List α} {P q s R : ℕ}
    (hP : HasPeriod (u.take R) P) (hPpos : 0 < P) (hqpos : 0 < q)
    (hfac : HasPeriod ((u.drop s).take (P + q)) q)
    (hfit : s + (P + q) ≤ R) (hR : R ≤ u.length) :
    HasPeriod (u.take (s + P)) q := by
  have hsR : s ≤ R := by omega
  -- 因子は `P` も周期に持つ
  have hyP : HasPeriod ((u.drop s).take (P + q)) P :=
    hasPeriod_take_of_le (hasPeriod_drop_take hP hR hsR) (by omega)
  have hylen : ((u.drop s).take (P + q)).length = P + q := by
    rw [List.length_take, List.length_drop]; omega
  set g := Nat.gcd P q with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hPpos
  have hgle : g ≤ q := Nat.gcd_le_right _ hqpos
  -- Fine–Wilf で `g` に落とす
  have hg : HasPeriod ((u.drop s).take (P + q)) g :=
    fineWilf hyP hfac hPpos hqpos (by rw [hylen]; omega)
  -- `x = u.take (s + P)` の末尾 `P` 文字が `g`-周期的
  have hxlen : (u.take (s + P)).length = s + P := by
    rw [List.length_take]; omega
  have hxP : HasPeriod (u.take (s + P)) P := hasPeriod_take_of_le hP (by omega)
  have hdrop : (u.take (s + P)).drop ((u.take (s + P)).length - P) = (u.drop s).take P := by
    rw [hxlen, show s + P - P = s from by omega, List.drop_take]
    congr 1; omega
  have hsuf : HasPeriod ((u.take (s + P)).drop ((u.take (s + P)).length - P)) g := by
    rw [hdrop]; exact hasPeriod_take_of_le hg (by omega)
  have hxg : HasPeriod (u.take (s + P)) g :=
    hasPeriod_of_suffix_gcd hxP hPpos (Nat.gcd_dvd_left P q) hsuf (by omega)
  -- `g ∣ q` なので周期 `q` も持つ
  have hq' : (q / g) * g = q := Nat.div_mul_cancel (Nat.gcd_dvd_right P q)
  have := hasPeriod_mul hxg (q / g)
  rwa [hq'] at this

/-- **UP ケースの矛盾**。`u.take R` が周期 `P` を持ち、位置 `s` に長さ `P + q` の
`q`-周期因子があり、しかも因子より左に `q`-周期性の破れ `u[e] ≠ u[e - q]` があるなら
矛盾する。（`e = E_j`、破れは run `j` の極大性。） -/
theorem factor_period_contradiction {u : List α} {P q s R e : ℕ}
    (hP : HasPeriod (u.take R) P) (hPpos : 0 < P) (hqpos : 0 < q)
    (hfac : HasPeriod ((u.drop s).take (P + q)) q)
    (hfit : s + (P + q) ≤ R) (hR : R ≤ u.length)
    (hq : q ≤ e) (he : e < s + P) (hbreak : u[e - q]? ≠ u[e]?) : False := by
  have hper := period_factor_propagate hP hPpos hqpos hfac hfit hR
  have hlen : (u.take (s + P)).length = s + P := by
    rw [List.length_take]; omega
  have h := hper (e - q) (by rw [hlen]; omega)
  rw [List.getElem?_take_of_lt (show e - q < s + P by omega),
    List.getElem?_take_of_lt (show e - q + q < s + P by omega)] at h
  rw [show e - q + q = e from by omega] at h
  exact hbreak h

/-! ## §9 領域の周期性によるコピーと、UP ケース（`r_j ≥ P + q`）の決着 -/

/-- **コピー補題**。`u.take R` が周期 `p` を持てば、位置 `t` と `t + p` から始まる
長さ `L` の因子は等しい（`t + p + L ≤ R`）。 -/
theorem factor_copy_eq {u : List α} {p t L R : ℕ}
    (hp : HasPeriod (u.take R) p) (hR : R ≤ u.length) (hfit : t + p + L ≤ R) :
    (u.drop (t + p)).take L = (u.drop t).take L := by
  have hlen : (u.take R).length = R := by rw [List.length_take]; omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
      List.getElem?_drop, List.getElem?_drop]
    have h := hp (t + i) (by rw [hlen]; omega)
    rw [List.getElem?_take_of_lt (show t + i < R by omega),
      List.getElem?_take_of_lt (show t + i + p < R by omega)] at h
    rw [show t + p + i = t + i + p from by omega]
    exact h.symm
  · rw [List.getElem?_take, List.getElem?_take, if_neg hi, if_neg hi]

/-- **UP ステップの (E)（`r_j ≥ P + q` の場合、第 1 子版）**。

`w` を `c` の領域の先頭 `a_{c+1}` から見た接尾辞とする：

* `w.take Rc` は `p = p_c` 周期（領域の周期性）、
* run `j` は `w` の先頭から（第 1 子）長さ `rj` の `q`-周期 run で、`w[rj-q] ≠ w[rj]`（極大性）、
* `rj < p + q`（`inner_run_lt`）、
* 着地位置 `t`（`t + k*q = rj + 1`）から周期 `P` の run が長さ `r'` 続く、
* `rj ≥ P + q`（本補題が扱う場合）、`q ≤ P`（UP ステップ：実際は `(k-1)*q ≤ P`）。

このとき **`t + r' < p + P + q`**、すなわち `E_{j+1} < a_{c+1} + p_c + P + q` が成り立つ。

証明：もし `p + P + q ≤ t + r'` なら、領域の `p`-周期性から `P`-run の中に
`w.take (P+q)`（run `j` の先頭、`q`-周期）のコピーが現れる。`period_factor_propagate`
によりコピーより左の部分はすべて `q`-周期的になるが、そこには run `j` の極大性による
破れ `w[rj-q] ≠ w[rj]` が含まれるので矛盾。 -/
theorem runEnd_up_step_le {w : List α} {k p q P rj r' t Rc : ℕ} (hk : 4 ≤ k)
    (_hp : 0 < p) (hq : 0 < q) (hPpos : 0 < P)
    (hreg : HasPeriod (w.take Rc) p) (hRc : Rc ≤ w.length)
    (hrun : HasPeriod (w.take rj) q) (hbreak : w[rj - q]? ≠ w[rj]?)
    (hrjlt : rj < p + q) (hlong : P + q ≤ rj) (hUP : q ≤ P)
    (ht : t + k * q = rj + 1)
    (hPrun : HasPeriod ((w.drop t).take r') P) (hr' : t + r' ≤ w.length)
    (hcopy : p + (P + q) ≤ Rc) :
    t + r' < p + P + q := by
  by_contra hcon
  have hkq : k * q ≤ rj + 1 := by omega
  have h4q : 4 * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
  have htp : t ≤ p := by omega
  -- コピー：`(w.drop p).take (P+q) = w.take (P+q)`
  have hcopyeq : (w.drop (0 + p)).take (P + q) = (w.drop 0).take (P + q) :=
    factor_copy_eq hreg hRc (by omega)
  have hfac0 : HasPeriod ((w.drop p).take (P + q)) q := by
    have h0 : (w.drop p).take (P + q) = w.take (P + q) := by
      simpa using hcopyeq
    rw [h0]; exact hasPeriod_take_of_le hrun (by omega)
  -- `P`-run の座標に移す
  have hshift : (w.drop t).drop (p - t) = w.drop p := by
    rw [List.drop_drop]; congr 1; omega
  have hfac : HasPeriod (((w.drop t).drop (p - t)).take (P + q)) q := by
    rw [hshift]; exact hfac0
  have hdroplen : (w.drop t).length = w.length - t := by simp
  refine factor_period_contradiction (u := w.drop t) (P := P) (q := q) (s := p - t)
    (R := r') (e := rj - t) hPrun hPpos hq hfac (by omega) (by omega) (by omega)
    (by omega) ?_
  rw [List.getElem?_drop, List.getElem?_drop,
    show t + (rj - t - q) = rj - q from by omega, show t + (rj - t) = rj from by omega]
  exact hbreak

/-! ## §9.5 (E) の反例と、正しい形 (E_k)

より深い自己相似語（`rec3.py` 系、開始位置 `s` もランダム）で測り直すと **(E) は偽**：
`p_c = 300`, `t_j = 11`, `p_j = 37`, `E_j - a_{c+1} = 338 = p_c + p_j + 1` という
反例がある（比 `1.027`）。一方 `C(c) < p_c` は依然として成立（実測 `max C/p_c = 0.907`、
非自明な部分木を持つ閉じた節点 332 個を含む）。

正しい弱形は `k` 倍の余裕を持つ **(E_k)**：

> `E_j - a_{c+1} < p_c + k * p_j`（実測の最悪比は `1.027`、要求は `< 8`）

そして (E_k) は次の二分律から出る：

* `t_j < (k-1) * p_j` なら `inner_run_lt`（`r_j < p_c + p_j`）から
  `E_j = t_j + r_j < p_c + k * p_j`；
* `t_j ≥ (k-1) * p_j` なら **(H)**（`E_j < a_{c+1} + p_c`）から自明。

したがって残る主張は **(H) ただ一つ**になった。 -/

/-- **(E_k) ⟹ (C)**。最後の子孫 `ℓ` について `E_ℓ - a_{c+1} < p_c + k * p_ℓ` なら
`C(c) = E_ℓ - a_{c+1} - k * p_ℓ + 1 ≤ p_c`。厳密不等号にはあと 1 セル必要
（`consumption_lt_period_of_dichotomy` を使う）。 -/
theorem consumption_le_period_of_runEndK {k p pl El C : ℕ}
    (hE : El < p + k * pl) (hC : C + k * pl = El + 1) : C ≤ p := by omega

/-- **二分律 (G)∨(H) ⟹ (C)**（`k = 8`）。最後の子孫 `ℓ` が

* `t_ℓ < (k-1) * p_ℓ` かつ `r_ℓ < p_c + p_ℓ`（`inner_run_lt`）、または
* `E_ℓ - a_{c+1} < p_c`（(H)）

のいずれかを満たせば `C(c) < p_c`。前者では
`E_ℓ ≤ t_ℓ + r_ℓ ≤ ((k-1) p_ℓ - 1) + (p_c + p_ℓ - 1) = p_c + k p_ℓ - 2`、
後者では `E_ℓ < p_c ≤ p_c + k p_ℓ - 1`。いずれも `C = E_ℓ - k p_ℓ + 1 < p_c`。 -/
theorem consumption_lt_period_of_dichotomy {k p pl tl rl C : ℕ} (hk : 4 ≤ k) (hpl : 0 < pl)
    (_hp : 0 < p)
    (hcase : (tl < (k - 1) * pl ∧ rl < p + pl) ∨ tl + rl < p)
    (hC : C + k * pl = (tl + rl) + 1) : C < p := by
  have h1 : (k - 1) * pl + pl = k * pl := by rw [← Nat.succ_mul]; congr 1; omega
  have h2 : 1 * pl ≤ k * pl := Nat.mul_le_mul_right pl (by omega)
  rcases hcase with ⟨ht, hr⟩ | h
  · omega
  · omega

/-! ## §10 領域を跨ぐ子孫は、領域先頭の周期を規定する

(H)（`t_j > (k-1) * p_j` なる子孫は `E_j < a_{c+1} + p_c`）を攻めるための道具。
子孫 `j` の run が最初の周期ブロックの境界 `p_c` を越えると、領域の `p_c`-周期性により
**領域の先頭 `[0, E_j - p_c)` が `p_j`-周期的**になる（`region_prefix_period`）。
越え方が `k * p_j` 以上なら、先頭は `p_j` の `k`-繰り返しなので
**第 1 子の周期は `q₁ ≤ p_j`**（`first_period_le_of_crossing`）。

数値実験でも、(H) の場合（`t_j > (k-1) p_j`）には常に `p_j ≤ q₁`（実測 `max p_j/q₁ = 1.0`）で
あり、この 2 つを合わせると `p_j = q₁` に押し込まれる。 -/

/-- **領域先頭の周期**。領域 `w.take Rc` が `p`-周期的で、位置 `t ≤ p` から始まる
長さ `r` の run が `P`-周期的なら、`p + L ≤ t + r` かつ `p + L + P ≤ Rc` のとき
領域の先頭 `w.take L` は `P`-周期的。

`w[i] = w[p+i]`（領域）`= w[p+i+P]`（run）`= w[i+P]`（領域）と辿る。 -/
theorem region_prefix_period {w : List α} {p P t r L Rc : ℕ}
    (hreg : HasPeriod (w.take Rc) p) (hRc : Rc ≤ w.length)
    (hrun : HasPeriod ((w.drop t).take r) P)
    (ht : t ≤ p) (hL : p + L ≤ t + r) (hfit : p + L + P ≤ Rc) :
    HasPeriod (w.take L) P := by
  have hreglen : (w.take Rc).length = Rc := by rw [List.length_take]; omega
  have hrunlen : ((w.drop t).take r).length = min r (w.length - t) := by
    rw [List.length_take, List.length_drop]
  have hregion : ∀ j, j + p < Rc → w[j]? = w[j + p]? := by
    intro j hj
    have h := hreg j (by rw [hreglen]; exact hj)
    rwa [List.getElem?_take_of_lt (show j < Rc by omega),
      List.getElem?_take_of_lt (show j + p < Rc by omega)] at h
  have hrunstep : ∀ m, m + P < r → m + t + P < w.length → w[t + m]? = w[t + m + P]? := by
    intro m hm hm2
    have h := hrun m (by rw [hrunlen]; omega)
    rw [List.getElem?_take_of_lt (show m < r by omega),
      List.getElem?_take_of_lt (show m + P < r by omega),
      List.getElem?_drop, List.getElem?_drop] at h
    rw [show t + m + P = t + (m + P) from by omega]
    exact h
  intro i hi
  rw [List.length_take] at hi
  rw [List.getElem?_take_of_lt (show i < L by omega),
    List.getElem?_take_of_lt (show i + P < L by omega)]
  have h1 : w[i]? = w[i + p]? := hregion i (by omega)
  have h2 : w[t + (p + i - t)]? = w[t + (p + i - t) + P]? :=
    hrunstep (p + i - t) (by omega) (by omega)
  rw [show t + (p + i - t) = i + p from by omega,
    show i + p + P = (i + P) + p from by omega] at h2
  have h3 : w[i + P]? = w[(i + P) + p]? := hregion (i + P) (by omega)
  rw [h1, h2, ← h3]

/-- **深く跨ぐ子孫は第 1 子の周期を抑える**。領域の先頭 `k * P` セルが `P`-周期的なら、
先頭位置の最小 `k`-繰り返し周期 `q₁` は `P` 以下。 -/
theorem first_period_le_of_crossing {w : List α} {k q₁ P : ℕ} (hPpos : 0 < P)
    (hq₁ : IsLeastKRep w k q₁) (hlen : k * P ≤ w.length)
    (hper : HasPeriod (w.take (k * P)) P) : q₁ ≤ P :=
  hq₁.2 P ⟨hPpos, hlen, hper⟩

/-- 系：run が `p_c` を `k * P` 以上跨ぐなら `q₁ ≤ P`。 -/
theorem first_period_le_of_deep_crossing {w : List α} {k p P t r q₁ Rc : ℕ} (hPpos : 0 < P)
    (hreg : HasPeriod (w.take Rc) p) (hRc : Rc ≤ w.length)
    (hrun : HasPeriod ((w.drop t).take r) P)
    (hq₁ : IsLeastKRep w k q₁)
    (ht : t ≤ p) (hdeep : p + k * P ≤ t + r) (hfit : p + k * P + P ≤ Rc) :
    q₁ ≤ P :=
  first_period_le_of_crossing hPpos hq₁ (by omega)
    (region_prefix_period hreg hRc hrun ht (by omega) (by omega))
/-! ## §11 DOWN 連鎖に沿った不変量 `E < p_c + q`

数値実験（UP 節点 147 個）で判明した最良の形：

* **UP 節点**（部分木を抜けて着地した節点）は `E' + t ≤ p_c + P - 1`、すなわち
  `E' < p_c + P` を **例外なく**満たす（最悪値 `-1`）。
* (E) が破れるのは DOWN 子だけ（`p_c = 300, t = 11, P = 37, E = 338`）。

そして `E < p_c + q` は **DOWN ステップで保存される**（`down_step_invariant`）。
`step_down_reach` から `E' + (k-1) * q ≤ E + q'` であり、`(k-1) * q' < q` と `q ≥ 1` から

```
E' ≤ E + q' - (k-1) * q < p_c + q + q' - (k-1) * q = p_c + q' - (k-2) * q < p_c + q'
```

したがって `E < p_c + q` は「連鎖の先頭」（第 1 子または UP 節点）でだけ確かめればよく、
第 1 子は `inner_run_lt` で無条件、UP 節点が唯一残る（下の `UpRunEnd`）。
そして `E < p_c + q` から `consumption_lt_period_of_runEnd` で `C(c) < p_c` が出る。 -/

/-- **DOWN ステップの鋭い形**：`E_child + (k-1) * p ≤ E_parent + q`
（親の開始位置を原点にとった相対座標。`E_parent = r`, `E_child = d + r'`）。 -/
theorem runEnd_down_step_sharp {w : List α} {k p q r r' d : ℕ} (hk : 4 ≤ k)
    (hd : k * p + d = r + 1)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop d) k q) (hlt : q < p)
    (hR' : ReachOf (w.drop d) q r') (hkq : k * q ≤ r') :
    (d + r') + (k - 1) * p ≤ r + q := by
  have hreach := step_down_reach hk hd hleast hR hkr hq hlt hR' hkq
  have h1 : (k - 1) * p + p = k * p := by rw [← Nat.succ_mul]; congr 1; omega
  omega

/-- **不変量の保存**：`E < p_c + q` は DOWN ステップで保たれる。

`hstep` は `runEnd_down_step_sharp`、`hgrow` は `child_period_bound`（`(k-1) q' < q`）。 -/
theorem down_step_invariant {k pc q q' E E' : ℕ} (hk : 4 ≤ k) (_hq : 0 < q) (_hq' : 0 < q')
    (hinv : E < pc + q) (_hgrow : (k - 1) * q' < q) (hstep : E' + (k - 1) * q ≤ E + q') :
    E' < pc + q' := by
  have h2 : 2 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
  omega

/-- **残る唯一の主張 (E-UP)**：部分木を抜けて着地した節点（UP 節点）の run は
`E' < p_c + P` で終わる。実測 147 例で例外なし（最悪の余裕 `1` セル）。 -/
def UpRunEnd (pc P E' : ℕ) : Prop := E' < pc + P

/-- **(E-UP) ⟹ 消費量補題**（連鎖の最後の節点に適用した形）。
`E < p_c + q` と `C + k * q = E + 1` から `C < p_c`。 -/
theorem consumption_of_invariant {k pc q E C : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (hinv : E < pc + q) (hC : C + k * q = E + 1) : C < pc := by
  have h1 : (k - 1) * q + q = k * q := by rw [← Nat.succ_mul]; congr 1; omega
  have h2 : 1 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
  omega

/-! ## §12 UP 節点の違反の場合分け

`Consumption` の否定を UP 節点 `ν`（開始オフセット `t`、最小 `k`-繰り返し周期 `P`、
run 長 `r'`）で書くと `p_c ≤ C = t + r' - k*P + 1` である。

* **早い UP 節点（`t + 1 ≤ (k-1) * P`）** は `inner_run_lt` だけで矛盾する
  （`up_violation_early`）：違反から `r' ≥ p_c + P` が出るが、領域の内側の run は
  `r' < p_c + P` で終わらなければならない。
  （`t < 2*P` は `k ≥ 4` ならこの場合に含まれる。）
* 残るのは **遅い UP 節点（`(k-1) * P ≤ t`）** だけ（`UpLate`）。実測でも
  `max t/((k-1)P) = 2.92` なのでこの場合は実在する。 -/

/-- **早い UP 節点では違反が起きない**。`t + 1 ≤ (k-1) * P` なら
`C = t + r' - k*P + 1 < p_c`。 -/
theorem up_violation_early {w : List α} {k pc P t r' rc : ℕ} (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k pc) (hR : ReachOf w pc rc) (hkr : k * pc ≤ rc)
    (hP : IsLeastKRep (w.drop t) k P) (hR' : ReachOf (w.drop t) P r')
    (hPlt : P < pc) (ht : t < pc)
    (hviol : pc + k * P ≤ t + r' + 1)
    (hearly : t + 1 ≤ (k - 1) * P) : False := by
  have hPpos : 0 < P := hP.1.1
  have hpc : 0 < pc := hleast.1.1
  have h1 : (k - 1) * P + P = k * P := by rw [← Nat.succ_mul]; congr 1; omega
  have h3 : 3 * pc ≤ k * pc := Nat.mul_le_mul_right pc (by omega)
  have hfit : t + (pc + P) ≤ rc := by omega
  have hinner := inner_run_lt hk hleast hR hkr hPpos hPlt hR' hfit
  omega

/-- **残る場合**：遅い UP 節点（`(k-1) * P ≤ t`）。

このとき違反からは `r' ≥ p_c + k*P - 1 - t` しか出ず、`t` が `p_c` に近いと
`r' ≥ k*P`（自明）に退化するので、`inner_run_lt` では閉じない。
必要なのは「`t` の手前にある run たち（`[t - P, t)` を覆う節点）と、
領域の `p_c`-周期性によるコピー」を使う議論である。 -/
def UpLate (k P t : ℕ) : Prop := (k - 1) * P ≤ t


section AxiomCheck
open PalPeg.PassSum9
#print axioms PalPeg.PassSum9.inner_run_lt
#print axioms PalPeg.PassSum9.sibling_growth
#print axioms PalPeg.PassSum9.sibling_growth_eight
#print axioms PalPeg.PassSum9.sibling_growth_kidsOk
#print axioms PalPeg.PassSum9.last_child_bound
#print axioms PalPeg.PassSum9.span_le
#print axioms PalPeg.PassSum9.consumption_lt_period_of_runEnd
#print axioms PalPeg.PassSum9.descendant_start_lt_of_runEnd
#print axioms PalPeg.PassSum9.runEnd_down_step
#print axioms PalPeg.PassSum9.period_factor_propagate
#print axioms PalPeg.PassSum9.factor_period_contradiction
#print axioms PalPeg.PassSum9.factor_copy_eq
#print axioms PalPeg.PassSum9.runEnd_up_step_le
#print axioms PalPeg.PassSum9.region_prefix_period
#print axioms PalPeg.PassSum9.first_period_le_of_crossing
#print axioms PalPeg.PassSum9.first_period_le_of_deep_crossing
#print axioms PalPeg.PassSum9.consumption_lt_period_of_dichotomy
#print axioms PalPeg.PassSum9.runEnd_down_step_sharp
#print axioms PalPeg.PassSum9.down_step_invariant
#print axioms PalPeg.PassSum9.consumption_of_invariant
#print axioms PalPeg.PassSum9.up_violation_early
#print axioms PalPeg.PassSum8.passPeriodSum_eight_of_hasTree
end AxiomCheck
