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

/-! ## §5 消費量補題 (C) の帰納段階（抽象版）

子の列を `(周期 qᵢ, 消費幅 spanᵢ)` の対の列で表す。`k = 8` に固定する
（`(k-2) = 6`）。 -/

/-- 子の列の消費幅の総和。 -/
def sumSpan : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: t => a.2 + sumSpan t

/-- 先頭の子の周期。 -/
def headRoot : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: _ => a.1

@[simp] theorem sumSpan_nil : sumSpan [] = 0 := rfl
@[simp] theorem headRoot_nil : headRoot [] = 0 := rfl

/-- 節点 `c`（周期 `p`）の子の列の整合性（`k = 8`）。

* 連続する子の周期は 3 倍以上（`sibling_growth_kidsOk` は 6 倍超を与える）、
* **非末子の消費幅は次の兄弟の周期以下**（残る穴、`SpanLeNextSibling`）、
* 末子は `span_m + 6 * q_m ≤ p`（`span_le`）、
* 周期は正。 -/
def SpansOk (p : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | [a] => 0 < a.1 ∧ a.2 + 6 * a.1 ≤ p
  | a :: b :: t => 0 < a.1 ∧ 3 * a.1 ≤ b.1 ∧ a.2 ≤ b.1 ∧ SpansOk p (b :: t)

/-- **等比和**：整合的な子の列の消費幅の総和は `6 * Σ span + 9 * q₁ ≤ 6 * p`。

非末子は `spanᵢ ≤ qᵢ₊₁` で次の兄弟の周期に吸収され、成長 `3*qᵢ ≤ qᵢ₊₁` により
`6 * spanᵢ + 9 * qᵢ ≤ 6 * qᵢ₊₁ + 3 * qᵢ₊₁ = 9 * qᵢ₊₁` と帰納が回る。 -/
theorem spans_sum_bound (p : ℕ) :
    ∀ ks : List (ℕ × ℕ), ks ≠ [] → SpansOk p ks →
      6 * sumSpan ks + 9 * headRoot ks ≤ 6 * p := by
  intro ks
  induction ks with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil =>
      intro _ h
      obtain ⟨-, hlast⟩ := h
      simp only [sumSpan, headRoot]
      omega
    | cons b t' =>
      intro _ h
      obtain ⟨-, hgrow, hspan, hrest⟩ := h
      have hIH := ih (by simp) hrest
      have hh : headRoot (b :: t') = b.1 := rfl
      rw [hh] at hIH
      have hs : sumSpan (a :: b :: t') = a.2 + sumSpan (b :: t') := rfl
      rw [hs, show headRoot (a :: b :: t') = a.1 from rfl]
      omega

/-- **消費量補題 (C) の帰納段階**：整合的な子の列に対し `Σ spanᵢ < p`。

`C(c) = Σ spanᵢ` なので、これは `C(c) < p_c` そのものである。 -/
theorem consumption_lt_period_abstract (p : ℕ) (hp : 0 < p) (ks : List (ℕ × ℕ))
    (h : SpansOk p ks) : sumSpan ks < p := by
  cases ks with
  | nil => simpa using hp
  | cons a t =>
    have hb := spans_sum_bound p (a :: t) (by simp) h
    have hpos : 0 < headRoot (a :: t) := by
      cases t with
      | nil => exact h.1
      | cons b t' => exact h.1
    omega

/-- 子が無い節点（葉）の消費量は `0 < p`。 -/
theorem consumption_lt_period_leaf (p : ℕ) (hp : 0 < p) : sumSpan [] < p := by
  simpa using hp

/-- 子が 1 つだけの節点：`span_le` の結論だけから `C(c) < p_c` が従う
（追加の仮定は不要）。 -/
theorem consumption_lt_period_single (p q s : ℕ) (_hq : 0 < q) (h : s + 6 * q ≤ p) :
    sumSpan [(q, s)] < p := by
  simp only [sumSpan]
  omega

/-! ## §6 残る穴の明示 -/

/-- **残る唯一の未証明の主張**：節点 `c` の非末子 `qᵢ` の消費幅は次の兄弟の周期以下。

`span_le` は `spanᵢ + 6 * qᵢ ≤ p_c` までしか与えないので、`p_c` が `qᵢ` に比べて
大きいときにこれだけでは足りない。実測（`k = 8`）では
`max spanᵢ / qᵢ₊₁ = 0.78`、`max spanᵢ / p_c = 0.081` である。

意味論的には「非末子の run は早く終わる」——run が長く伸びる子のあとの脱出位置は
`R_c` の外に出てしまい、その子が末子になる——という現象にあたる。 -/
def SpanLeNextSibling (_p : ℕ) (ks : List (ℕ × ℕ)) : Prop :=
  match ks with
  | [] => True
  | [_] => True
  | a :: b :: _ => a.2 ≤ b.1

end PassSum9
end PalPeg

section AxiomCheck
open PalPeg.PassSum9
#print axioms PalPeg.PassSum9.inner_run_lt
#print axioms PalPeg.PassSum9.sibling_growth
#print axioms PalPeg.PassSum9.sibling_growth_eight
#print axioms PalPeg.PassSum9.sibling_growth_kidsOk
#print axioms PalPeg.PassSum9.last_child_bound
#print axioms PalPeg.PassSum9.span_le
#print axioms PalPeg.PassSum9.spans_sum_bound
#print axioms PalPeg.PassSum9.consumption_lt_period_abstract
#print axioms PalPeg.PassSum8.passPeriodSum_eight_of_hasTree
end AxiomCheck
