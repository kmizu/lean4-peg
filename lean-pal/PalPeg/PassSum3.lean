import PalPeg.PassSum2

/-!
# 1 パス内の入れ子木の構造（`Σⱼ pⱼ ≤ C₁ * T` に向けた第 3 段）

`PalPeg.PassSum` は隣接する 2 つの run の二分法を、`PalPeg.PassSum2` は
対 `(j, j+2)` の情報（`step_down_then`）を確立した。残る障害は
`PassSum2` 末尾で述べられている「深い V 字」、すなわち

```
P → P/(k-1) → … → m → (k-2)(k-1)m → … → P → …
```

型の繰り返しである。このファイルはその排除に必要な **語の側の構造補題**
（依頼の (F1)–(F3)）を形式化する。すべて `sorry` なし。

* (F1) `same_period_reach_end`：**同じ周期 `p` を持つ 2 つの run の周期領域は
  同じ右端で終わる**。すなわち親の領域 `[0, r)` の内側の位置 `t` で最小周期が再び
  `p` なら、その到達域は `r' = r - t` ちょうど。
  系 `same_period_nested`：`W_t ⊆ R₀`、`same_period_advance_eq`：前進後の右端は不変。
* (F2) `sibling_growth`：兄弟（親の領域を出る窓）が親の領域の**先頭寄り**
  （`u + (k-1)*p ≤ r + 1`）から始まるなら `(k-2)*p ≤ q`。
  すなわち「(B) からの成長」。
* (F3) `crossing_siblings_dvd`：親の右端 `r` を**ともに越える** 2 つの後続 run
  `u < u'`（"long descendants"）については、重なり `r - u'` が `q + q'` 以上なら
  `q' ∣ q`。とくに `q' ≤ q` で、`q' = q` なら (F1) より両者の右端は一致する。
  対偶として、`q' ∤ q` なら重なりは `q + q'` 未満（`crossing_siblings_overlap_lt`）。

## 残る組合せ的主張（未証明）

(F1)–(F3) は「木の各節点の子の並び」についての局所情報を与えるが、
依頼にある (F4) の集約（成長鎖の頂点の位置が幾何級数的に進むこと、および
入れ子木上の強帰納法）は**まだ閉じていない**。正確には次が残る：

> **(V)** 1 パスの run 開始位置 `a₀ < a₁ < …`、最小周期 `pⱼ`、到達域 `rⱼ`、
> `Eⱼ = aⱼ + rⱼ` について、`Eⱼ` を右端とする入れ子木の各節点 `j` に対し
> `Σ_{j' が j の子孫} pⱼ' ≤ C * pⱼ` が成り立つ（`C` は `k` のみに依存）。

(V) が示せれば、根（`T`-周期領域）に適用して `Σⱼ pⱼ ≤ C₁ * T`、すなわち
`GSDecompose2Work.decompose2Work_le` の仮定 `hsum` が得られる。
(V) の困難は、`(F3)` の "long descendant" を経て親の領域を出たあとの着地位置
`a_{c'} = E_ℓ - k*p_ℓ + 1` と、もとの子 `c` の周期 `p_c` との間に
関係がつかないこと（`p_{c'} ≥ (k-1)*p_ℓ` は出るが `p_c` とは無関係）である。
ここでは (F1)–(F3) までを確定させ、(V) を明示的に切り出すにとどめる。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

section Nesting

variable {w : List α} {k p q q' r r' ρ ρ' t uu uu' : ℕ}

/-! ## (F1) 同じ周期の領域は同じ右端で終わる -/

/-- **(F1) 核**。`w.take r` が周期 `p` の到達域（`r < |w|` なので極大）で、
その内側の位置 `t`（`t + p ≤ r`）から始まる周期 `p` の到達域が `r'` なら
`t + r' = r`。

* `t + r' < r` なら `w.take r` の `p`-周期性が `r' + 1` まで届いて極大性に反する；
* `r < t + r'` なら `hasPeriod_glue` で `w.take (r+1)` が `p`-周期になり同じく矛盾。 -/
theorem same_period_reach_end (hp : 0 < p) (hR : ReachOf w p r) (hrlt : r < w.length)
    (htp : t + p ≤ r) (hR' : ReachOf (w.drop t) p r') : t + r' = r := by
  have hrle : r ≤ w.length := hR.1
  have hdroplen : (w.drop t).length = w.length - t := by simp
  have hr'le : r' ≤ w.length - t := by have := hR'.1; omega
  have hmax : ¬ HasPeriod (w.take (r + 1)) p := by
    rcases hR.2.2 with h | h
    · omega
    · exact h
  -- 上からの評価
  have hle : r ≤ t + r' := by
    by_contra hcon
    have hlt : t + r' < r := by omega
    have hin : HasPeriod ((w.drop t).take (r - t)) p :=
      hasPeriod_drop_take hR.2.1 hrle (by omega)
    have hext : HasPeriod ((w.drop t).take (r' + 1)) p :=
      hasPeriod_take_of_le hin (by omega)
    rcases hR'.2.2 with h | h
    · rw [hdroplen] at h; omega
    · exact h hext
  -- 下からの評価
  have hge : t + r' ≤ r := by
    by_contra hcon
    have hglue : HasPeriod (w.take (t + r')) p :=
      hasPeriod_glue hR.2.1 hR'.2.1 htp (by omega) (by omega)
    exact hmax (hasPeriod_take_of_le hglue (by omega))
  omega

/-- **(F1) 系：入れ子**。同じ周期の後続 run の窓は親の周期領域に収まる。 -/
theorem same_period_nested (hp : 0 < p) (hR : ReachOf w p r) (hrlt : r < w.length)
    (htp : t + p ≤ r) (hR' : ReachOf (w.drop t) p r') (hkp : k * p ≤ r') :
    t + k * p ≤ r := by
  have := same_period_reach_end hp hR hrlt htp hR'
  omega

/-- **(F1) 系：右端は動かない**。同じ周期の run では `Eⱼ = aⱼ + rⱼ` が不変。
（したがって周期 `p` の run 開始位置たちの前進量 `rⱼ - k*p + 1` は
`r` からの距離だけで決まり、`p` ごとに領域は 1 つしかない。） -/
theorem same_period_advance_eq (hk : 0 < k) (hp : 0 < p) (hR : ReachOf w p r) (hrlt : r < w.length)
    (htp : t + p ≤ r) (hR' : ReachOf (w.drop t) p r') (hkp : k * p ≤ r') :
    t + (r' - k * p + 1) + (k * p - 1) = r := by
  have heq := same_period_reach_end hp hR hrlt htp hR'
  obtain ⟨c, rfl⟩ : ∃ c, r' = k * p + c := ⟨r' - k * p, by omega⟩
  have hkppos : 0 < k * p := Nat.mul_pos hk hp
  omega

/-! ## (F2) 親の領域を出る兄弟の周期の成長 -/

/-- **(F2)**。親（最小周期 `p`、到達域 `r`）の領域の内側で、しかも先頭寄り
（`uu + (k-1)*p ≤ r + 1`）から始まる run の窓が親の領域を出るなら、
その周期は `(k-2)*p` 以上になる。

(B) `sibling_overlap_lt` から `r - uu < p + q`、一方
`(k-1)*p - 1 ≤ r - uu` なので `(k-2)*p ≤ q`。 -/
theorem sibling_growth (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop uu) k q) (hnfit : r < uu + k * q)
    (hhead : uu + (k - 1) * p ≤ r + 1) : (k - 2) * p ≤ q := by
  have hp : 0 < p := hleast.1.1
  have hkp1 : (k - 1) * p + p = k * p := by rw [← Nat.succ_mul]; congr 1; omega
  have hkp2 : (k - 2) * p + p = (k - 1) * p := by
    have h : k - 1 = (k - 2) + 1 := by omega
    rw [h, Nat.succ_mul]
  have h4p : 4 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  have hur : uu < r := by omega
  have hov := sibling_overlap_lt hk hleast hR hkr hq hur hnfit
  omega

/-! ## (F3) 親の右端を越える 2 つの後続 run -/

/-- **(F3)**。位置 `uu < uu'` から始まる 2 つの run の周期領域がともに親の右端 `r`
を越える（`r ≤ uu + ρ`, `r ≤ uu' + ρ'`）とき、重なり `[uu', r)` の長さが `q + q'`
以上なら `q' ∣ q`。

重なりは周期 `q`（`uu` の領域から遺伝）と周期 `q'`（`uu'` の領域）を同時に持つので
Fine–Wilf から `g = gcd q q'` も周期、`uu'` の根 `(w.drop uu').take q'` は最小性より
原始的なので `g = q'`、ゆえに `q' ∣ q`。 -/
theorem crossing_siblings_dvd (hk : 4 ≤ k)
    (hq : IsLeastKRep (w.drop uu) k q) (hR : ReachOf (w.drop uu) q ρ)
    (hq' : IsLeastKRep (w.drop uu') k q') (hR' : ReachOf (w.drop uu') q' ρ')
    (hlt : uu ≤ uu') (hcross : r ≤ uu + ρ) (hcross' : r ≤ uu' + ρ')
    (hover : q + q' ≤ r - uu') : q' ∣ q := by
  have hqpos : 0 < q := hq.1.1
  have hq'pos : 0 < q' := hq'.1.1
  set L := r - uu' with hL
  have hLpos : 0 < L := by omega
  have hdroplen : (w.drop uu).length = w.length - uu := by simp
  have hdroplen' : (w.drop uu').length = w.length - uu' := by simp
  have hρle : ρ ≤ w.length - uu := by have := hR.1; omega
  have hρ'le : ρ' ≤ w.length - uu' := by have := hR'.1; omega
  have hLlen : L ≤ w.length - uu' := by omega
  -- 重なりが周期 `q` を持つ
  have hshift : (w.drop uu).drop (uu' - uu) = w.drop uu' := by
    rw [List.drop_drop]; congr 1; omega
  have hqwin0 : HasPeriod (((w.drop uu).drop (uu' - uu)).take (ρ - (uu' - uu))) q :=
    hasPeriod_drop_take hR.2.1 hR.1 (by omega)
  rw [hshift] at hqwin0
  have hqwin : HasPeriod ((w.drop uu').take L) q :=
    hasPeriod_take_of_le hqwin0 (by omega)
  -- 重なりが周期 `q'` を持つ
  have hq'win : HasPeriod ((w.drop uu').take L) q' :=
    hasPeriod_take_of_le hR'.2.1 (by omega)
  have hwlen : ((w.drop uu').take L).length = L := by
    rw [List.length_take, hdroplen']; omega
  have hgpos : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hqpos
  have hgle : Nat.gcd q q' ≤ q' := Nat.gcd_le_right _ hq'pos
  have hg := fineWilf hqwin hq'win hqpos hq'pos (by rw [hwlen]; omega)
  have hroot : HasPeriod ((w.drop uu').take q') (Nat.gcd q q') :=
    hasPeriod_take_of_le hg (by omega)
  have hrootlen : ((w.drop uu').take q').length = q' := by
    rw [List.length_take, hdroplen']
    have := hq'.1.2.1
    rw [hdroplen'] at this
    have : q' ≤ k * q' := Nat.le_mul_of_pos_left q' (by omega)
    omega
  have hgeq : Nat.gcd q q' = q' := by
    by_contra hne
    have hltg : Nat.gcd q q' < q' := by omega
    exact not_primitive_of_period hgpos (by omega)
      (by rw [hrootlen]; exact Nat.gcd_dvd_right q q') hroot
      (IsLeastKRep.primitive (by omega) hq')
  rw [← hgeq]; exact Nat.gcd_dvd_left q q'

/-- **(F3) 対偶版**。`q' ∤ q` なら、右端を越える 2 つの run の重なりは `q + q'` 未満。 -/
theorem crossing_siblings_overlap_lt (hk : 4 ≤ k)
    (hq : IsLeastKRep (w.drop uu) k q) (hR : ReachOf (w.drop uu) q ρ)
    (hq' : IsLeastKRep (w.drop uu') k q') (hR' : ReachOf (w.drop uu') q' ρ')
    (hlt : uu ≤ uu') (hcross : r ≤ uu + ρ) (hcross' : r ≤ uu' + ρ')
    (hndvd : ¬ q' ∣ q) : r - uu' < q + q' := by
  by_contra hcon
  exact hndvd (crossing_siblings_dvd hk hq hR hq' hR' hlt hcross hcross' (by omega))

/-- **(F3) 系**。右端を越える 2 つの run の周期が等しければ（`q' = q`）、
その周期領域の右端も一致する。すなわち "long descendant" は本質的に 1 つしかない。 -/
theorem crossing_siblings_same_end (hqpos : 0 < q)
    (hR : ReachOf (w.drop uu) q ρ) (hR' : ReachOf (w.drop uu') q ρ')
    (hlt : uu ≤ uu') (hin : (uu' - uu) + q ≤ ρ) (hρlt : ρ < (w.drop uu).length) :
    uu' + ρ' = uu + ρ := by
  have hshift : (w.drop uu).drop (uu' - uu) = w.drop uu' := by
    rw [List.drop_drop]; congr 1; omega
  have hR'' : ReachOf ((w.drop uu).drop (uu' - uu)) q ρ' := by rw [hshift]; exact hR'
  have := same_period_reach_end (w := w.drop uu) (t := uu' - uu) hqpos hR hρlt hin hR''
  omega

end Nesting

/-! ## 残る主張の明示

依頼の (F4)（成長鎖の集約と入れ子木上の強帰納法）は閉じていない。
残る組合せ的主張を `Prop` として切り出しておく。 -/

/-- **(V) 残る主張**：1 パスの周期和が `bound` に比例する。
`GSDecompose2Work.decompose2Work_le` の仮定 `hsum` そのものである。 -/
def PassSumLinear (x : List α) (k C₁ : ℕ) : Prop :=
  ∀ b s : ℕ, stripLoop2Periods x k b (x.length + 1) s ≤ C₁ * b

/-- (V) を仮定すれば `decompose2Work` は線形。（`decompose2Work_le` の言い換え。） -/
theorem decompose2Work_le_of_passSumLinear (x : List α) (k C₁ : ℕ) (hk : 4 ≤ k)
    (h : PassSumLinear x k C₁) :
    decompose2Work x k ≤ ((4 * k + 2) * C₁ + 17 * k + 50) * x.length + (2 * k + 5) :=
  decompose2Work_le x k C₁ hk h

end PalPeg
