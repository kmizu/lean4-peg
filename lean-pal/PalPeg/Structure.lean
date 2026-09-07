import PalPeg.Words
import PalPeg.Chain

/-!
# 接尾辞回文の構造補題（replica / border / predictability / maturity）

`PalPeg.Words` の道具箱（`isPal_take_iff`, `isPal_drop_iff`,
`hasPeriod_iff_drop_eq_take`, `fineWilf`, `hasPeriod_of_prefix_dvd`）を用いて、
実時間 `PAL` 機械の設計で必要になる 4 つの構造補題を証明する。

* (R) `suffixPal_replica`      — 周期による接尾辞回文の複製
* (B') `border_of_minimalPeriod` — 最小周期のとき鎖の第 2 要素は最長 border
* (P) `center_suffix_of_pal`, `pal_prefix_length_ge` — 予測可能性
* (M) `lsp_shift_bound`        — 成熟した接尾辞回文による長さの禁止帯

なお、素朴な「成熟版シフト補題」（`n - p` 時点の最長回文接尾辞がちょうど `ℓ - p`）は
**偽**である。反例は `counterexample_lsp_shift_of_mature` を参照。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## (R) 複製補題 (replica lemma) -/

/-- 周期 `p` を持つ語では、長さ `L ≤ |x| - p` の接尾辞は、
`x` の長さ `|x| - p` の接頭辞（= border）の同じ長さの接尾辞と一致する。 -/
theorem drop_eq_take_drop_of_period {x : List α} {p L : ℕ}
    (hxp : HasPeriod x p) (hpn : p ≤ x.length) (hL : L ≤ x.length - p) :
    x.drop (x.length - L) = (x.take (x.length - p)).drop (x.length - p - L) := by
  have hb := (hasPeriod_iff_drop_eq_take hpn).mp hxp
  rw [← hb, List.drop_drop]
  congr 1
  omega

/-- 語 `w` の長さ `ℓ` の接尾辞が周期 `p` を持つとき、長さ `L ≤ ℓ - p` の接尾辞は
`w.take (w.length - p)` の長さ `L` の接尾辞と**同じ語**である。 -/
theorem suffixPal_replica_eq {w : List α} {ℓ p L : ℕ}
    (hℓn : ℓ ≤ w.length) (hxp : HasPeriod (w.drop (w.length - ℓ)) p)
    (hpl : p ≤ ℓ) (hL : L ≤ ℓ - p) :
    w.drop (w.length - L) = (w.take (w.length - p)).drop (w.length - p - L) := by
  have hxlen : (w.drop (w.length - ℓ)).length = ℓ := by
    rw [List.length_drop]; omega
  have hcore := drop_eq_take_drop_of_period (L := L) hxp (by rw [hxlen]; omega)
    (by rw [hxlen]; omega)
  rw [hxlen] at hcore
  have h1 : (w.drop (w.length - ℓ)).drop (ℓ - L) = w.drop (w.length - L) := by
    rw [List.drop_drop]; congr 1; omega
  have h2 : (w.drop (w.length - ℓ)).take (ℓ - p)
      = (w.take (w.length - p)).drop (w.length - ℓ) := by
    rw [List.drop_take]; congr 1; omega
  have h3 : ((w.take (w.length - p)).drop (w.length - ℓ)).drop (ℓ - p - L)
      = (w.take (w.length - p)).drop (w.length - p - L) := by
    rw [List.drop_drop]; congr 1; omega
  rw [← h1, hcore, h2, h3]

/-- **(R) 複製補題**。`w` の長さ `ℓ` の接尾辞が周期 `p` を持つ回文なら、
`L ≤ ℓ - p` について「`w` の長さ `L` の接尾辞が回文」と
「`w.take (w.length - p)` の長さ `L` の接尾辞が回文」は同値。 -/
theorem suffixPal_replica {w : List α} {ℓ p L : ℕ}
    (hℓn : ℓ ≤ w.length) (hx : IsPal (w.drop (w.length - ℓ)))
    (hxp : HasPeriod (w.drop (w.length - ℓ)) p) (hp : 0 < p) (hpl : p ≤ ℓ)
    (hL : L ≤ ℓ - p) :
    IsPal (w.drop (w.length - L)) ↔
      IsPal ((w.take (w.length - p)).drop (w.length - p - L)) := by
  have _hx := hx
  have _hp := hp
  rw [suffixPal_replica_eq hℓn hxp hpl hL]

/-! ## (B') 鎖の第 2 要素は最長 border -/

/-- 回文 `y` の長さ `k` の接尾辞が回文なら、`|y| - k` は `y` の周期。 -/
theorem hasPeriod_of_pal_suffix_pal {y : List α} {k : ℕ} (hy : IsPal y)
    (hk : k ≤ y.length) (hz : IsPal (y.drop (y.length - k))) :
    HasPeriod y (y.length - k) := by
  have h := (isPal_drop_iff hy hk).mp hz
  rw [hasPeriod_iff_drop_eq_take (by omega),
    show y.length - (y.length - k) = k from by omega]
  exact h.symm

/-- **(B')**。`x` が回文で `p` が最小の正の周期のとき、
`x.drop p`（長さ `|x| - p` の接尾辞）は回文であり、
長さが `|x| - p` より真に大きく `|x|` 未満の接尾辞は回文でない。 -/
theorem border_of_minimalPeriod {x : List α} {p : ℕ} (hx : IsPal x)
    (hxp : HasPeriod x p) (hp : 0 < p) (hpn : p ≤ x.length)
    (hmin : ∀ q, 0 < q → q < p → ¬ HasPeriod x q) :
    IsPal (x.drop p) ∧
      ∀ L, x.length - p < L → L < x.length → ¬ IsPal (x.drop (x.length - L)) := by
  have hb := (hasPeriod_iff_drop_eq_take hpn).mp hxp
  constructor
  · have h := isPal_drop_iff hx (k := x.length - p) (by omega)
    rw [show x.length - (x.length - p) = p from by omega] at h
    exact h.mpr hb.symm
  · intro L h1 h2 hpal
    exact hmin (x.length - L) (by omega) (by omega)
      (hasPeriod_of_pal_suffix_pal hx (by omega) hpal)

/-! ## (P) 予測可能性 (predictability) -/

/-- **(P)**。`w` が長さ `m'` の回文で `m ≤ m' ≤ 2 * m` なら、
`w.take m` の長さ `2 * m - m'` の接尾辞は回文。 -/
theorem center_suffix_of_pal {w : List α} {m m' : ℕ} (hw : IsPal w)
    (hlen : w.length = m') (hm : m ≤ m') (hm' : m' ≤ 2 * m) :
    IsPal ((w.take m).drop (m' - m)) := by
  have hk : m' - m ≤ w.length / 2 := by rw [hlen]; omega
  have hc := isPal_drop_take_center hw hk
  have he : (w.take m).drop (m' - m)
      = (w.drop (m' - m)).take (w.length - 2 * (m' - m)) := by
    rw [List.drop_take]; congr 1; omega
  rw [he]; exact hc

/-- **(P) の系**。時刻 `m` における接尾辞回文の長さがすべて `ℓ₀` か `K` 未満であれば、
未来の時刻 `m' ∈ [m, 2m]` に全体接頭辞 `w.take m'` が回文になるのは
`2 * m - m' = ℓ₀` か `2 * m - m' < K` のときに限る
（すなわち `m' = 2 * m - ℓ₀` または `m' > 2 * m - K`）。 -/
theorem pal_prefix_length_ge {w : List α} {m m' ℓ₀ K : ℕ}
    (hm'n : m' ≤ w.length) (hpal : IsPal (w.take m')) (hm : m ≤ m') (hm2 : m' ≤ 2 * m)
    (hchain : ∀ L, L ≤ m → IsPal ((w.take m).drop (m - L)) → L = ℓ₀ ∨ L < K) :
    2 * m - m' = ℓ₀ ∨ 2 * m - m' < K := by
  have hlen : (w.take m').length = m' := by rw [List.length_take]; omega
  have h := center_suffix_of_pal hpal hlen hm hm2
  rw [List.take_take, show min m m' = m from by omega] at h
  refine hchain (2 * m - m') (by omega) ?_
  rw [show m - (2 * m - m') = m' - m from by omega]
  exact h

/-! ## (M) 成熟した接尾辞回文と長さの禁止帯 -/

/-- 回文 `x` の最小周期が `p` で `3 * p ≤ |x|` のとき、
`x` の長さ `|x| - p` の接頭辞を接尾辞に持つ回文 `y` の長さは
`|x| - p` と `|x|` の間（両端を除く）には入れない。 -/
theorem minimalPeriod_no_medium_pal {x y : List α} {p : ℕ}
    (hx : IsPal x) (hxp : HasPeriod x p) (hp : 0 < p) (hpl : p ≤ x.length)
    (hmin : ∀ q, 0 < q → q < p → ¬ HasPeriod x q) (hmature : 3 * p ≤ x.length)
    (hy : IsPal y)
    (hsuf : y.drop (y.length - (x.length - p)) = x.take (x.length - p))
    (hy1 : x.length - p < y.length) (hy2 : y.length < x.length) : False := by
  have hzlen : (x.take (x.length - p)).length = x.length - p := by
    rw [List.length_take]; omega
  -- border は回文
  have hzpal : IsPal (x.take (x.length - p)) := by
    refine (isPal_take_iff hx (by omega)).mpr ?_
    rw [show x.length - (x.length - p) = p from by omega]
    exact ((hasPeriod_iff_drop_eq_take hpl).mp hxp).symm
  -- q := |y| - (|x| - p) は y の周期
  have hyq : HasPeriod y (y.length - (x.length - p)) :=
    hasPeriod_of_pal_suffix_pal hy (by omega) (by rw [hsuf]; exact hzpal)
  set q := y.length - (x.length - p) with hq
  have hq0 : 0 < q := by omega
  have hqp : q < p := by omega
  -- 重なり z = x.take (|x| - p) は周期 p と q をもつ
  have hzq : HasPeriod (x.take (x.length - p)) q := by
    rw [← hsuf]; exact hasPeriod_drop hyq
  have hzp : HasPeriod (x.take (x.length - p)) p := hasPeriod_take hxp
  -- Fine–Wilf
  have hg0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  have hgq : Nat.gcd p q ≤ q := Nat.gcd_le_right _ hq0
  have hzg : HasPeriod (x.take (x.length - p)) (Nat.gcd p q) := by
    refine fineWilf hzp hzq hp hq0 ?_
    rw [hzlen]; omega
  -- 先頭 p 文字へ制限してから x 全体に伝播
  have htp : (x.take (x.length - p)).take p = x.take p := by
    rw [List.take_take, show min p (x.length - p) = p from by omega]
  have hxg : HasPeriod x (Nat.gcd p q) :=
    hasPeriod_of_prefix_dvd hxp hp (Nat.gcd_dvd_left p q)
      (by rw [← htp]; exact hasPeriod_take hzg)
  exact hmin _ hg0 (by omega) hxg

/-- **(M) の正しい形（禁止帯）**。`w` の長さ `ℓ` の接尾辞 `x` が回文で最小の正の周期が `p`、
かつ成熟している（`3 * p ≤ ℓ`）とき、`w.take (w.length - p)` の回文接尾辞の長さ `M` は
`M ≤ ℓ - p` か `ℓ ≤ M` のいずれかであり、`(ℓ - p, ℓ)` の帯には入らない。

（素朴な主張「最長回文接尾辞はちょうど `ℓ - p`」は偽。
`counterexample_lsp_shift_of_mature` を参照。） -/
theorem lsp_shift_bound {w : List α} {ℓ p M : ℕ}
    (hℓn : ℓ ≤ w.length) (hx : IsPal (w.drop (w.length - ℓ)))
    (hxp : HasPeriod (w.drop (w.length - ℓ)) p) (hp : 0 < p) (hpl : p ≤ ℓ)
    (hmin : ∀ q, 0 < q → q < p → ¬ HasPeriod (w.drop (w.length - ℓ)) q)
    (hmature : 3 * p ≤ ℓ) (hM : M ≤ w.length - p)
    (hy : IsPal ((w.take (w.length - p)).drop (w.length - p - M)))
    (hMgt : ℓ - p < M) : ℓ ≤ M := by
  by_contra hlt
  simp only [Nat.not_le] at hlt
  have hxlen : (w.drop (w.length - ℓ)).length = ℓ := by
    rw [List.length_drop]; omega
  have hprelen : (w.take (w.length - p)).length = w.length - p := by
    rw [List.length_take]; omega
  have hylen : ((w.take (w.length - p)).drop (w.length - p - M)).length = M := by
    rw [List.length_drop, hprelen]; omega
  refine minimalPeriod_no_medium_pal (x := w.drop (w.length - ℓ))
    (y := (w.take (w.length - p)).drop (w.length - p - M))
    hx hxp hp (by rw [hxlen]; omega) hmin (by rw [hxlen]; omega) hy ?_
    (by rw [hxlen, hylen]; omega) (by rw [hxlen, hylen]; omega)
  have hk : w.length - p - M + (M - (ℓ - p)) = w.length - ℓ := by omega
  rw [hxlen, hylen, List.drop_drop, hk, List.drop_take]
  congr 1
  omega

/-! ## 反例：素朴な「成熟版シフト補題」は偽

`w = 0 0 1 0 0 0` について、`w` の最長回文接尾辞は `x = 0 0 0`（`ℓ = 3`）、
その最小周期は `p = 1` で `3 * p ≤ ℓ` は成立（成熟）。
にもかかわらず `w.take (w.length - p) = 0 0 1 0 0` は長さ `5` の回文接尾辞をもち、
`ℓ - p = 2` をはるかに超える。禁止帯 `(2, 3)` は空なので `lsp_shift_bound` とは矛盾しない。 -/

/-- 反例の語。 -/
def cexWord : List (Fin 2) := [0, 0, 1, 0, 0, 0]

theorem cex_x : cexWord.drop (cexWord.length - 3) = [0, 0, 0] := by decide

theorem cex_x_pal : IsPal (cexWord.drop (cexWord.length - 3)) := by
  unfold IsPal; decide

theorem cex_x_period : HasPeriod (cexWord.drop (cexWord.length - 3)) 1 := by
  intro i hi
  rw [cex_x] at hi ⊢
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp only [List.length_cons, List.length_nil] at hi; omega

theorem cex_x_minimal : ∀ q, 0 < q → q < 1 → ¬ HasPeriod (cexWord.drop (cexWord.length - 3)) q := by
  intro q h1 h2; omega

/-- `x` は本当に最長の回文接尾辞。 -/
theorem cex_x_longest :
    ∀ L, L ≤ cexWord.length → IsPal (cexWord.drop (cexWord.length - L)) → L ≤ 3 := by
  unfold IsPal
  decide

/-- しかし `w.take (|w| - 1)` は長さ `5` の回文接尾辞をもつ（`ℓ - p = 2` より大きい）。 -/
theorem cex_long_pal :
    IsPal ((cexWord.take (cexWord.length - 1)).drop (cexWord.length - 1 - 5)) := by
  unfold IsPal; decide

end PalPeg

