import PalPeg.GalilScaffoldChainFallback

/-!
# 局所周期の合併・切り出し・偶奇・鏡映

Galil 型の実時間回文照合で必要になる、純粋な語の組合せ論の 4 本立て。

* `PeriodOn x p a b` — 添字区間 `[a, b]` 上で `p` が `x` の周期であること。
* `periodOn_union` — 少なくとも `p` 個の位置で重なる 2 つの周期区間は合併できる。
* `hasPeriod_slice_iff` — `PeriodOn` は切り出した部分列の `HasPeriod` と同値。
* `encoded_periodOn_even` — 符号化語（偶数位置が区切り `2`、奇数位置が文字）の
  局所周期は必ず偶数。
* `periodOn_mirror` — 回文中心 `C` の内側では、右側の周期区間が左側へ鏡映される。
-/

set_option autoImplicit false
namespace PalPeg
open Manacher

universe u
variable {α : Type u}

/-! ## 区間上の周期 -/

/-- `x` has period `p` on the index interval `[a, b]` (inclusive, indices in range). -/
def PeriodOn (x : List α) (p a b : ℕ) : Prop := ∀ i, a ≤ i → i + p ≤ b → x[i]? = x[i + p]?

/-- 周期 `0` はどの区間でも自明に成り立つ。 -/
theorem periodOn_zero (x : List α) (a b : ℕ) : PeriodOn x 0 a b := by
  intro i _ _
  simp

/-- 区間を狭める向きの単調性。 -/
theorem PeriodOn.mono {x : List α} {p a b a' b' : ℕ} (h : PeriodOn x p a b)
    (ha : a ≤ a') (hb : b' ≤ b) : PeriodOn x p a' b' :=
  fun i hi hib => h i (le_trans ha hi) (le_trans hib hb)

/-! ## 1. 重なり合う 2 つの周期区間の合併 -/

/-- **周期区間の合併**。区間 `[a, b]` と `[a', b']` が共に周期 `p` を持ち、
重なり `[max a a', min b b']` が少なくとも `p` 個の位置を含むなら、
合併区間 `[min a a', max b b']` 上でも `p` は周期である。

重なりが `p` 個以上あるので、合併区間内の任意の `i` について `i` と `i + p` は
必ず同じ一方の区間に収まる（そうでないと重なりが `p` 未満になる）。 -/
theorem periodOn_union {x : List α} {p a b a' b' : ℕ} (h1 : PeriodOn x p a b)
    (h2 : PeriodOn x p a' b') (hov : a' ≤ b ∧ a ≤ b')
    (hlen : p ≤ min b b' + 1 - max a a') :
    PeriodOn x p (min a a') (max b b') := by
  obtain ⟨hov1, hov2⟩ := hov
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact periodOn_zero x _ _
  intro i hi hib
  by_cases hcase : a ≤ i ∧ i + p ≤ b
  · exact h1 i hcase.1 hcase.2
  · have hcase' : a' ≤ i ∧ i + p ≤ b' := by omega
    exact h2 i hcase'.1 hcase'.2

/-! ## 2. 切り出した部分列の周期との同値 -/

/-- `x` の添字区間 `[a, b]` を切り出した部分列 `(x.drop a).take (b + 1 - a)` が
周期 `p` を持つことと、`x` が `[a, b]` 上で周期 `p` を持つことは同値。 -/
theorem hasPeriod_slice_iff {x : List α} {p a b : ℕ} (hb : b < x.length) (hab : a ≤ b) :
    HasPeriod ((x.drop a).take (b + 1 - a)) p ↔ PeriodOn x p a b := by
  have hlen : ((x.drop a).take (b + 1 - a)).length = b + 1 - a := by
    rw [List.length_take, List.length_drop]
    omega
  constructor
  · intro h i hi hip
    have hj : i - a + p < ((x.drop a).take (b + 1 - a)).length := by rw [hlen]; omega
    have key := h (i - a) hj
    rw [getElem?_take_drop (m := b + 1 - a) (by omega),
      getElem?_take_drop (m := b + 1 - a) (by omega)] at key
    rw [show a + (i - a) = i from by omega, show a + (i - a + p) = i + p from by omega] at key
    exact key
  · intro h j hj
    rw [hlen] at hj
    rw [getElem?_take_drop (m := b + 1 - a) (by omega),
      getElem?_take_drop (m := b + 1 - a) (by omega)]
    have key := h (a + j) (by omega) (by omega)
    rw [show a + (j + p) = a + j + p from by omega]
    exact key

/-! ## 3. 符号化語の局所周期は偶数 -/

/-- 文字の符号 `letter a`（値は `0` か `1`）は区切り記号 `2` とは異なる。 -/
theorem letter_ne_two (a : Fin 2) : GalilScaffoldPlace.letter a ≠ 2 := by
  fin_cases a <;> decide

/-- **符号化語の周期は偶数**。`encoded raw` は偶数位置に区切り `2`、奇数位置に
文字を置くので、長さ `p` の周期が区間 `[a, b]`（`a + p ≤ b`）で成り立つなら
`p` は偶数でなければならない。`p` が奇数だと `a` と `a + p` の偶奇が食い違い、
区切りと文字を同一視することになって矛盾する。 -/
theorem encoded_periodOn_even {raw : List (Fin 2)} {p a b : ℕ}
    (h : PeriodOn (GalilScaffoldChainInputSupply.encoded raw) p a b)
    (hp : 0 < p) (hab : a + p ≤ b)
    (hb : b < (GalilScaffoldChainInputSupply.encoded raw).length) :
    p % 2 = 0 := by
  by_contra hodd
  have hlen : (GalilScaffoldChainInputSupply.encoded raw).length = 2 * raw.length + 1 := by
    simp [GalilScaffoldChainInputSupply.encoded, GalilScaffoldChainInputSupply.pairs_length]
  rw [hlen] at hb
  have key := h a (le_refl a) hab
  have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hmod with h0 | h0
  · obtain ⟨n, hn⟩ : ∃ n, a + p = 2 * n + 1 := ⟨(a + p) / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, a = 2 * m := ⟨a / 2, by omega⟩
    have hmle : m ≤ raw.length := by omega
    have hnlt : n < raw.length := by omega
    rw [hn, hm] at key
    rw [GalilScaffoldChainInputSupply.encoded_even raw m hmle,
      GalilScaffoldChainInputSupply.encoded_odd raw n hnlt] at key
    exact letter_ne_two _ (Option.some.inj key).symm
  · obtain ⟨n, hn⟩ : ∃ n, a + p = 2 * n := ⟨(a + p) / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
    have hmlt : m < raw.length := by omega
    have hnle : n ≤ raw.length := by omega
    rw [hn, hm] at key
    rw [GalilScaffoldChainInputSupply.encoded_odd raw m hmlt,
      GalilScaffoldChainInputSupply.encoded_even raw n hnle] at key
    exact letter_ne_two _ (Option.some.inj key)

/-! ## 4. 回文中心を通した周期区間の鏡映 -/

set_option linter.unusedVariables false in
/-- **周期区間の鏡映**。`PalAt x C k` の内側では、右半分 `[C, C + k]` の周期 `p`
（`p ≤ k`）が左半分 `[C - k, C]` にそのまま移る。

注意: 実際の証明に `hp : p ≤ k` は不要（`C - k ≤ i` と `i + p ≤ C` だけで
`2 * C - (i + p) + p = 2 * C - i ≤ C + k` が出る）。呼び出し側の仕様に合わせて
仮定はそのまま残し、未使用変数の linter だけ黙らせている。 -/
theorem periodOn_mirror {x : List α} {C k p : ℕ} (hpal : PalAt x C k) (hp : p ≤ k)
    (h : PeriodOn x p C (C + k)) : PeriodOn x p (C - k) C := by
  intro i hi hip
  have hm1 : x[i]? = x[2 * C - i]? := Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hm2 : x[i + p]? = x[2 * C - (i + p)]? :=
    Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hstep : x[2 * C - (i + p)]? = x[2 * C - (i + p) + p]? := h _ (by omega) (by omega)
  rw [show 2 * C - (i + p) + p = 2 * C - i from by omega] at hstep
  rw [hm1, hm2]
  exact hstep.symm

set_option linter.unusedVariables false in
/-- **左→右の鏡映**（`periodOn_mirror` の逆向き）。回文の左半分 `[C − k, C]` での
周期 `p` が右半分 `[C, C + k]` に移る。証明は `periodOn_mirror` と対称。

fresh 側 `ShiftPal` で要るのはこちら向き——`Candidate` は中心の**左**（place stream の
接頭辞）の回文性を保証するので、そこから現在の回文の右半分へ運ぶ。 -/
theorem periodOn_mirror' {x : List α} {C k p : ℕ} (hpal : PalAt x C k) (hp : p ≤ k)
    (h : PeriodOn x p (C - k) C) : PeriodOn x p C (C + k) := by
  have hkC : k ≤ C := hpal.1
  intro i hi hip
  have hm1 : x[i]? = x[2 * C - i]? := Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hm2 : x[i + p]? = x[2 * C - (i + p)]? :=
    Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hstep : x[2 * C - (i + p)]? = x[2 * C - (i + p) + p]? := h _ (by omega) (by omega)
  rw [show 2 * C - (i + p) + p = 2 * C - i from by omega] at hstep
  rw [hm1, hm2]
  exact hstep.symm

#print axioms periodOn_mirror'

/-- **中心が `d` ずれた 2 つの回文から周期 `2d`。**

`PalAt x (C − d) d`（内側）と `PalAt x (C − 2d) (2d)`（外側）から
`PeriodOn x (2d) (C − 4d) C`。

`i ∈ [C − 4d, C − 2d]` について、外側の鏡映が `x[i] = x[2(C−2d) − i]`、
内側の鏡映が `x[i + 2d] = x[2(C−d) − (i+2d)]` を与え、
`2(C−2d) − i = 2(C−d) − (i+2d) = 2C − 4d − i` で一致する。

これが `GalilDpCorrect.Candidate` の 2 節
（`(w.take (2h+1)).reverse = w.take (2h+1)` と `(w.take (4h+1)).reverse = w.take (4h+1)`、
`CloseoutWatchPhase3.palAt_pair_of_candidate` 経由）から周期を出す段。 -/
theorem periodOn_of_palAt_pair {x : List α} {C d : ℕ}
    (hin : PalAt x (C - d) d) (hout : PalAt x (C - 2 * d) (2 * d)) :
    PeriodOn x (2 * d) (C - 4 * d) C := by
  have hin1 : d ≤ C - d := hin.1
  have hout1 : 2 * d ≤ C - 2 * d := hout.1
  intro i hi hip
  have h1 : x[i]? = x[2 * (C - 2 * d) - i]? :=
    Manacher.mirror_getElem? hout (by omega) (by omega)
  have h2 : x[i + 2 * d]? = x[2 * (C - d) - (i + 2 * d)]? :=
    Manacher.mirror_getElem? hin (by omega) (by omega)
  rw [h1, h2]
  congr 1
  omega

#print axioms periodOn_of_palAt_pair

/-- **`reshift_from_right` の `hright` を 2 回文と現在の回文から出す。**

`periodOn_of_palAt_pair` が中心の左 `[C − 4d, C]` で周期 `2d` を出し、
`PeriodOn.mono` で現在の回文の左半分 `[C − r, C]` に絞り（`r ≤ 4d` が要る）、
`periodOn_mirror'` で右半分 `[C, C + r]` へ移す。

`r ≤ 4d` は found 時の `GalilReplayBudgetProof.found_radius_le_two_period`
（`value sF.radius ≤ 2 * h`）から。`2d ≤ r` は `reshift_from_right` の `hsmall` と同じ。 -/
theorem periodOn_right_of_palAt_pair {x : List α} {C d r : ℕ}
    (hin : PalAt x (C - d) d) (hout : PalAt x (C - 2 * d) (2 * d))
    (hcur : PalAt x C r) (hle : r ≤ 4 * d) (hp : 2 * d ≤ r) :
    PeriodOn x (2 * d) C (C + r) :=
  periodOn_mirror' hcur hp
    ((periodOn_of_palAt_pair hin hout).mono (by omega) (le_refl _))

#print axioms periodOn_right_of_palAt_pair

/-- **fresh 側のシフト回文**（n140 の段 4）。

中心が `h` ずれた 2 回文（DP の `Candidate` から）＋現在の回文＋末尾の予測から、
シフト後の回文 `PalAt word (C + h) (r + 1 − h)` を出す。
これが `ShiftPal` の結論の第 3 節そのもの。

`hright` は `periodOn_right_of_palAt_pair` が `[C, C + r]` で出し、
最後の 1 添字（`j + 2h = C + r + 1`）だけ `hpred`（`shiftGuardVM` の予測節）で埋める。

`hold` が半径 `h` 分で足りるのは n139 で `reshift_from_right` を弱めたため。 -/
theorem reshift_of_palAt_period (word : List (Fin 3)) (C h r : ℕ)
    (hin : Manacher.PalAt word (C - h) h)
    (hcur : Manacher.PalAt word C r)
    (hstep : 0 < h) (hsmall : 2 * h ≤ r)
    (hend : C + r + 1 < word.length)
    (hleft : PeriodOn word (2 * h) (C - r) C)
    (hpred : word[C + r + 1]? = word[C + r + 1 - 2 * h]?) :
    Manacher.PalAt word (C + h) (r + 1 - h) := by
  have hhC : h ≤ C := by have := hin.1; omega
  have hCh : C - h + h = C := by omega
  have hrh : r - h + h = r := by omega
  have hper : PeriodOn word (2 * h) C (C + r) := periodOn_mirror' hcur hsmall hleft
  have hres := PalPeg.GalilScaffoldChainInputSupply.reshift_from_right word (C - h) (r - h) h
    hin (by rw [hCh, hrh]; exact hcur) hstep (by omega) (by rw [hCh, hrh]; omega) ?_
  · rw [show C - h + 2 * h = C + h from by omega, show r - h + 1 = r + 1 - h from by omega] at hres
    exact hres
  · intro j hj hj2
    rw [hCh] at hj
    rw [hCh, hrh] at hj2
    by_cases hlast : j + 2 * h ≤ C + r
    · exact hper j (by omega) hlast
    · have hje : j = C + r + 1 - 2 * h := by omega
      subst hje
      rw [show C + r + 1 - 2 * h + 2 * h = C + r + 1 from by omega]
      exact hpred.symm

#print axioms reshift_of_palAt_period

/-- **`phase = 4` への特化.**  四つの検証済み半周期は `r ≤ 4 * h` のときだけ
左区間 `[C − r, C]` の周期を与える。Scala の `ScaffoldChain.canShift` は
`r ≤ 4 * h` を検査せえへんので、機械側が使うのは `reshift_of_palAt_period` の方。 -/
theorem reshift_of_palAt_pair (word : List (Fin 3)) (C h r : ℕ)
    (hin : Manacher.PalAt word (C - h) h)
    (hout : Manacher.PalAt word (C - 2 * h) (2 * h))
    (hcur : Manacher.PalAt word C r)
    (hstep : 0 < h) (hsmall : 2 * h ≤ r) (hle : r ≤ 4 * h)
    (hend : C + r + 1 < word.length)
    (hpred : word[C + r + 1]? = word[C + r + 1 - 2 * h]?) :
    Manacher.PalAt word (C + h) (r + 1 - h) :=
  reshift_of_palAt_period word C h r hin hcur hstep hsmall hend
    ((periodOn_of_palAt_pair hin hout).mono (by omega) (le_refl _)) hpred

#print axioms reshift_of_palAt_pair

#print axioms periodOn_union
#print axioms hasPeriod_slice_iff
#print axioms encoded_periodOn_even
#print axioms periodOn_mirror

end PalPeg
