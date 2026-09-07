import PalPeg.GSScan

/-!
# 境界ジョブ：凍結窓の回文接頭辞フラグ（オフライン）

`ALGORITHM_SPEC.md` §3（中央回文ジョブ）の **L4 / L5 / L9** を添字レベルで形式化する。
凍結された窓 `x`（長さ `m`）に対し、`ℓ = 0..m` の各長さについて
`IsPal (x.take ℓ)` を判定するフラグ列を、**定数個の整数カーソルだけ**で走る
Galil–Seiferas 型の照合で計算する（Manacher と違い数値配列を持たない＝
チューリング機械に落とせる）。

* **L4 / L9（双対性）** — `overlap_iff_palPrefix`：`ℓ ≤ m` のとき
  「パターン `x` とテキスト `x.reverse` の長さ `ℓ` の右重なり」＝
  「`x.take ℓ` が回文」。分離記号 `#` を使う `u # reverse(u)` の版
  (`GS_OVERLAP.md:51-54`) の代わりに、二視点版 (`GS_LOCAL_CLOCK.md:126-140`,
  `gs_dual_flags.py`) を採る。分離記号は最終入力に許されないので、この方が
  形式化にも実装にも素直である。
* **L5（段の縮小）** — 長さ `L` の段はパターン `x.take L`、テキスト
  `(x.take L).reverse` を走査し、長さ `ℓ ≥ max 1 (2s)` の重なりだけを報告する
  (`gs_overlap.py:120-143`)。残りは `L := max 1 (2s) - 1` の新しい段に回る。
  `(k-1)s < L`（L1）より段長は幾何級数的に縮み、総仕事量は線形。
* 段の中では、テキスト末尾に達した**部分一致**を読む。`GS_OVERLAP.md:36-45` の規則を
  そのまま写す：`v` の一致長 `q` を伸ばし、`pos + s + q = L`（フロンティア）に達したら
  短い接頭辞 `u` を直接照合して `ℓ = L - pos` を報告し、しかるのち通常の GS ずらしを行う。

分解 `(s, p₁, r)` の**存在**は別ファイル（`GSDecomp.lean`）の仕事なので、ここでは
各段のパターンについて `StageOK`（`KSimple` ＋ charging 不等式 ＋ L1）を仮定として受け取る。

## 参照実装との差分（意図的なもの）

* `gs_overlap.iter_borders` は第一段だけ `position = 1` から始める（語全体は**真の**
  境界でないため）。ここは二視点版なので、長さ `ℓ = |x|`（＝`x` 自身が回文）も
  正当な答えであり、どの段も `pos = 0` から始める。分離記号版で言えば
  `x # reverse(x)`（長さ `2m+1`）の長さ `ℓ ≤ m` の境界はすべて真の境界なので、
  除外すべき重なりはそもそも現れない。
* 仕事量 `ovCost` は、フロンティアでの短い接頭辞の照合を、途中で失敗しても常に
  `|u|` 回と数える（保守的）。分解 `dec` 自身の計算コストは別ファイルの担当なので
  数えていない（段ごとに線形で、同じ幾何級数に乗る）。
* `minimum = max 1 (2s)`、次段長 `max 1 (2s) - 1`、ずらし規則、フロンティアでの
  直接照合という段の骨格は `gs_overlap.py:120-146` のままである。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 0. 添字の小道具 -/

theorem matchLen_of_eq_index {v T : List α} {i i' q q' : ℕ} (hi : i = i') (hq : q' ≤ q)
    (hm : MatchLen v T i q) : MatchLen v T i' q' := by
  subst hi; exact matchLen_mono hm hq

/-- パターンを `u ++ v` に分けたときの部分一致の分解。`occAt_append_iff` の部分一致版。 -/
theorem matchLen_append_iff {u v T : List α} {i n : ℕ} (h : u.length ≤ n) :
    MatchLen (u ++ v) T i n ↔
      MatchLen u T i u.length ∧ MatchLen v T (i + u.length) (n - u.length) := by
  constructor
  · intro H
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hh := H j (by omega)
      rwa [List.getElem?_append_left hj] at hh
    · have hh := H (u.length + j) (by omega)
      rw [List.getElem?_append_right (by omega),
        show u.length + j - u.length = j from by omega] at hh
      rw [← hh]; exact getElem?_congr (by omega)
  · rintro ⟨h1, h2⟩ j hj
    by_cases hju : j < u.length
    · rw [List.getElem?_append_left hju]; exact h1 j hju
    · rw [List.getElem?_append_right (by omega)]
      have hh := h2 (j - u.length) (by omega)
      rw [← hh]; exact getElem?_congr (by omega)

/-- 一致部分の内側にもう一つ**部分**一致があれば、そのずれは一致部分の周期になる
（`hasPeriod_of_occ` の部分一致版：完全な出現は要らない）。 -/
theorem hasPeriod_of_partialMatch {v T : List α} {a q δ : ℕ} (hq : q ≤ v.length)
    (hm : MatchLen v T a q) (hm2 : MatchLen v T (a + δ) (q - δ)) :
    HasPeriod (v.take q) δ := by
  have hlen : (v.take q).length = q := by simp only [List.length_take]; omega
  intro i hi
  rw [hlen] at hi
  rw [List.getElem?_take_of_lt (show i < q by omega), List.getElem?_take_of_lt hi]
  have h1 : T[a + δ + i]? = v[i]? := hm2 i (by omega)
  have h2 : T[a + (i + δ)]? = v[i + δ]? := hm _ hi
  rw [← h1, ← h2]
  exact getElem?_congr (by omega)

/-- **L2（安全なずらし・部分一致版）**：`KSimple` のもとで、ずらし幅より短い周期はない。 -/
theorem no_short_period {v : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    {q δ : ℕ} (hq : q ≤ v.length) (hδ : 0 < δ) (hδ' : δ < gsShift k p₁ r q)
    (hper : HasPeriod (v.take q) δ) : False := by
  unfold gsShift at hδ'
  split_ifs at hδ' with hc
  · have hkd : k * δ ≤ q :=
      le_trans (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_of_lt hδ')) hc.1
    have := hK.no_small_repeat q δ hq hδ hkd hper
    omega
  · have hkd : k * δ ≤ q := by
      have hδ2 : δ + 1 ≤ ceilDiv q k := by omega
      have h2 : k * (δ + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul (Nat.le_refl k) hδ2
      have h3 : k * ceilDiv q k ≤ q + k - 1 := (ceilDiv_bounds hk).2
      have h4 : k * (δ + 1) = k * δ + k := by ring
      omega
    obtain ⟨h1, h2⟩ := hK.no_small_repeat q δ hq hδ hkd hper
    exact hc ⟨le_trans (Nat.mul_le_mul (Nat.le_refl k) h1) hkd, h2⟩

theorem ceilDiv_le_max {q k : ℕ} (hk : 0 < k) : ceilDiv q k ≤ max 1 q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h0 : (0 + k - 1) / k = 0 := Nat.div_eq_of_lt (by omega)
    unfold ceilDiv
    omega
  · obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
    have hmul : (a + 1) + (b + 1) - 1 ≤ (a + 1) * (b + 1) := by
      calc (a + 1) + (b + 1) - 1 = a + b + 1 := by omega
        _ ≤ a * b + (a + b + 1) := Nat.le_add_left _ _
        _ = (a + 1) * (b + 1) := by ring
    unfold ceilDiv
    calc ((a + 1) + (b + 1) - 1) / (b + 1) ≤ ((a + 1) * (b + 1)) / (b + 1) :=
          Nat.div_le_div_right hmul
      _ = a + 1 := Nat.mul_div_cancel _ (Nat.succ_pos b)
      _ ≤ max 1 (a + 1) := le_max_right _ _

theorem gsShift_le_max {k p₁ r q : ℕ} (hk : 0 < k) : gsShift k p₁ r q ≤ max 1 q := by
  have hpk : ∀ p : ℕ, p ≤ k * p := by
    intro p; have := Nat.mul_le_mul hk (Nat.le_refl p); simpa using this
  unfold gsShift
  split_ifs with hc
  · have := hpk p₁
    have := hc.1
    omega
  · have := ceilDiv_le_max (q := q) hk
    omega

/-- ずらし幅と保持する一致長の合計は `max 1 q` を越えない：フロンティアを越えない。 -/
theorem gsShift_add_gsNextQ_le {k p₁ r q : ℕ} (hk : 0 < k) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ max 1 q := by
  have hpk : ∀ p : ℕ, p ≤ k * p := by
    intro p; have := Nat.mul_le_mul hk (Nat.le_refl p); simpa using this
  unfold gsShift gsNextQ
  split_ifs with hc
  · have := hpk p₁
    have := hc.1
    omega
  · have := ceilDiv_le_max (q := q) hk
    omega

theorem gsShift_add_gsNextQ_le_succ {k p₁ r q : ℕ} (hk : 0 < k) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ q + 1 :=
  le_trans (gsShift_add_gsNextQ_le hk) (max_le (by omega) (by omega))

theorem gsShift_add_gsNextQ_le_self {k p₁ r q : ℕ} (hk : 0 < k) (hq : 1 ≤ q) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ q :=
  le_trans (gsShift_add_gsNextQ_le hk) (max_le hq (Nat.le_refl _))

/-- ずらしのあとも保持部分は本当に一致している（`safe_shift_matchLen` の両枝版）。 -/
theorem gs_matched {v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) {a q : ℕ}
    (hq : q ≤ v.length) (hm : MatchLen v T a q) :
    MatchLen v T (a + gsShift k p₁ r q) (gsNextQ k p₁ r q) := by
  by_cases hc : k * p₁ ≤ q ∧ q ≤ r
  · have hs : gsShift k p₁ r q = p₁ := by unfold gsShift; rw [if_pos hc]
    have hn : gsNextQ k p₁ r q = q - p₁ := by unfold gsNextQ; rw [if_pos hc]
    rw [hs, hn]
    exact safe_shift_matchLen hK hq hc.2 hm
  · have hn : gsNextQ k p₁ r q = 0 := by unfold gsNextQ; rw [if_neg hc]
    rw [hn]
    exact matchLen_zero v T _

/-! ## 1. L4 / L9：右重なりと回文接頭辞の双対性 -/

/-- 長さ `ℓ` の**右重なり**：パターン `y` がテキスト `T` の右端に接して部分一致する。
`gs_overlap.iter_borders` の候補位置 `position = |T| - ℓ` に対応する。 -/
def OverlapAt (y T : List α) (ℓ : ℕ) : Prop := MatchLen y T (T.length - ℓ) ℓ

theorem overlapAt_getElem? {y : List α} {ℓ : ℕ} (h : ℓ ≤ y.length) :
    OverlapAt y y.reverse ℓ ↔ ∀ j, j < ℓ → y[j]? = y[ℓ - 1 - j]? := by
  unfold OverlapAt MatchLen
  rw [List.length_reverse]
  constructor
  · intro H j hj
    have hidx : y.length - ℓ + j < y.length := by omega
    have hh := H j hj
    rw [List.getElem?_reverse hidx,
      show y.length - 1 - (y.length - ℓ + j) = ℓ - 1 - j from by omega] at hh
    exact hh.symm
  · intro H j hj
    have hidx : y.length - ℓ + j < y.length := by omega
    rw [List.getElem?_reverse hidx,
      show y.length - 1 - (y.length - ℓ + j) = ℓ - 1 - j from by omega]
    exact (H j hj).symm

theorem isPal_take_getElem? {y : List α} {ℓ : ℕ} (h : ℓ ≤ y.length) :
    IsPal (y.take ℓ) ↔ ∀ j, j < ℓ → y[j]? = y[ℓ - 1 - j]? := by
  have hlen : (y.take ℓ).length = ℓ := by simp only [List.length_take]; omega
  rw [isPal_iff_getElem?, hlen]
  constructor
  · intro H j hj
    have hh := H j hj
    rwa [List.getElem?_take_of_lt hj,
      List.getElem?_take_of_lt (show ℓ - 1 - j < ℓ from by omega)] at hh
  · intro H j hj
    rw [List.getElem?_take_of_lt hj,
      List.getElem?_take_of_lt (show ℓ - 1 - j < ℓ from by omega)]
    exact H j hj

/-- **L9（二視点）**：パターン `y`／テキスト `y.reverse` の長さ `ℓ` の右重なりは、
ちょうど `y.take ℓ` が回文であること。 -/
theorem overlapAt_reverse_iff {y : List α} {ℓ : ℕ} (h : ℓ ≤ y.length) :
    OverlapAt y y.reverse ℓ ↔ IsPal (y.take ℓ) :=
  (overlapAt_getElem? h).trans (isPal_take_getElem? h).symm

/-- **L4（双対性・語の等式版）**：`x.take ℓ` が `x.reverse` の接尾辞であることと、
`x.take ℓ` が回文であることは同値。 -/
theorem overlap_iff_palPrefix {x : List α} {ℓ : ℕ} (h : ℓ ≤ x.length) :
    x.take ℓ = x.reverse.drop (x.length - ℓ) ↔ IsPal (x.take ℓ) := by
  rw [← overlapAt_reverse_iff h]
  unfold OverlapAt MatchLen
  rw [List.length_reverse]
  constructor
  · intro heq j hj
    have hh := congrArg (fun l => l[j]?) heq
    simp only [List.getElem?_drop, List.getElem?_take_of_lt hj] at hh
    exact hh.symm
  · intro H
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_drop]
    split
    · next hlt => exact (H j hlt).symm
    · next hge =>
      rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]

/-! ## 2. 段の走査（GS 規則で右重なりを列挙する） -/

section Scan

variable [DecidableEq α]

/-- 重なり走査の一歩。`GS_OVERLAP.md:31-33`, `gs_overlap.py:126-143`。
フロンティア（`pos + |u| + q = |T|`）に達したとき、および不一致のときにずらす。 -/
def ovStep (u v T : List α) (k p₁ r : ℕ) (st : ScanState) : ScanState :=
  if st.pos + u.length + st.q = T.length then
    ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩
  else if T[st.pos + u.length + st.q]? = v[st.q]? then
    ⟨st.pos, st.q + 1⟩
  else
    ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩

/-- 走査本体：候補位置が `|T| - minimum` を越えるまで走り、フロンティアに達して
短い接頭辞 `u` も一致した位置で重なり長 `|T| - pos` を報告する。 -/
def ovRun (u v T : List α) (k p₁ r minimum : ℕ) : ℕ → ScanState → List ℕ
  | 0, _ => []
  | fuel + 1, st =>
      if T.length < st.pos + minimum then []
      else if st.pos + u.length + st.q = T.length ∧ MatchLen u T st.pos u.length then
        (T.length - st.pos) :: ovRun u v T k p₁ r minimum fuel (ovStep u v T k p₁ r st)
      else ovRun u v T k p₁ r minimum fuel (ovStep u v T k p₁ r st)

/-- 走査の仕事量：一歩につき 1、フロンティアではさらに `u` の直接照合 `|u|` 回。 -/
def ovCost (u v T : List α) (k p₁ r minimum : ℕ) : ℕ → ScanState → ℕ
  | 0, _ => 0
  | fuel + 1, st =>
      if T.length < st.pos + minimum then 0
      else
        (if st.pos + u.length + st.q = T.length then 1 + u.length else 1)
          + ovCost u v T k p₁ r minimum fuel (ovStep u v T k p₁ r st)

/-- 走査の不変条件：`v` の部分が実際に一致していて、フロンティアを越えていない。 -/
structure OvInv (u v T : List α) (st : ScanState) : Prop where
  matched : MatchLen v T (st.pos + u.length) st.q
  front : st.pos + u.length + st.q ≤ T.length

omit [DecidableEq α] in
theorem OvInv.q_le {u v T : List α} {st : ScanState} (h : OvInv u v T st)
    (hlen : u.length + v.length = T.length) : st.q ≤ v.length := by
  have := h.front; omega

theorem ovStep_pos_mono (u v T : List α) (k p₁ r : ℕ) (st : ScanState) :
    st.pos ≤ (ovStep u v T k p₁ r st).pos := by
  unfold ovStep; split_ifs <;> simp

omit [DecidableEq α] in
/-- 走査中の状態でフロンティアに達しているなら、一致長 `q` は `|u|` 以上かつ正。
`minimum ≥ max 1 (2|u|)` が効くところ（`GS_OVERLAP.md:38-39`）。 -/
theorem front_q_ge {u T : List α} {minimum : ℕ} {st : ScanState}
    (hmin : max 1 (2 * u.length) ≤ minimum) (hrange : st.pos + minimum ≤ T.length)
    (hfront : st.pos + u.length + st.q = T.length) : u.length ≤ st.q ∧ 1 ≤ st.q := by
  omega

theorem ovStep_inv {u v T : List α} {k p₁ r minimum : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) {st : ScanState}
    (hrange : st.pos + minimum ≤ T.length) (h : OvInv u v T st) :
    OvInv u v T (ovStep u v T k p₁ r st) := by
  have hq : st.q ≤ v.length := h.q_le hlen
  have hmatched : MatchLen v T (st.pos + gsShift k p₁ r st.q + u.length)
      (gsNextQ k p₁ r st.q) :=
    matchLen_of_eq_index (i := st.pos + u.length + gsShift k p₁ r st.q) (by omega)
      (Nat.le_refl _) (gs_matched hK hq h.matched)
  have hsucc := gsShift_add_gsNextQ_le_succ (k := k) (p₁ := p₁) (r := r) (q := st.q) hk
  have hfr := h.front
  unfold ovStep
  split_ifs with h1 h2
  · have hge := front_q_ge (T := T) hmin hrange h1
    have hself := gsShift_add_gsNextQ_le_self (k := k) (p₁ := p₁) (r := r) (q := st.q)
      hk hge.2
    exact ⟨hmatched, by simp only []; omega⟩
  · exact ⟨by simpa using matchLen_succ h.matched h2, by simp only []; omega⟩
  · exact ⟨hmatched, by simp only []; omega⟩

/-! ### ポテンシャル -/

omit [DecidableEq α] in
theorem gs_phi_shift_lt {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁) (st : ScanState) :
    Phi k st < Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
  have hpk : p₁ ≤ k * p₁ := by
    have := Nat.mul_le_mul hk (Nat.le_refl p₁); simpa using this
  simp only [Phi]
  unfold gsShift gsNextQ
  split_ifs with hc
  · have e1 : (k + 1) * (st.pos + p₁) = (k + 1) * st.pos + (k * p₁ + p₁) := by ring
    have e2 : 0 < k * p₁ := Nat.mul_pos hk hp
    have e3 := hc.1
    omega
  · have hcm : st.q ≤ k * ceilDiv st.q k := (ceilDiv_bounds hk).1
    have hle : k * ceilDiv st.q k ≤ k * max 1 (ceilDiv st.q k) :=
      Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right _ _)
    have e1 : (k + 1) * (st.pos + max 1 (ceilDiv st.q k))
        = (k + 1) * st.pos + (k * max 1 (ceilDiv st.q k) + max 1 (ceilDiv st.q k)) := by ring
    have e2 : 1 ≤ max 1 (ceilDiv st.q k) := Nat.le_max_left _ _
    omega

/-- **L3（ポテンシャル）**：重なり走査でも `Φ = (k+1)·pos + q` は毎歩真に増加する。 -/
theorem ovStep_phi_lt {u v T : List α} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁)
    (st : ScanState) : Phi k st < Phi k (ovStep u v T k p₁ r st) := by
  unfold ovStep
  split_ifs with h1 h2
  · exact gs_phi_shift_lt hk hp st
  · simp only [Phi]; omega
  · exact gs_phi_shift_lt hk hp st

/-! ### 健全性 -/

/-- **段の健全性**：報告される長さは `minimum` 以上の真の右重なり。 -/
theorem ovRun_sound {u v T : List α} {k p₁ r minimum : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) :
    ∀ (fuel : ℕ) (st : ScanState), OvInv u v T st → ∀ ℓ,
      ℓ ∈ ovRun u v T k p₁ r minimum fuel st →
      minimum ≤ ℓ ∧ ℓ + st.pos ≤ T.length ∧ OverlapAt (u ++ v) T ℓ := by
  intro fuel
  induction fuel with
  | zero => intro st _ ℓ hℓ; simp [ovRun] at hℓ
  | succ fuel ih =>
    intro st hinv ℓ hℓ
    have hfront := hinv.front
    simp only [ovRun] at hℓ
    split_ifs at hℓ with hstop hrep
    · simp at hℓ
    · rcases List.mem_cons.mp hℓ with rfl | hℓ
      · refine ⟨by omega, by omega, ?_⟩
        unfold OverlapAt
        rw [show T.length - (T.length - st.pos) = st.pos from by omega]
        refine (matchLen_append_iff (by omega)).mpr ⟨hrep.2, ?_⟩
        exact matchLen_of_eq_index rfl (by omega) hinv.matched
      · obtain ⟨h1, h2, h3⟩ :=
          ih _ (ovStep_inv hK hk hlen hmin (by omega) hinv) ℓ hℓ
        have := ovStep_pos_mono u v T k p₁ r st
        exact ⟨h1, by omega, h3⟩
    · obtain ⟨h1, h2, h3⟩ := ih _ (ovStep_inv hK hk hlen hmin (by omega) hinv) ℓ hℓ
      have := ovStep_pos_mono u v T k p₁ r st
      exact ⟨h1, by omega, h3⟩

/-! ### 完全性（L2：候補位置を飛ばさない） -/

/-- **L2（安全なずらし）**：右重なりの候補位置を追い越さない。完全な出現は要らず、
不変条件 `pos + |u| + q ≤ |T|` のおかげで部分一致だけで周期が取れる。 -/
theorem ovStep_pos_le {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hlen : u.length + v.length = T.length) {st : ScanState} (hinv : OvInv u v T st)
    {ℓ : ℕ} (hov : OverlapAt (u ++ v) T ℓ) (hu : u.length ≤ ℓ) (hℓT : ℓ ≤ T.length)
    (hlt : st.pos + ℓ < T.length) :
    (ovStep u v T k p₁ r st).pos + ℓ ≤ T.length := by
  have hfront := hinv.front
  have hq : st.q ≤ v.length := hinv.q_le hlen
  have hv : MatchLen v T (T.length - ℓ + u.length) (ℓ - u.length) :=
    ((matchLen_append_iff hu).mp hov).2
  have hshift : st.pos + gsShift k p₁ r st.q ≤ T.length - ℓ := by
    by_contra hcon
    have hδ : 0 < T.length - ℓ - st.pos := by omega
    have hδ' : T.length - ℓ - st.pos < gsShift k p₁ r st.q := by omega
    have hm2 : MatchLen v T (st.pos + u.length + (T.length - ℓ - st.pos))
        (st.q - (T.length - ℓ - st.pos)) :=
      matchLen_of_eq_index (by omega) (by omega) hv
    exact no_short_period hK hk hq hδ hδ'
      (hasPeriod_of_partialMatch hq hinv.matched hm2)
  unfold ovStep
  split_ifs <;> simp only [] <;> omega

/-- **段の完全性**：`minimum ≤ ℓ` の右重なりは必ず報告される。 -/
theorem ovRun_complete {u v T : List α} {k p₁ r minimum : ℕ} (hK : KSimple v k p₁ r)
    (hk : 0 < k) (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) {ℓ : ℕ}
    (hov : OverlapAt (u ++ v) T ℓ) (hℓ : minimum ≤ ℓ) (hℓT : ℓ ≤ T.length) :
    ∀ (fuel : ℕ) (st : ScanState), OvInv u v T st → st.pos + ℓ ≤ T.length →
      (k + 1) * T.length + v.length + 1 ≤ Phi k st + fuel →
      ℓ ∈ ovRun u v T k p₁ r minimum fuel st := by
  have hu : u.length ≤ ℓ := by omega
  have hvm : MatchLen v T (T.length - ℓ + u.length) (ℓ - u.length) :=
    ((matchLen_append_iff hu).mp hov).2
  have hum : MatchLen u T (T.length - ℓ) u.length := ((matchLen_append_iff hu).mp hov).1
  intro fuel
  induction fuel with
  | zero =>
    intro st hinv hpos hf
    exfalso
    have h1 : st.pos ≤ T.length := by have := hinv.front; omega
    have h2 : st.q ≤ v.length := hinv.q_le hlen
    have h3 : (k + 1) * st.pos ≤ (k + 1) * T.length := Nat.mul_le_mul (Nat.le_refl _) h1
    have h4 : Phi k st = (k + 1) * st.pos + st.q := rfl
    omega
  | succ fuel ih =>
    intro st hinv hpos hf
    have hfront := hinv.front
    have hstep := ovStep_inv hK hk hlen hmin (by omega) hinv
    have hphi := ovStep_phi_lt (u := u) (v := v) (T := T) (p₁ := p₁) (r := r) hk
      hK.period_pos st
    have hf' : (k + 1) * T.length + v.length + 1 ≤ Phi k (ovStep u v T k p₁ r st) + fuel := by
      omega
    simp only [ovRun]
    rw [if_neg (by omega : ¬ (T.length < st.pos + minimum))]
    by_cases hi : st.pos + ℓ = T.length
    · by_cases hfr : st.pos + u.length + st.q = T.length
      · rw [if_pos ⟨hfr, matchLen_of_eq_index (by omega) (Nat.le_refl _) hum⟩,
          show T.length - st.pos = ℓ from by omega]
        exact List.mem_cons_self
      · have hcomp : T[st.pos + u.length + st.q]? = v[st.q]? := by
          have hh := hvm st.q (by omega)
          rw [← hh]
          exact getElem?_congr (by omega)
        have hsame : (ovStep u v T k p₁ r st).pos = st.pos := by
          unfold ovStep; rw [if_neg hfr, if_pos hcomp]
        rw [if_neg (by tauto)]
        exact ih _ hstep (by omega) hf'
    · have hposle : (ovStep u v T k p₁ r st).pos + ℓ ≤ T.length :=
        ovStep_pos_le hK hk hlen hinv hov hu hℓT (by omega)
      have hmem := ih _ hstep hposle hf'
      split_ifs
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem

/-! ## 3. 段（パターン `y`、テキスト `y.reverse`） -/

/-- 一段の走査。パターン `y`、テキスト `y.reverse`、最短重なり長 `max 1 (2s)`
（`gs_overlap.py:120-143`）。 -/
def stageRun (y : List α) (k s p₁ r fuel : ℕ) : List ℕ :=
  ovRun (y.take s) (y.drop s) y.reverse k p₁ r (max 1 (2 * s)) fuel ⟨0, 0⟩

/-- **一段の仕様**：報告される長さの集合はちょうど
`{ℓ | max 1 (2s) ≤ ℓ ≤ |y| かつ y.take ℓ が回文}`。 -/
theorem stageRun_mem_iff {y : List α} {k s p₁ r fuel : ℕ} (hk : 0 < k) (hs : s ≤ y.length)
    (hK : KSimple (y.drop s) k p₁ r)
    (hfuel : (k + 1) * y.length + y.length + 1 ≤ fuel) (ℓ : ℕ) :
    ℓ ∈ stageRun y k s p₁ r fuel ↔ max 1 (2 * s) ≤ ℓ ∧ ℓ ≤ y.length ∧ IsPal (y.take ℓ) := by
  have hut : (y.take s).length = s := by simp only [List.length_take]; omega
  have hvt : (y.drop s).length = y.length - s := by simp only [List.length_drop]
  have hTt : (y.reverse).length = y.length := by simp
  have hlen : (y.take s).length + (y.drop s).length = (y.reverse).length := by omega
  have hmin : max 1 (2 * (y.take s).length) ≤ max 1 (2 * s) := by rw [hut]
  have happ : y.take s ++ y.drop s = y := List.take_append_drop s y
  have hinv0 : OvInv (y.take s) (y.drop s) y.reverse ⟨0, 0⟩ :=
    ⟨by simpa using matchLen_zero (y.drop s) y.reverse _, by simp only []; omega⟩
  constructor
  · intro hmem
    obtain ⟨h1, h2, h3⟩ := ovRun_sound hK hk hlen hmin _ _ hinv0 ℓ hmem
    rw [happ] at h3
    refine ⟨h1, by omega, ?_⟩
    exact (overlapAt_reverse_iff (by omega)).mp h3
  · rintro ⟨h1, h2, h3⟩
    have hov : OverlapAt (y.take s ++ y.drop s) y.reverse ℓ := by
      rw [happ]; exact (overlapAt_reverse_iff h2).mpr h3
    have hphi0 : Phi k (⟨0, 0⟩ : ScanState) = 0 := by simp [Phi]
    have hgoal : (k + 1) * (y.reverse).length + (y.drop s).length + 1
        ≤ Phi k (⟨0, 0⟩ : ScanState) + fuel := by
      rw [hTt, hvt, hphi0]; omega
    have hz : (⟨0, 0⟩ : ScanState).pos = 0 := rfl
    exact ovRun_complete hK hk hlen hmin hov h1 (by omega) fuel ⟨0, 0⟩ hinv0
      (by omega) hgoal

/-! ### 仕事量（`u` の直接照合をずらしに付け替える） -/

omit [DecidableEq α] in
theorem gsNextQ_le {k p₁ r q : ℕ} : gsNextQ k p₁ r q ≤ q := by
  unfold gsNextQ; split_ifs <;> omega

omit [DecidableEq α] in
/-- **charging（`GS_OVERLAP.md:47-50`）**：報告位置での短い接頭辞の照合 `|u|` 回は、
続くずらしのポテンシャル増分に付け替えられる。`c ≤ q`（報告では `q ≥ |u|`）と
`c ≤ k·p₁`（分解の L1 由来）が効く。 -/
theorem gs_charge {k p₁ r q c : ℕ} (hk : 0 < k) (hp : 0 < p₁) (_hq : 1 ≤ q)
    (hcq : c ≤ q) (hchg : c ≤ k * p₁) (pos : ℕ) :
    1 + c ≤ (k + 1) *
      (Phi k ⟨pos + gsShift k p₁ r q, gsNextQ k p₁ r q⟩ - Phi k ⟨pos, q⟩) := by
  have hpk : p₁ ≤ k * p₁ := by
    have := Nat.mul_le_mul hk (Nat.le_refl p₁); simpa using this
  have hkp : 0 < k * p₁ := Nat.mul_pos hk hp
  simp only [Phi]
  unfold gsShift gsNextQ
  split_ifs with hcond
  · have hpq : p₁ ≤ q := le_trans hpk hcond.1
    have e : (k + 1) * (pos + p₁) = (k + 1) * pos + (k * p₁ + p₁) := by ring
    have hd : (k + 1) * (pos + p₁) + (q - p₁) - ((k + 1) * pos + q) = k * p₁ := by omega
    rw [hd]
    have h2 : 2 * (k * p₁) ≤ (k + 1) * (k * p₁) :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    omega
  · have hS1 : 1 ≤ max 1 (ceilDiv q k) := le_max_left _ _
    have hkS : q ≤ k * max 1 (ceilDiv q k) :=
      le_trans (ceilDiv_bounds hk).1 (Nat.mul_le_mul (Nat.le_refl k) (le_max_right _ _))
    have e : (k + 1) * (pos + max 1 (ceilDiv q k))
        = (k + 1) * pos + (k * max 1 (ceilDiv q k) + max 1 (ceilDiv q k)) := by ring
    have hd : (k + 1) * (pos + max 1 (ceilDiv q k)) + 0 - ((k + 1) * pos + q)
        = (k + 1) * max 1 (ceilDiv q k) - q := by
      have e2 : (k + 1) * max 1 (ceilDiv q k)
          = k * max 1 (ceilDiv q k) + max 1 (ceilDiv q k) := by ring
      omega
    rw [hd]
    have hge : max 1 (ceilDiv q k) ≤ (k + 1) * max 1 (ceilDiv q k) - q := by
      have e2 : (k + 1) * max 1 (ceilDiv q k)
          = k * max 1 (ceilDiv q k) + max 1 (ceilDiv q k) := by ring
      omega
    calc 1 + c ≤ (k + 1) * max 1 (ceilDiv q k) := by
          have e2 : (k + 1) * max 1 (ceilDiv q k)
              = k * max 1 (ceilDiv q k) + max 1 (ceilDiv q k) := by ring
          omega
      _ ≤ (k + 1) * ((k + 1) * max 1 (ceilDiv q k) - q) :=
          Nat.mul_le_mul (Nat.le_refl _) hge

theorem ovStep_phi_le {u v T : List α} {k p₁ r minimum : ℕ} (hk : 0 < k)
    (hlen : u.length + v.length = T.length) {st : ScanState} (hinv : OvInv u v T st)
    (hmin : 1 ≤ minimum) (hrange : st.pos + minimum ≤ T.length) :
    Phi k (ovStep u v T k p₁ r st) ≤ (k + 1) * (2 * T.length) + T.length := by
  have hq : st.q ≤ v.length := hinv.q_le hlen
  have hfront := hinv.front
  have hpos : st.pos ≤ T.length := by omega
  have hsm := gsShift_le_max (k := k) (p₁ := p₁) (r := r) (q := st.q) hk
  have hnq : gsNextQ k p₁ r st.q ≤ st.q := gsNextQ_le
  have hp2 : (ovStep u v T k p₁ r st).pos ≤ 2 * T.length
      ∧ (ovStep u v T k p₁ r st).q ≤ T.length := by
    unfold ovStep
    split_ifs <;> simp only [] <;> omega
  have hmul : (k + 1) * (ovStep u v T k p₁ r st).pos ≤ (k + 1) * (2 * T.length) :=
    Nat.mul_le_mul (Nat.le_refl _) hp2.1
  simp only [Phi]
  omega

/-- **L3（段の線形性）**：一段の仕事量はポテンシャルの残りに比例する。 -/
theorem ovCost_le {u v T : List α} {k p₁ r minimum : ℕ} (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) (hchg : u.length ≤ k * p₁) :
    ∀ (fuel : ℕ) (st : ScanState), OvInv u v T st →
      ovCost u v T k p₁ r minimum fuel st
        ≤ (k + 1) * ((k + 1) * (2 * T.length) + T.length - Phi k st) := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [ovCost]
  | succ fuel ih =>
    intro st hinv
    simp only [ovCost]
    by_cases hstop : T.length < st.pos + minimum
    · rw [if_pos hstop]; exact Nat.zero_le _
    · rw [if_neg hstop]
      have hrange : st.pos + minimum ≤ T.length := by omega
      have hstep := ovStep_inv hK hk hlen hmin hrange hinv
      have hlt := ovStep_phi_lt (u := u) (v := v) (T := T) (p₁ := p₁) (r := r) hk
        hK.period_pos st
      have hcap := ovStep_phi_le (u := u) (v := v) (T := T) (k := k) (p₁ := p₁) (r := r)
        (minimum := minimum) hk hlen hinv (by omega) hrange
      have hself : Phi k st ≤ (k + 1) * (2 * T.length) + T.length := by omega
      have key : (k + 1) * ((k + 1) * (2 * T.length) + T.length - Phi k (ovStep u v T k p₁ r st))
          + (k + 1) * (Phi k (ovStep u v T k p₁ r st) - Phi k st)
          = (k + 1) * ((k + 1) * (2 * T.length) + T.length - Phi k st) := by
        rw [← Nat.mul_add]; congr 1; omega
      have hcost : (if st.pos + u.length + st.q = T.length then 1 + u.length else 1)
          ≤ (k + 1) * (Phi k (ovStep u v T k p₁ r st) - Phi k st) := by
        split_ifs with hfr
        · have hge := front_q_ge (T := T) hmin hrange hfr
          have hstepeq : ovStep u v T k p₁ r st
              = ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
            unfold ovStep; rw [if_pos hfr]
          rw [hstepeq]
          have := gs_charge (k := k) (p₁ := p₁) (r := r) (q := st.q) (c := u.length)
            hk hK.period_pos hge.2 hge.1 hchg st.pos
          have hst : (⟨st.pos, st.q⟩ : ScanState) = st := rfl
          rw [hst] at this
          exact this
        · have h1 : 1 ≤ Phi k (ovStep u v T k p₁ r st) - Phi k st := by omega
          have := Nat.mul_le_mul (Nat.le_refl (k + 1)) h1
          omega
      have := Nat.add_le_add hcost (ih _ hstep)
      omega

/-! ## 4. 段の縮小（L5）とジョブ全体 -/

/-- 次の段の長さ（`gs_overlap.py:144-146`）。 -/
def nextLen (s : ℕ) : ℕ := max 1 (2 * s) - 1

theorem nextLen_lt {k s L : ℕ} (hk : 4 ≤ k) (hshort : (k - 1) * s < L) : nextLen s < L := by
  have h3 : 3 * s ≤ (k - 1) * s := Nat.mul_le_mul (by omega) (Nat.le_refl s)
  unfold nextLen
  omega

/-- `k = 8` での幾何級数比（`GS_OVERLAP.md:41-42` の `2/(k-1)`）。 -/
theorem nextLen_shrink {s L : ℕ} (hshort : 7 * s < L) : 3 * nextLen s + 1 ≤ L := by
  unfold nextLen
  omega

end Scan

/-- 段（パターン `x.take L`）の前提。分解 `(s, p₁, r)` の**存在**は `GSDecomp.lean` の
仕事なので、ここでは各段について仮定として受け取る。

* `ksimple` — `GSScan.KSimple`（`v = (x.take L).drop s` が `k`-simple）。
* `cut_charge` — `GS_OVERLAP.md:47-50` の `(k-2)s < (k-1)p₁` の帰結（`k ≥ 4` で `s ≤ 2p₁`）。
* `cut_short` — L1 `(k-1)s < L`。段の長さが幾何級数的に縮む根拠。 -/
structure StageOK (x : List α) (k L s p₁ r : ℕ) : Prop where
  cut_le : s ≤ L
  ksimple : KSimple ((x.take L).drop s) k p₁ r
  cut_charge : s ≤ k * p₁
  cut_short : (k - 1) * s < L

/-- `GS_OVERLAP.md:47-50` の形からの導出（`k ≥ 4`）。 -/
theorem cut_charge_of_ratio {k s p₁ : ℕ} (hk : 4 ≤ k) (h : (k - 2) * s < (k - 1) * p₁) :
    s ≤ k * p₁ := by
  have h2 : 2 * s ≤ (k - 2) * s := Nat.mul_le_mul (by omega) (Nat.le_refl s)
  have h3 : (k - 1) * p₁ ≤ 2 * (k * p₁) := by
    calc (k - 1) * p₁ ≤ (2 * k) * p₁ := Nat.mul_le_mul (by omega) (Nat.le_refl p₁)
      _ = 2 * (k * p₁) := by ring
  omega

section Job

variable [DecidableEq α]

/-- **境界ジョブ**：段を縮めながら、`x` の長さ `1..L` の回文接頭辞をすべて列挙する
（`gs_overlap.iter_borders` の二視点版）。 -/
def borderJob (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, L =>
      if L = 0 then []
      else
        stageRun (x.take L) k (dec L).1 (dec L).2.1 (dec L).2.2 ((k + 2) * L + 1)
          ++ borderJob x dec k fuel (nextLen (dec L).1)

/-- ジョブの仕事量（段の起動 1 ＋ 走査歩数 ＋ 短い接頭辞の照合）。 -/
def borderJobCost (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, L =>
      if L = 0 then 0
      else
        1 + ovCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
              (x.take L).reverse k (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
              ((k + 2) * L + 1) ⟨0, 0⟩
          + borderJobCost x dec k fuel (nextLen (dec L).1)

/-- **ジョブの仕様**：報告される長さの集合はちょうど `x` の非空の回文接頭辞長。 -/
theorem borderJob_mem_iff {x : List α} {dec : ℕ → ℕ × ℕ × ℕ} {k : ℕ} (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ∀ (fuel L : ℕ), L ≤ x.length → L < fuel → ∀ ℓ,
      ℓ ∈ borderJob x dec k fuel L ↔ 1 ≤ ℓ ∧ ℓ ≤ L ∧ IsPal (x.take ℓ) := by
  intro fuel
  induction fuel with
  | zero => intro L _ hf; omega
  | succ fuel ih =>
    intro L hL hfuel ℓ
    simp only [borderJob]
    split_ifs with h0
    · subst h0
      simp only [List.not_mem_nil, false_iff, not_and]
      intro h1 h2
      exact absurd h2 (by omega)
    · obtain ⟨hcut, hks, hchg, hshort⟩ := hOK L (by omega) hL
      have hylen : (x.take L).length = L := by simp only [List.length_take]; omega
      have hnext : nextLen (dec L).1 < L := nextLen_lt hk hshort
      have htake : ∀ ℓ', ℓ' ≤ L → (IsPal ((x.take L).take ℓ') ↔ IsPal (x.take ℓ')) := by
        intro ℓ' h
        rw [List.take_take, show min ℓ' L = ℓ' from by omega]
      have hsf : (k + 1) * (x.take L).length + (x.take L).length + 1 ≤ (k + 2) * L + 1 := by
        rw [hylen]
        have e : (k + 1) * L + L + 1 = (k + 2) * L + 1 := by ring
        omega
      have hstage := stageRun_mem_iff (y := x.take L) (k := k) (s := (dec L).1)
        (p₁ := (dec L).2.1) (r := (dec L).2.2) (fuel := (k + 2) * L + 1) (by omega)
        (by omega) hks hsf ℓ
      rw [List.mem_append, hstage, ih (nextLen (dec L).1) (by omega) (by omega) ℓ, hylen]
      constructor
      · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
        · exact ⟨by omega, b, (htake ℓ b).mp c⟩
        · exact ⟨a, by omega, c⟩
      · rintro ⟨a, b, c⟩
        by_cases hcs : max 1 (2 * (dec L).1) ≤ ℓ
        · exact Or.inl ⟨hcs, b, (htake ℓ b).mpr c⟩
        · exact Or.inr ⟨a, by unfold nextLen; omega, c⟩

instance instDecidableIsPal (y : List α) : Decidable (IsPal y) :=
  inferInstanceAs (Decidable (y.reverse = y))

/-- **回文接頭辞フラグ**：`ℓ = 0..|x|` の各長さについて `x.take ℓ` が回文かどうか。 -/
def palPrefixFlagsGS (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : List Bool :=
  (List.range (x.length + 1)).map
    (fun ℓ => decide (ℓ = 0 ∨ ℓ ∈ borderJob x dec k (x.length + 1) x.length))

/-- **主定理（正しさ）**：フラグ列の第 `ℓ` 成分は `IsPal (x.take ℓ)` の真偽。 -/
theorem palPrefixFlagsGS_spec {x : List α} {dec : ℕ → ℕ × ℕ × ℕ} {k : ℕ} (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (ℓ : ℕ) (hℓ : ℓ ≤ x.length) :
    (palPrefixFlagsGS x dec k)[ℓ]? = some (decide (IsPal (x.take ℓ))) := by
  unfold palPrefixFlagsGS
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 1
  rw [decide_eq_decide]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · simp
  · rw [borderJob_mem_iff hk hOK (x.length + 1) x.length (Nat.le_refl _) (by omega) ℓ]
    constructor
    · rintro (h | ⟨_, _, h⟩)
      · omega
      · exact h
    · intro h; exact Or.inr ⟨hpos, hℓ, h⟩

/-- 総仕事量。 -/
def totalSteps (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ :=
  borderJobCost x dec k (x.length + 1) x.length

theorem stageCost_le {x : List α} {dec : ℕ → ℕ × ℕ × ℕ} {k L : ℕ} (hk : 0 < k)
    (hL : L ≤ x.length) (_hone : 1 ≤ L)
    (hOK : StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ovCost ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse k (dec L).2.1 (dec L).2.2 (max 1 (2 * (dec L).1))
      ((k + 2) * L + 1) ⟨0, 0⟩
      ≤ (k + 1) * ((k + 1) * (2 * L) + L) := by
  obtain ⟨hcut, hks, hchg, hshort⟩ := hOK
  have hylen : (x.take L).length = L := by simp only [List.length_take]; omega
  have hut : ((x.take L).take (dec L).1).length = (dec L).1 := by
    simp only [List.length_take]; omega
  have hvt : ((x.take L).drop (dec L).1).length = L - (dec L).1 := by
    simp only [List.length_drop]; omega
  have hTt : ((x.take L).reverse).length = L := by simp only [List.length_reverse]; omega
  have hlen : ((x.take L).take (dec L).1).length + ((x.take L).drop (dec L).1).length
      = ((x.take L).reverse).length := by omega
  have hmin : max 1 (2 * ((x.take L).take (dec L).1).length) ≤ max 1 (2 * (dec L).1) := by
    rw [hut]
  have hinv0 : OvInv ((x.take L).take (dec L).1) ((x.take L).drop (dec L).1)
      (x.take L).reverse ⟨0, 0⟩ :=
    ⟨by simpa using matchLen_zero _ _ _, by simp only []; omega⟩
  have hphi0 : Phi k (⟨0, 0⟩ : ScanState) = 0 := by simp [Phi]
  have := ovCost_le hks hk hlen hmin (by rw [hut]; exact hchg) ((k + 2) * L + 1) ⟨0, 0⟩ hinv0
  rw [hTt, hphi0] at this
  omega

/-- **主定理（線形時間）**：`k = 8` のとき総仕事量は `258·|x|` 以下。 -/
theorem borderJobCost_le {x : List α} {dec : ℕ → ℕ × ℕ × ℕ}
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x 8 L (dec L).1 (dec L).2.1 (dec L).2.2) :
    ∀ (fuel L : ℕ), L ≤ x.length → borderJobCost x dec 8 fuel L ≤ 258 * L := by
  intro fuel
  induction fuel with
  | zero => intro L _; simp [borderJobCost]
  | succ fuel ih =>
    intro L hL
    simp only [borderJobCost]
    split_ifs with h0
    · exact Nat.zero_le _
    · have hOKL := hOK L (by omega) hL
      have hstage := stageCost_le (dec := dec) (by omega) hL (by omega) hOKL
      have hshort := hOKL.cut_short
      have hshrink : 3 * nextLen (dec L).1 + 1 ≤ L := nextLen_shrink (by omega)
      have hrec := ih (nextLen (dec L).1) (by omega)
      have h86 : 258 * nextLen (dec L).1 ≤ 86 * (L - 1) := by
        have : 86 * (3 * nextLen (dec L).1) ≤ 86 * (L - 1) :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        omega
      omega

/-- **主定理（線形時間・総和形）**。 -/
theorem palPrefixFlagsGS_work {x : List α} {dec : ℕ → ℕ × ℕ × ℕ}
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x 8 L (dec L).1 (dec L).2.1 (dec L).2.2) :
    totalSteps x dec 8 ≤ 258 * x.length :=
  borderJobCost_le hOK (x.length + 1) x.length (Nat.le_refl _)

/-! ## 5. 小例による健全性チェック -/

section Examples

/-- 周期を持たない分解（`period = None`, `r = 0`）を各段に与えた場合。 -/
example : palPrefixFlagsGS ([0, 1, 0] : List ℕ) (fun L => (0, L + 1, 0)) 8
    = [true, true, false, true] := by decide

example : palPrefixFlagsGS ([0, 1, 1, 0, 1] : List ℕ) (fun L => (0, L + 1, 0)) 8
    = [true, true, false, false, true, false] := by decide

example : borderJob ([0, 1, 1, 0, 1] : List ℕ) (fun L => (0, L + 1, 0)) 8 6 5 = [4, 1] := by
  decide

/-- 周期ずらしの枝（`k*p₁ ≤ q ≤ r`）を通る例：`v = 0^8` は `p₁ = 1`, `r = 8` で
`8`-simple。段 `L = 9` は `s = 1` なので `ℓ ≥ 2` を報告し、`ℓ = 1` は次段が拾う。 -/
example : palPrefixFlagsGS ((List.replicate 9 0) : List ℕ)
    (fun L => if L = 9 then (1, 1, 8) else (0, L + 1, 0)) 8
    = [true, true, true, true, true, true, true, true, true, true] := by decide

example : borderJob ((List.replicate 9 0) : List ℕ)
    (fun L => if L = 9 then (1, 1, 8) else (0, L + 1, 0)) 8 10 9
    = [9, 8, 7, 6, 5, 4, 3, 2, 1] := by decide

/-- 仕事量は `258·|x|` の見積りよりずっと小さい（見積りは保守的）。 -/
example : borderJobCost ((List.replicate 9 0) : List ℕ)
    (fun L => if L = 9 then (1, 1, 8) else (0, L + 1, 0)) 8 10 9 = 49 := by decide

end Examples

end Job

end PalPeg
