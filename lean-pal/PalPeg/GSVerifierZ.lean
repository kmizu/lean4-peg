import PalPeg.GSVerifier
import PalPeg.GSRealTime

/-!
# ジグザグ接頭辞検証器（巻き戻しの無い `u` 検証） (`GSVerifierZ`)

`PalPeg.GSVerifier` の検証器は、候補ごとに `u` を **先頭から** 照合するので、
ずらしのたびに `U` テープのヘッドを添字 `checked + 1` から `1` へ戻す必要がある。
その巻き戻しは 1 歩で `Θ(checked)` 動作を要し、`PalPeg.PointwiseGap.rewind_not_pointwise`
が示すとおり周期枝では `ΔΦ` で点ごとに償却できない。

本ファイルは、その巻き戻しを **完全に無くす** 設計を抽象レベルで与える。

## 設計

* `u` の照合順序は任意でよい（全位置を照合できれば十分）。そこで検証器は
  **区間 `[lo, hi)`** を「この候補について照合済みの位置の集合」として持ち、
  ヘッド位置 `head ∈ [lo, hi]` と向き `up` を持つ。
* 1 回の単位動作 `zMove` は、ヘッドを 1 セル動かす：
  * 伸ばす向きの端（`up` なら `head = hi`、`down` なら `head = lo`）にいれば
    1 文字照合して区間を 1 伸ばす、
  * 端でなければ（＝反対側の端から戻ってくる途中なら）ただ 1 セル進む、
  * テープ端（`head = |u|` または `head = 0`）に達したら向きを反転する。
* **ずらしのときヘッドは動かさない**（`head` はそのまま、区間は `[head, head)` に
  リセット）。`Txt2` 側は融合ループが `gsShift` だけ右へ進めるので、
  新しい候補位置に対して `U` と `Txt2` は**そのまま整列している**。

したがって 1 歩の費用は常に `O(1)` であり、`Ψ = 2·checked` のような償却項は現れない。

## 締切

`zrem |u| z` を「照合を完了するまでに必要な残り単位動作数」とすると
（`zrem_zero_iff`、`zrem_pred`）、ずらし直後は `zrem ≤ head + |u| ≤ 2|u|` である。
1 歩あたり 2 単位動作を割り当てるので、締切条件は

  `ZDeadline : |u| ≤ |v| - gsNextQ k p₁ r q`   （⟹ `zrem ≤ 2*(|v| - q')`）

となる。現在の `GSRealTime.prefix_verifier_deadline` は
`|u| < 2*(|v| - gsNextQ …)` しか与えない（周期枝では `|v| - q' ≥ p₁` と
`hL1b : (k-2)|u| < (k-1)p₁`、すなわち `k = 8` なら `|u| < 7p₁/6`）ので、
**L1 の切り出し定数を `|u| ≤ p₁` 相当まで強めるか、ずらしのときに近い方の端へ
向きを選ぶ（`zrem ≤ 1.5|u|` になり `1.5·(7/6) = 1.75 < 2` で足りる）必要がある**。
本ファイルは前者を仮定 `ZDeadline` として明示的に持つ。
-/

set_option autoImplicit false

namespace PalPeg
namespace GSVerifierZ

universe w
variable {α : Type w}

/-! ## 1. 状態 -/

/-- ジグザグ検証器の状態：照合済み区間 `[lo, hi)`、ヘッド位置、向き。 -/
structure ZS where
  /-- `U` のヘッド位置（`u` の添字）。 -/
  head : ℕ
  /-- 照合済み区間の下端。 -/
  lo : ℕ
  /-- 照合済み区間の上端（開区間）。 -/
  hi : ℕ
  /-- `true` なら上（右）向き。 -/
  up : Bool
deriving DecidableEq, Repr

/-- 走査状態とジグザグ検証器の状態。 -/
abbrev VStateZ := ScanState × ZS

/-- 照合済み区間の正しさ。 -/
def MatchIv (u T : List α) (i lo hi : ℕ) : Prop :=
  ∀ j, lo ≤ j → j < hi → T[i + j]? = u[j]?

theorem matchIv_empty (u T : List α) (i c : ℕ) : MatchIv u T i c c := by
  intro j h1 h2; omega

/-- 照合完了（区間が `[0, |u|)`）なら `MatchLen`。 -/
theorem matchIv_full {u T : List α} {i lo hi : ℕ} (h : MatchIv u T i lo hi)
    (h0 : lo = 0) (h1 : hi = u.length) : MatchLen u T i u.length := by
  intro j hj
  exact h j (by omega) (by omega)

/-! ## 2. 残り仕事量 -/

/-- 照合完了（区間が `[0, |u|)`）。 -/
def zdone (s : ℕ) (z : ZS) : Bool := decide (z.lo = 0 ∧ z.hi = s)

/-- 照合を完了するまでに必要な残り単位動作数。上向きなら「`|u|` まで進む」＋
（下端が未了なら）「`|u|` から `0` まで戻って照合する」`|u|` 動作。 -/
def zrem (s : ℕ) (z : ZS) : ℕ :=
  if z.lo = 0 ∧ z.hi = s then 0
  else if z.up then (s - z.head) + (if z.lo = 0 then 0 else 1 + s)
  else z.head + (if z.hi = s then 0 else 1 + s)

/-- 状態の整合性：`lo ≤ head ≤ hi ≤ |u|`、および「反対端が未了なら
ヘッドは伸ばす側の端にいるか、戻る途中である」。 -/
def ZWf (s : ℕ) (z : ZS) : Prop :=
  z.lo ≤ z.head ∧ z.head ≤ z.hi ∧ z.hi ≤ s ∧
    (z.up = true → z.head = z.hi ∨ z.lo = 0) ∧
    (z.up = false → z.head = z.lo ∨ z.hi = s)

theorem zrem_eq_zero_of_done {s : ℕ} {z : ZS} (h : zdone s z = true) : zrem s z = 0 := by
  simp only [zdone, decide_eq_true_eq] at h
  unfold zrem
  rw [if_pos h]

theorem zdone_of_zrem_eq_zero {s : ℕ} {z : ZS} (hw : ZWf s z)
    (h : zrem s z = 0) : zdone s z = true := by
  obtain ⟨w1, w2, w3, w4, w5⟩ := hw
  simp only [zdone, decide_eq_true_eq]
  unfold zrem at h
  by_cases hd : z.lo = 0 ∧ z.hi = s
  · exact hd
  · rw [if_neg hd] at h
    exfalso
    by_cases hup : z.up = true
    · rw [if_pos hup] at h
      by_cases hlo : z.lo = 0
      · rw [if_pos hlo] at h
        have hhi : z.hi ≠ s := fun hc => hd ⟨hlo, hc⟩
        omega
      · rw [if_neg hlo] at h
        omega
    · rw [if_neg hup] at h
      by_cases hhi : z.hi = s
      · rw [if_pos hhi] at h
        have hlo : z.lo ≠ 0 := fun hc => hd ⟨hc, hhi⟩
        omega
      · rw [if_neg hhi] at h
        omega

/-! ## 3. 1 単位動作 -/

variable [DecidableEq α]

/-- **1 単位動作**：ヘッドを 1 セル動かす（伸ばす端なら 1 文字照合、
反対端から戻る途中ならただ進む、テープ端なら反転）。 -/
def zMove (u T : List α) (pos : ℕ) (z : ZS) : ZS :=
  if z.up then
    (if z.head < u.length then
        (if z.head = z.hi then
            (if T[pos - u.length + z.head]? = u[z.head]? then
                ⟨z.head + 1, z.lo, z.hi + 1, true⟩
              else z)
          else ⟨z.head + 1, z.lo, z.hi, true⟩)
      else ⟨z.head, z.lo, z.hi, false⟩)
  else
    (if 0 < z.head then
        (if z.head = z.lo then
            (if T[pos - u.length + (z.head - 1)]? = u[z.head - 1]? then
                ⟨z.head - 1, z.lo - 1, z.hi, false⟩
              else z)
          else ⟨z.head - 1, z.lo, z.hi, false⟩)
      else ⟨z.head, z.lo, z.hi, true⟩)

theorem zMove_wf {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z) :
    ZWf u.length (zMove u T pos z) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold zMove
  by_cases hup : z.up = true
  · rw [if_pos hup]
    have h4' := h4 hup
    by_cases hlt : z.head < u.length
    · rw [if_pos hlt]
      by_cases he : z.head = z.hi
      · rw [if_pos he]
        by_cases hm : T[pos - u.length + z.head]? = u[z.head]?
        · rw [if_pos hm]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show z.lo ≤ z.head + 1; omega
          · show z.head + 1 ≤ z.hi + 1; omega
          · show z.hi + 1 ≤ u.length; omega
          · intro _; exact Or.inl (show z.head + 1 = z.hi + 1 by omega)
          · intro hc; exact absurd hc (by simp)
        · rw [if_neg hm]; exact ⟨h1, h2, h3, h4, h5⟩
      · rw [if_neg he]
        have hlo : z.lo = 0 := by rcases h4' with hc | hc; exacts [absurd hc he, hc]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show z.lo ≤ z.head + 1; omega
        · show z.head + 1 ≤ z.hi; omega
        · exact h3
        · intro _; exact Or.inr (show z.lo = 0 from hlo)
        · intro hc; exact absurd hc (by simp)
    · rw [if_neg hlt]
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro hc; exact absurd hc (by simp)
      · intro _; exact Or.inr (show z.hi = u.length by omega)
  · rw [if_neg hup]
    have hupf : z.up = false := by simpa using hup
    have h5' := h5 hupf
    by_cases hpos : 0 < z.head
    · rw [if_pos hpos]
      by_cases he : z.head = z.lo
      · rw [if_pos he]
        by_cases hm : T[pos - u.length + (z.head - 1)]? = u[z.head - 1]?
        · rw [if_pos hm]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show z.lo - 1 ≤ z.head - 1; omega
          · show z.head - 1 ≤ z.hi; omega
          · exact h3
          · intro hc; exact absurd hc (by simp)
          · intro _; exact Or.inl (show z.head - 1 = z.lo - 1 by omega)
        · rw [if_neg hm]; exact ⟨h1, h2, h3, h4, h5⟩
      · rw [if_neg he]
        have hhi : z.hi = u.length := by
          rcases h5' with hc | hc; exacts [absurd hc he, hc]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show z.lo ≤ z.head - 1; omega
        · show z.head - 1 ≤ z.hi; omega
        · exact h3
        · intro hc; exact absurd hc (by simp)
        · intro _; exact Or.inr hhi
    · rw [if_neg hpos]
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro _; exact Or.inr (show z.lo = 0 by omega)
      · intro hc; exact absurd hc (by simp)

/-- 完了していれば区間は動かない。 -/
theorem zMove_done {u T : List α} {pos : ℕ} {z : ZS} (h : zdone u.length z = true) :
    zdone u.length (zMove u T pos z) = true := by
  simp only [zdone, decide_eq_true_eq] at h ⊢
  unfold zMove
  by_cases hup : z.up = true
  · rw [if_pos hup]
    by_cases hlt : z.head < u.length
    · rw [if_pos hlt]
      by_cases he : z.head = z.hi
      · rw [if_pos he]
        split_ifs
        · exact ⟨h.1, by omega⟩
        · exact h
      · rw [if_neg he]; exact h
    · rw [if_neg hlt]; exact h
  · rw [if_neg hup]
    by_cases hpos : 0 < z.head
    · rw [if_pos hpos]
      by_cases he : z.head = z.lo
      · rw [if_pos he]
        split_ifs
        · exact ⟨by omega, h.2⟩
        · exact h
      · rw [if_neg he]; exact h
    · rw [if_neg hpos]; exact h

/-- **1 単位動作で残り仕事量はちょうど 1 減る**（未完了かつ `u` が全一致のとき）。 -/
theorem zMove_rem {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hdone : zdone u.length z = false)
    (hfull : MatchLen u T (pos - u.length) u.length) :
    zrem u.length (zMove u T pos z) + 1 = zrem u.length z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [zdone, decide_eq_false_iff_not, not_and] at hdone
  have hf1 : z.head < u.length → T[pos - u.length + z.head]? = u[z.head]? :=
    fun hlt => hfull z.head hlt
  have hf2 : 0 < z.head → T[pos - u.length + (z.head - 1)]? = u[z.head - 1]? :=
    fun hp => hfull (z.head - 1) (by omega)
  by_cases hup : z.up = true
  · have h4' := h4 hup
    simp only [zMove, zrem, hup, if_true]
    by_cases hlt : z.head < u.length
    · rw [if_pos hlt]
      by_cases he : z.head = z.hi
      · rw [if_pos he, if_pos (hf1 hlt)]
        simp only [hup, if_true]
        split_ifs <;> omega
      · rw [if_neg he]
        have hlo : z.lo = 0 := by rcases h4' with hc | hc; exacts [absurd hc he, hc]
        simp only [hup, if_true]
        split_ifs <;> omega
    · rw [if_neg hlt]
      have hhi : z.hi = u.length := by omega
      have hlo : z.lo ≠ 0 := fun hc => hdone hc hhi
      simp only [Bool.false_eq_true, if_false]
      split_ifs <;> omega
  · have hupf : z.up = false := by simpa using hup
    have h5' := h5 hupf
    simp only [zMove, zrem, hupf, Bool.false_eq_true, if_false]
    by_cases hpos : 0 < z.head
    · rw [if_pos hpos]
      by_cases he : z.head = z.lo
      · rw [if_pos he, if_pos (hf2 hpos)]
        simp only [hupf, Bool.false_eq_true, if_false]
        split_ifs <;> omega
      · rw [if_neg he]
        have hhi : z.hi = u.length := by rcases h5' with hc | hc; exacts [absurd hc he, hc]
        simp only [hupf, Bool.false_eq_true, if_false]
        split_ifs <;> omega
    · rw [if_neg hpos]
      have hhead : z.head = 0 := by omega
      have hlo : z.lo = 0 := by omega
      have hhi : z.hi ≠ u.length := hdone hlo
      simp only [if_true]
      split_ifs <;> omega

/-- 1 単位動作は照合済み区間の正しさを保つ。 -/
theorem zMove_matchIv {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hm : MatchIv u T (pos - u.length) z.lo z.hi) :
    MatchIv u T (pos - u.length) (zMove u T pos z).lo (zMove u T pos z).hi := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold zMove
  by_cases hup : z.up = true
  · rw [if_pos hup]
    split_ifs with hlt he hc
    · intro j hj1 hj2
      rcases Nat.lt_or_ge j z.hi with hlt2 | hge
      · exact hm j hj1 hlt2
      · have hj : j = z.hi := by simp only [] at hj2; omega
        rw [hj, ← he]; exact hc
    · exact hm
    · exact hm
    · exact hm
  · rw [if_neg hup]
    split_ifs with hpos he hc
    · intro j hj1 hj2
      rcases Nat.lt_or_ge j z.lo with hlt2 | hge
      · have hj : j = z.lo - 1 := by simp only [] at hj1; omega
        rw [hj, ← he]; exact hc
      · exact hm j hge hj2
    · exact hm
    · exact hm
    · exact hm

/-- **残り仕事量は 1 単位動作でちょうど 1 減る**（`ℕ` の切り捨て減算版：
完了していれば `0` のまま）。 -/
theorem zMove_rem_le {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hfull : MatchLen u T (pos - u.length) u.length) :
    zrem u.length (zMove u T pos z) ≤ zrem u.length z - 1 := by
  by_cases hdn : zdone u.length z = true
  · have h1 := zrem_eq_zero_of_done hdn
    have h2 := zrem_eq_zero_of_done (zMove_done (T := T) (pos := pos) hdn)
    omega
  · have := zMove_rem h (by simpa using hdn) hfull
    omega

/-- `j` 単位動作。 -/
def zMoves (u T : List α) (pos : ℕ) : ℕ → ZS → ZS
  | 0, z => z
  | j + 1, z => zMoves u T pos j (zMove u T pos z)

theorem zMoves_wf {u T : List α} {pos : ℕ} :
    ∀ (j : ℕ) {z : ZS}, ZWf u.length z → ZWf u.length (zMoves u T pos j z) := by
  intro j
  induction j with
  | zero => intro z h; exact h
  | succ j ih => intro z h; exact ih (zMove_wf h)

theorem zMoves_matchIv {u T : List α} {pos : ℕ} :
    ∀ (j : ℕ) {z : ZS}, ZWf u.length z →
      MatchIv u T (pos - u.length) z.lo z.hi →
      MatchIv u T (pos - u.length) (zMoves u T pos j z).lo (zMoves u T pos j z).hi := by
  intro j
  induction j with
  | zero => intro z _ h; exact h
  | succ j ih => intro z hw h; exact ih (zMove_wf hw) (zMove_matchIv hw h)

theorem zMoves_rem_le {u T : List α} {pos : ℕ}
    (hfull : MatchLen u T (pos - u.length) u.length) :
    ∀ (j : ℕ) {z : ZS}, ZWf u.length z →
      zrem u.length (zMoves u T pos j z) ≤ zrem u.length z - j := by
  intro j
  induction j with
  | zero => intro z _; show zrem u.length z ≤ zrem u.length z - 0; omega
  | succ j ih =>
    intro z hw
    have h1 := zMove_rem_le hw hfull
    have h2 := ih (z := zMove u T pos z) (zMove_wf hw)
    show zrem u.length (zMoves u T pos j (zMove u T pos z)) ≤ zrem u.length z - (j + 1)
    omega

/-! ## 4. 一歩（走査＋4 単位動作） -/

/-- **ずらしのリセット**：ヘッドはそのまま、区間を空に。 -/
def zReset (z : ZS) : ZS := ⟨z.head, z.head, z.head, false⟩

/-- 1 歩あたりの単位動作の割当（quota）。 -/
def zQuota : ℕ := 4

/-- **一歩**：走査 1 歩 ＋（比較成功なら）検証器の `zQuota = 4` 単位動作、
ずらしならリセット。 -/
def vStepZ (u v : List α) (k p₁ r : ℕ) (T : List α) (z : VStateZ) : VStateZ :=
  if z.1.q = v.length then (scanStep v k p₁ r T z.1, zReset z.2)
  else if T[z.1.pos + z.1.q]? = v[z.1.q]? then
    (scanStep v k p₁ r T z.1, zMoves u T z.1.pos zQuota z.2)
  else (scanStep v k p₁ r T z.1, zReset z.2)

@[simp] theorem vStepZ_fst (u v : List α) (k p₁ r : ℕ) (T : List α) (z : VStateZ) :
    (vStepZ u v k p₁ r T z).1 = scanStep v k p₁ r T z.1 := by
  unfold vStepZ; split_ifs <;> rfl

/-- **一歩の費用は定数**：`v` の比較 1 ＋ `u` の単位動作 4。 -/
def vStepZCost : ℕ := 5

/-! ## 5. 不変条件 -/

/-- 検証器の不変条件（`GSVerifier.VInv` のジグザグ版）。 -/
def ZInv (u v T : List α) (z : VStateZ) : Prop :=
  u.length ≤ z.1.pos ∧
    ZWf u.length z.2 ∧
      MatchIv u T (z.1.pos - u.length) z.2.lo z.2.hi ∧
        (MatchLen u T (z.1.pos - u.length) u.length →
          zrem u.length z.2 ≤ zQuota * (v.length - z.1.q))

/-- **締切条件**：ずらし直後の残り仕事量 `≤ 2*(|v| - q')` を保証する形。
`GSRealTime.prefix_verifier_deadline` は `|u| < 2*(|v| - gsNextQ …)` を与えるが、
ジグザグでは（戻りの走行があるので）`|u| ≤ |v| - gsNextQ …` が要る。 -/
def ZDeadline (u v : List α) (k p₁ r : ℕ) : Prop :=
  ∀ q, q ≤ v.length → 2 * u.length + 1 ≤ zQuota * (v.length - gsNextQ k p₁ r q)

/-- **`ZDeadline` は L1 の切り出しから従う**：`GSRealTime.prefix_verifier_deadline`
（`|u| < 2*(|v| - gsNextQ …)`）を 2 倍すればよい（quota = 4）。 -/
theorem zdeadline_of_prefix {u v : List α} {k p₁ r : ℕ} (hk : 3 ≤ k) (hp : 0 < p₁)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) :
    ZDeadline u v k p₁ r := by
  intro q hq
  have h := prefix_verifier_deadline (u := u) (v := v) (r := r) hk hp hL1a hL1b hq
  show 2 * u.length + 1 ≤ 4 * (v.length - gsNextQ k p₁ r q)
  omega

/-- ずらし直後は不変条件を満たす。 -/
theorem zInv_shift {u v T : List α} {k p₁ r : ℕ} (hd : ZDeadline u v k p₁ r)
    {pos q : ℕ} {z : ZS} (hz : ZWf u.length z) (hpos : u.length ≤ pos) (hq : q ≤ v.length)
    (hp : 0 < gsShift k p₁ r q) :
    ZInv u v T ((⟨pos + gsShift k p₁ r q, gsNextQ k p₁ r q⟩ : ScanState), zReset z) := by
  obtain ⟨h1, h2, h3, _, _⟩ := hz
  refine ⟨by simp only []; omega, ⟨by simp [zReset], by simp [zReset], by
    simp only [zReset]; omega, by simp [zReset], by simp [zReset]⟩, ?_, ?_⟩
  · exact matchIv_empty u T _ _
  · intro _
    have hrem : zrem u.length (zReset z) ≤ z.head + 1 + u.length := by
      simp only [zrem, zReset, Bool.false_eq_true, if_false]
      split_ifs <;> omega
    have hdd := hd q hq
    have hhead : z.head ≤ u.length := by omega
    show zrem u.length (zReset z) ≤ zQuota * (v.length - gsNextQ k p₁ r q)
    simp only [zQuota] at hdd ⊢
    omega

/-- **一歩で不変条件は保たれる**。 -/
theorem vStepZ_inv {u v T : List α} {k p₁ r : ℕ} (hp : 0 < p₁)
    (hd : ZDeadline u v k p₁ r) {z : VStateZ} (hs : ScanInv v T z.1) (h : ZInv u v T z) :
    ZInv u v T (vStepZ u v k p₁ r T z) := by
  obtain ⟨hpos, hwf, hmiv, hdead⟩ := h
  obtain ⟨_, hq⟩ := hs
  have hgs : 0 < gsShift k p₁ r z.1.q := gsShift_pos hp
  have hshift : ZInv u v T
      ((⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState), zReset z.2) :=
    zInv_shift hd hwf hpos hq hgs
  unfold vStepZ
  split_ifs with h1 h2
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_pos h1]]
    exact hshift
  · have hsucc : scanStep v k p₁ r T z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) := by
      unfold scanStep; rw [if_neg h1, if_pos h2]
    rw [hsucc]
    refine ⟨hpos, zMoves_wf (T := T) (pos := z.1.pos) zQuota hwf, ?_, ?_⟩
    · exact zMoves_matchIv (T := T) (pos := z.1.pos) zQuota hwf hmiv
    · intro hfull
      have hdd := hdead hfull
      have hqlt : z.1.q < v.length := lt_of_le_of_ne hq h1
      have hle := zMoves_rem_le (u := u) (T := T) (pos := z.1.pos) hfull zQuota hwf
      show zrem u.length (zMoves u T z.1.pos zQuota z.2)
        ≤ zQuota * (v.length - (z.1.q + 1))
      simp only [zQuota] at hle hdd ⊢
      omega
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_neg h1, if_neg h2]]
    exact hshift

/-! ## 6. 報告の同値 -/

/-- 検証器の報告ビット：`v` が全一致し、かつ `u` の照合が完了している。 -/
def zReportFlag (u v : List α) (n : ℕ) (z : VStateZ) : Bool :=
  decide (z.1.q = v.length ∧ z.1.pos + v.length = n) && zdone u.length z.2

/-- **報告の健全性**：報告したなら `u` は全一致している。 -/
theorem zReportFlag_sound {u v T : List α} {n : ℕ} {z : VStateZ} (h : ZInv u v T z)
    (hf : zReportFlag u v n z = true) :
    MatchLen u T (z.1.pos - u.length) u.length := by
  obtain ⟨_, _, hmiv, _⟩ := h
  simp only [zReportFlag, Bool.and_eq_true, decide_eq_true_eq, zdone] at hf
  exact matchIv_full hmiv hf.2.1 hf.2.2

/-- **報告の完全性**：`u` が全一致していて `q = |v|` なら、残り仕事量は `0`、
すなわち照合は完了しており報告される。 -/
theorem zReportFlag_complete {u v T : List α} {n : ℕ} {z : VStateZ} (h : ZInv u v T z)
    (hfull : MatchLen u T (z.1.pos - u.length) u.length)
    (hq : z.1.q = v.length) (hn : z.1.pos + v.length = n) :
    zReportFlag u v n z = true := by
  obtain ⟨_, hwf, _, hdead⟩ := h
  have hr : zrem u.length z.2 ≤ zQuota * (v.length - z.1.q) := hdead hfull
  rw [hq] at hr
  simp only [Nat.sub_self, Nat.mul_zero, Nat.le_zero] at hr
  have hd : zdone u.length z.2 = true := zdone_of_zrem_eq_zero hwf hr
  simp only [zReportFlag, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hq, hn⟩, hd⟩

/-- **報告は接頭辞オラクルと一致する**（`GSVerifier.vReportFlag_eq` のジグザグ版）。 -/
theorem zReportFlag_eq {u v T : List α} {n : ℕ} {z : VStateZ} (h : ZInv u v T z) :
    zReportFlag u v n z = true
      ↔ (z.1.q = v.length ∧ z.1.pos + v.length = n
          ∧ MatchLen u T (z.1.pos - u.length) u.length) := by
  constructor
  · intro hf
    have hs := zReportFlag_sound h hf
    simp only [zReportFlag, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact ⟨hf.1.1, hf.1.2, hs⟩
  · rintro ⟨hq, hn, hfull⟩
    exact zReportFlag_complete h hfull hq hn

/-! ## 7. テープ実現（`GSVerifierTapesZ`）への設計メモ

本ファイルの `zMove` は「伸ばす端にいるときだけ照合し、反対端から戻る途中は
ただ進む」形になっている。この「戻る途中か否か」の判定には `hi` の位置を
テープ上に **印** として持つ必要があり、`VExt` に成分を足すことになる。

**それは不要である**：戻りの走行でも毎回照合してしまえばよい（すでに照合済みの
位置なので、候補が生きているかぎり必ず一致する）。すなわちテープ側は

* `up` のとき：`endSym` を読んでいなければ `U` と `Txt2` を 1 つ右へ動かして照合、
  読んでいれば向きを反転（`down` へ）、
* `down` のとき：`startSym` を読んでいなければ `U` と `Txt2` を 1 つ左へ動かして照合、
  読んでいれば向きを反転（`up` へ）

とすればよく、必要な状態は **`U` のヘッド位置と向き 1 ビットだけ**である
（`lo`/`hi` はゴースト）。照合完了は「`up` で `endSym` を読んでいる」ことに等しく、
これもテープ読み取りで判定できる。向きの 1 ビットは有限制御（`GSVerifierProgZ`）か
`VExt` の 1 セルテープに置く。

この「戻りでも照合する」版は、`zMove` の分岐 `z.head = z.hi` を外し、
`lo := min lo (head-1)` / `hi := max hi (head+1)` と書き換えたものであり、
残り仕事量 `zrem` と本ファイルの補題はそのまま通る（`hfull` のもとで
戻りの照合は必ず成功するため）。`GSVerifierTapesZ` はこちらを実装すべきである。 -/

/-! ## 8. 公理の確認 -/

#print axioms zdeadline_of_prefix
#print axioms zMove_wf
#print axioms zMove_rem
#print axioms zMove_matchIv
#print axioms zInv_shift
#print axioms vStepZ_inv
#print axioms zReportFlag_eq

end GSVerifierZ
end PalPeg
