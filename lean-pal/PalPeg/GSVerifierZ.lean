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

/-- **照合完了**：`up` かつヘッドが右端（`endSym` を読む位置）にいる。
これは **テープから読み取れる**判定である（`GSVerifierTapesZ` の
`Tape.read U = endSym ∧ up`）。`ZWf` のもとで区間 `[0, |u|)` の照合完了と同値。 -/
def zdone (s : ℕ) (z : ZS) : Bool := z.up && decide (z.head = s)

/-- 照合を完了する（`up` で右端に着く）までに必要な残り単位動作数。
`up` なら右端まで `s - head`。`down` なら左端まで `head`、反転 `1`、右端まで `s`。 -/
def zrem (s : ℕ) (z : ZS) : ℕ :=
  if z.up then s - z.head else z.head + 1 + s

/-- 状態の整合性：`head ≤ |u|`, `hi ≤ |u|`、かつ **`up` なら照合済み区間は
ちょうど `[0, head)`**。（`up` へ反転できるのは `head = 0` に着いたときだけで、
そこで区間は `[0,0)` に張り直される。） -/
def ZWf (s : ℕ) (z : ZS) : Prop :=
  z.head ≤ s ∧ z.hi ≤ s ∧ (z.up = true → z.lo = 0 ∧ z.hi = z.head)

theorem zrem_eq_zero_of_done {s : ℕ} {z : ZS} (h : zdone s z = true) : zrem s z = 0 := by
  simp only [zdone, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [zrem, h.1, if_true, h.2, Nat.sub_self]

theorem zdone_of_zrem_eq_zero {s : ℕ} {z : ZS} (hw : ZWf s z)
    (h : zrem s z = 0) : zdone s z = true := by
  obtain ⟨w1, w2, _⟩ := hw
  simp only [zdone, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hup : z.up = true
  · refine ⟨hup, ?_⟩
    simp only [zrem, hup, if_true] at h
    omega
  · exfalso
    have hupf : z.up = false := by simpa using hup
    simp only [zrem, hupf, Bool.false_eq_true, if_false] at h
    omega

/-- **完了なら照合済み区間は `[0, |u|)`**（`ZWf` から）。 -/
theorem matchIv_of_done {s : ℕ} {z : ZS} (hw : ZWf s z) (h : zdone s z = true) :
    z.lo = 0 ∧ z.hi = s := by
  obtain ⟨w1, w2, w3⟩ := hw
  simp only [zdone, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e1, e2⟩ := w3 h.1
  exact ⟨e1, by omega⟩

/-! ## 3. 1 単位動作 -/

variable [DecidableEq α]

/-- **1 単位動作（ジグザグ掃引）**。

* `up`：右端（`head = |u|`）に着いていれば**完了**なので動かない。そうでなければ
  `u[head]` と `T[pos-|u|+head]` を照合し、一致すれば両ヘッドを 1 つ右へ動かして
  照合済み区間を `[0, head+1)` に伸ばす（不一致なら止まる＝この候補は死ぬ）。
* `down`：左端（`head = 0`）でなければ両ヘッドを 1 つ左へ動かすだけ
  （**照合はしない**）。左端に着いたら `up` へ反転し、照合済み区間を `[0,0)` に張り直す。

上りの掃引だけで `[0, |u|)` 全体を覆うので、下りの掃引で照合する必要はない。
したがって **`U` と `Txt2` の整列は向きによらず同じ**（`U` の添字 `head+1`、
`Txt2` の添字 `pos - |u| + head`）であり、テープ実現がきわめて簡単になる。

実装（`GSVerifierTapesZ`）が持つ実状態は **`U` のヘッド位置と向き 1 ビットだけ**である
（`lo`/`hi` はゴースト）。 -/
def zMove (u T : List α) (pos : ℕ) (z : ZS) : ZS :=
  if z.up then
    (if z.head < u.length then
        (if T[pos - u.length + z.head]? = u[z.head]? then
            ⟨z.head + 1, z.lo, z.head + 1, true⟩
          else z)
      else z)
  else
    (if 0 < z.head then ⟨z.head - 1, z.lo, z.hi, false⟩ else ⟨0, 0, 0, true⟩)

theorem zMove_wf {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z) :
    ZWf u.length (zMove u T pos z) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold zMove ZWf
  split_ifs with hup hlt hc hpos <;>
    refine ⟨by first | omega | (simp only []; omega),
      by first | omega | (simp only []; omega), ?_⟩
  · intro _; exact ⟨(h3 hup).1, by simp only []⟩
  · exact h3
  · exact h3
  · intro hcon; exact absurd hcon (by simp)
  · intro _; exact ⟨rfl, rfl⟩

/-- 完了していれば状態は動かない（`zMove` の不動点）。 -/
theorem zMove_done {u T : List α} {pos : ℕ} {z : ZS} (h : zdone u.length z = true) :
    zMove u T pos z = z := by
  simp only [zdone, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold zMove
  rw [if_pos h.1, if_neg (by omega : ¬ z.head < u.length)]

/-- **1 単位動作で残り仕事量はちょうど 1 減る**（未完了かつ `u` が全一致のとき）。 -/
theorem zMove_rem {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hdone : zdone u.length z = false)
    (hfull : MatchLen u T (pos - u.length) u.length) :
    zrem u.length (zMove u T pos z) + 1 = zrem u.length z := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [zdone, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_true] at hdone
  by_cases hup : z.up = true
  · have hne : z.head ≠ u.length := by
      rcases hdone with hc | hc
      · rw [hup] at hc; exact absurd hc (by simp)
      · exact hc
    have hlt : z.head < u.length := by omega
    simp only [zMove, zrem, hup, if_true, if_pos hlt, if_pos (hfull z.head hlt)]
    omega
  · have hupf : z.up = false := by simpa using hup
    simp only [zMove, zrem, hupf, Bool.false_eq_true, if_false]
    by_cases hpos : 0 < z.head
    · rw [if_pos hpos]
      simp only [Bool.false_eq_true, if_false]
      omega
    · rw [if_neg hpos]
      simp only [if_true]
      omega

/-- 1 単位動作は照合済み区間の正しさを保つ。 -/
theorem zMove_matchIv {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hm : MatchIv u T (pos - u.length) z.lo z.hi) :
    MatchIv u T (pos - u.length) (zMove u T pos z).lo (zMove u T pos z).hi := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold zMove
  split_ifs with hup hlt hc hpos
  · intro j hj1 hj2
    simp only [] at hj1 hj2
    rcases Nat.lt_or_ge j z.head with hlt2 | hge
    · exact hm j hj1 (by rw [(h3 hup).2]; exact hlt2)
    · have hj : j = z.head := by omega
      rw [hj]; exact hc
  · exact hm
  · exact hm
  · exact hm
  · exact matchIv_empty u T _ _

/-- **残り仕事量は 1 単位動作でちょうど 1 減る**（`ℕ` の切り捨て減算版：
完了していれば `0` のまま）。 -/
theorem zMove_rem_le {u T : List α} {pos : ℕ} {z : ZS} (h : ZWf u.length z)
    (hfull : MatchLen u T (pos - u.length) u.length) :
    zrem u.length (zMove u T pos z) ≤ zrem u.length z - 1 := by
  by_cases hdn : zdone u.length z = true
  · have h1 := zrem_eq_zero_of_done hdn
    rw [zMove_done (T := T) (pos := pos) hdn]
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
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨by simp only []; omega,
    ⟨by simp only [zReset]; omega, by simp only [zReset]; omega, by simp [zReset]⟩, ?_, ?_⟩
  · exact matchIv_empty u T _ _
  · intro _
    have hrem : zrem u.length (zReset z) ≤ z.head + 1 + u.length := by
      simp only [zrem, zReset, Bool.false_eq_true, if_false]
      omega
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
  obtain ⟨_, hwf, hmiv, _⟩ := h
  simp only [zReportFlag, Bool.and_eq_true] at hf
  obtain ⟨hlo, hhi⟩ := matchIv_of_done hwf hf.2
  exact matchIv_full hmiv hlo hhi

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

§3 の `zMove` は次のようにテープで実現される（`U` は `startSym :: (u ++ [endSym])`、
ヘッドは添字 `head + 1`、`Txt2` はヘッドが添字 `pos - |u| + head`。
**この整列は向きによらない**）。

* `up`：`Tape.read U = endSym` なら**何もしない**（完了）。そうでなければ
  `Tape.read U = Tape.read Txt2` を判定し、真なら `[U .right, X .right]`、
  偽なら何もしない。これは既存の `GSVTapes.vcompActs endSym` そのものである。
* `down`：`U` の 1 つ左を**覗いて**（動作 0）`startSym` なら向きを `up` に反転して
  何もしない、そうでなければ `[U .left, X .left]`。
  （`startSym ∉ u` なので、この覗きは「`head = 0` か」を正しく判定する。）

したがって 1 単位動作は **高々 2 動作**、`zQuota = 4` 単位で高々 8 動作である。
完了判定は「`up` かつ `Tape.read U = endSym`」で、これもテープ読み取りだけで済む。
向きの 1 ビットは有限制御（`GSVerifierProgZ`）に置く。

**ずらしのとき `U` は動かさない**（`zReset` は `head` をそのままにする）。`Txt2` は
融合ループ（`perProgramX` / `resProgramX`）が `gsShift` だけ右へ運ぶので、新しい
`pos + gsShift` に対して整列がそのまま保たれる。よって `uxWalk`（`U` の巻き戻しと
`Txt2` の残差補正）は**まったく不要**であり、`Ψ = 2·checked` のような償却項は現れない
（`PalPeg.PointwiseGap.rewind_not_pointwise` の反例を回避する）。 -/

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
