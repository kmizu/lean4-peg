import PalPeg.GSRealTime

/-!
# 短い接頭辞 `u` の **インターリーブ検証器**（オラクルの除去）

`PalPeg.GSRealTime` の `answer` は、`v` の報告位置で短い接頭辞 `u` の照合を
`decide (MatchLen u T (n+1-|x|) |u|)` という **オラクル** で済ませていた。
本ファイルはそれを、`gs_events.py` の `PatternMatcher`（`checked` / `quota` /
`prefix_ok` / `mode`）に対応する **具体的なインターリーブ検証器** に置き換える。

## 機械

状態は `VState = ScanState × ℕ`：走査状態と、現候補 `pos` について検証済みの
`u` の文字数 `checked`。

* `vComp u T pos c` — 1 回の比較 `T[pos - |u| + c]? = u[c]?`。成功なら `c+1`、
  失敗ならそのまま（`prefix_ok = False` は「`checked` がそこで止まる」ことで
  暗黙に表現される。以後この候補では `checked = |u|` に到達できない）。
  `c = |u|`（検証完了）ならもう比較しない。
* `vStep` — `scanStep` を 1 回。それが **`v` の成功比較**（`q` が増える枝）なら
  続けて `vComp` を **2 回**（`quota = 2`）。**ずらし**なら `checked := 0`。
* `vRunIn` / `vOnlineRun` / `vAnswer` — `runIn` / `onlineRun` / `answer` と同じ
  ラウンド予算 `gsRate k = k+1` 走査ステップ。`vAnswer` にオラクルは無い。

検証器が読む位置 `pos - |u| + checked` は `checked ≤ |u|` より `pos` 以下、
すなわち走査ヘッド `pos + q` より手前なので、到着済み（`Fits`）の文字だけを読む。

## 費用

1 ステップの単位操作は「`v` の比較 1 回 + `u` の比較高々 2 回」＝ `≤ 3`
(`vStepCost_le`)。したがって 1 ラウンドは `≤ 3*(k+1) = gsRateInterleaved k`
(`vRound_cost_le`)。

## 正しさ

不変条件 `VInv`：

* `|u| ≤ pos`（候補はパターン開始位置を持つ）、
* `MatchLen u T (pos - |u|) checked`（検証済み部分は本当に一致している）、
* `checked ≤ |u|`、
* **締切** `MatchLen u T (pos-|u|) |u| → |u| ≤ checked + 2*(|v| - q)`。

第 4 条は `prefix_verifier_deadline`（`|u| < 2*(|v| - gsNextQ k p₁ r q)`）で
ずらし直後に回復し、`v` の成功比較 1 回（`q` が 1 増え右辺が 2 減る）につき
`checked` が 2 増える（一致する限り）ので保存される。報告時（`q = |v|`）には
`|u| ≤ checked` が出るので、`checked = |u| ↔ MatchLen u T (pos-|u|) |u|`。

主定理 `vAnswer_correct`：`vAnswer = decide (OccAt (u++v) T (n - |x|))`。
経路は `vAnswer_eq_answer`（走査成分の射影 `vOnlineRun_fst` ＋ 報告の同値）
→ `online_answer_correct`。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 検証器つき状態 -/

/-- 走査状態と、現候補について検証済みの `u` の文字数 `checked`。 -/
abbrev VState := ScanState × ℕ

/-- 検証器の不変条件（`|u| ≤ pos`、検証済み部分の正しさ、上限、締切）。 -/
def VInv (u v T : List α) (z : VState) : Prop :=
  u.length ≤ z.1.pos ∧
    MatchLen u T (z.1.pos - u.length) z.2 ∧
      z.2 ≤ u.length ∧
        (MatchLen u T (z.1.pos - u.length) u.length →
          u.length ≤ z.2 + 2 * (v.length - z.1.q))

/-- 1 回の `u` 比較の費用（検証が終わっていれば 0）。 -/
def vCompCost (u : List α) (c : ℕ) : ℕ := if c < u.length then 1 else 0

variable [DecidableEq α]

/-! ## 検証器の 1 比較 -/

/-- 検証器の 1 比較：`T[pos - |u| + c]? = u[c]?` が成り立てば `c+1`、
そうでなければ `c` のまま（不一致でこの候補は死ぬ）。`c = |u|` なら何もしない。 -/
def vComp (u T : List α) (pos c : ℕ) : ℕ :=
  if c < u.length ∧ T[pos - u.length + c]? = u[c]? then c + 1 else c

theorem le_vComp (u T : List α) (pos c : ℕ) : c ≤ vComp u T pos c := by
  unfold vComp; split_ifs <;> omega

theorem vComp_le_succ (u T : List α) (pos c : ℕ) : vComp u T pos c ≤ c + 1 := by
  unfold vComp; split_ifs <;> omega

theorem vComp_le_length {u T : List α} {pos c : ℕ} (h : c ≤ u.length) :
    vComp u T pos c ≤ u.length := by
  unfold vComp
  split_ifs with hc
  · obtain ⟨h1, _⟩ := hc; omega
  · exact h

theorem vComp_eq_of_ge {u T : List α} {pos c : ℕ} (h : u.length ≤ c) :
    vComp u T pos c = c := by
  unfold vComp
  rw [if_neg (by rintro ⟨h1, _⟩; omega)]

/-- 検証済み部分の正しさは 1 比較で保たれる。 -/
theorem vComp_matchLen {u T : List α} {pos c : ℕ}
    (h : MatchLen u T (pos - u.length) c) :
    MatchLen u T (pos - u.length) (vComp u T pos c) := by
  unfold vComp
  split_ifs with hc
  · exact matchLen_succ h hc.2
  · exact h

/-- 候補が本物（`u` が全一致）なら比較は必ず成功し、`checked` は 1 増える。 -/
theorem vComp_of_full {u T : List α} {pos c : ℕ}
    (hfull : MatchLen u T (pos - u.length) u.length) (hc : c < u.length) :
    vComp u T pos c = c + 1 := by
  unfold vComp
  exact if_pos ⟨hc, hfull c hc⟩

/-! ## インターリーブした 1 ステップ -/

/-- 走査 1 歩 ＋（`v` の成功比較なら）`u` の比較 2 回。ずらしなら `checked := 0`。 -/
def vStep (u v : List α) (k p₁ r : ℕ) (T : List α) (z : VState) : VState :=
  if z.1.q = v.length then (scanStep v k p₁ r T z.1, 0)
  else if T[z.1.pos + z.1.q]? = v[z.1.q]? then
    (scanStep v k p₁ r T z.1, vComp u T z.1.pos (vComp u T z.1.pos z.2))
  else (scanStep v k p₁ r T z.1, 0)

@[simp] theorem vStep_fst (u v : List α) (k p₁ r : ℕ) (T : List α) (z : VState) :
    (vStep u v k p₁ r T z).1 = scanStep v k p₁ r T z.1 := by
  unfold vStep; split_ifs <;> rfl

/-- 1 ステップの単位操作数：`v` の比較 1 ＋ `u` の比較高々 2。 -/
def vStepCost (u v : List α) (T : List α) (z : VState) : ℕ :=
  if z.1.q = v.length then 1
  else if T[z.1.pos + z.1.q]? = v[z.1.q]? then
    1 + vCompCost u z.2 + vCompCost u (vComp u T z.1.pos z.2)
  else 1

theorem vStepCost_le (u v : List α) (T : List α) (z : VState) :
    vStepCost u v T z ≤ 3 := by
  unfold vStepCost vCompCost
  split_ifs <;> omega

/-! ## ラウンド実行 -/

/-- ラウンド `n` の中で高々 `m` 歩（走査境界 `Enabled` は走査成分だけで決まる）。 -/
def vRunIn (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → VState → VState
  | 0, z => z
  | m + 1, z =>
      if Enabled v n z.1 then vRunIn u v k p₁ r T n m (vStep u v k p₁ r T z) else z

/-- その `m` 歩の単位操作数。 -/
def vRunCost (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → VState → ℕ
  | 0, _ => 0
  | m + 1, z =>
      if Enabled v n z.1 then
        vStepCost u v T z + vRunCost u v k p₁ r T n m (vStep u v k p₁ r T z)
      else 0

/-- ラウンド `n` 終了時の状態。初期状態は `(⟨|u|, 0⟩, 0)`。 -/
def vOnlineRun (u v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → VState
  | 0 => (⟨u.length, 0⟩, 0)
  | n + 1 => vRunIn u v k p₁ r T (n + 1) (gsRate k) (vOnlineRun u v k p₁ r T n)

/-- 報告フラグ：`v` が全一致し、その終端がちょうどラウンド `n`、かつ
接頭辞検証も完了（`checked = |u|`）。**オラクルなし**。 -/
def vReportFlag (u v : List α) (n : ℕ) (z : VState) : Bool :=
  decide (z.1.q = v.length ∧ z.1.pos + v.length = n ∧ z.2 = u.length)

def vReportedIn (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → VState → Bool
  | 0, z => vReportFlag u v n z
  | m + 1, z =>
      vReportFlag u v n z ||
        (if Enabled v n z.1 then vReportedIn u v k p₁ r T n m (vStep u v k p₁ r T z)
          else false)

/-- ラウンド `n` の出力（オラクルを含まない完全な機械）。 -/
def vAnswer (u v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → Bool
  | 0 => false
  | n + 1 => vReportedIn u v k p₁ r T (n + 1) (gsRate k) (vOnlineRun u v k p₁ r T n)

/-! ## 費用の評価 -/

theorem vRunCost_le (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) :
    ∀ (m : ℕ) (z : VState), vRunCost u v k p₁ r T n m z ≤ 3 * m := by
  intro m
  induction m with
  | zero => intro z; simp [vRunCost]
  | succ m ih =>
    intro z
    simp only [vRunCost]
    split_ifs with he
    · have h1 := vStepCost_le u v T z
      have h2 := ih (vStep u v k p₁ r T z)
      omega
    · omega

/-- **1 ラウンドの費用**：走査 `k+1` ステップに検証器を織り込んでも、
単位操作は `gsRateInterleaved k = 3*(k+1)` 以下。 -/
theorem vRound_cost_le (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) (z : VState) :
    vRunCost u v k p₁ r T n (gsRate k) z ≤ gsRateInterleaved k := by
  have h := vRunCost_le u v k p₁ r T n (gsRate k) z
  simp only [gsRate, gsRateInterleaved] at *
  omega

/-! ## 不変条件 `VInv` の保存 -/

omit [DecidableEq α] in
/-- ずらし直後の状態は `VInv` を満たす（締切は `prefix_verifier_deadline`）。 -/
theorem vInv_shift {u v T : List α} {k p₁ r : ℕ} (hk : 3 ≤ k) (hp : 0 < p₁)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁)
    {pos q : ℕ} (hpos : u.length ≤ pos) (hq : q ≤ v.length) :
    VInv u v T ((⟨pos + gsShift k p₁ r q, gsNextQ k p₁ r q⟩ : ScanState), 0) := by
  have hdl := prefix_verifier_deadline (u := u) (v := v) (r := r) hk hp hL1a hL1b hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · show u.length ≤ pos + gsShift k p₁ r q
    omega
  · exact matchLen_zero u T _
  · exact Nat.zero_le _
  · intro _
    show u.length ≤ 0 + 2 * (v.length - gsNextQ k p₁ r q)
    omega

theorem vStep_inv {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁)
    {z : VState} (hs : ScanInv v T z.1) (h : VInv u v T z) :
    VInv u v T (vStep u v k p₁ r T z) := by
  obtain ⟨hpos, hml, hcle, hdead⟩ := h
  obtain ⟨hm, hq⟩ := hs
  have hshift : VInv u v T
      ((⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState), 0) :=
    vInv_shift hk hK.period_pos hL1a hL1b hpos hq
  unfold vStep
  split_ifs with h1 h2
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_pos h1]]
    exact hshift
  · have hsucc : scanStep v k p₁ r T z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) := by
      unfold scanStep; rw [if_neg h1, if_pos h2]
    rw [hsucc]
    refine ⟨hpos, ?_, ?_, ?_⟩
    · exact vComp_matchLen (vComp_matchLen hml)
    · exact vComp_le_length (vComp_le_length hcle)
    · intro hfull
      have hdd := hdead hfull
      have hqlt : z.1.q < v.length := lt_of_le_of_ne hq h1
      show u.length ≤ vComp u T z.1.pos (vComp u T z.1.pos z.2) + 2 * (v.length - (z.1.q + 1))
      by_cases hcu : z.2 < u.length
      · rw [vComp_of_full hfull hcu]
        by_cases hcu2 : z.2 + 1 < u.length
        · rw [vComp_of_full hfull hcu2]
          omega
        · rw [vComp_eq_of_ge (by omega)]
          omega
      · have e1 : vComp u T z.1.pos z.2 = z.2 := vComp_eq_of_ge (by omega)
        rw [e1, e1]
        omega
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_neg h1, if_neg h2]]
    exact hshift

/-! ## 走査成分の射影 -/

theorem vRunIn_fst (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) :
    ∀ (m : ℕ) (z : VState),
      (vRunIn u v k p₁ r T n m z).1 = runIn v k p₁ r T n m z.1 := by
  intro m
  induction m with
  | zero => intro z; rfl
  | succ m ih =>
    intro z
    simp only [vRunIn, runIn]
    split_ifs with he
    · rw [ih (vStep u v k p₁ r T z), vStep_fst]
    · rfl

theorem vOnlineRun_fst (u v : List α) (k p₁ r : ℕ) (T : List α) :
    ∀ n, (vOnlineRun u v k p₁ r T n).1 = onlineRun u v k p₁ r T n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [vOnlineRun, onlineRun]
    rw [vRunIn_fst, ih]

theorem vRunIn_inv {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) {n : ℕ} :
    ∀ (m : ℕ) (z : VState), ScanInv v T z.1 → VInv u v T z →
      VInv u v T (vRunIn u v k p₁ r T n m z) := by
  intro m
  induction m with
  | zero => intro z _ h; exact h
  | succ m ih =>
    intro z hs h
    simp only [vRunIn]
    split_ifs with he
    · refine ih _ ?_ (vStep_inv hK hk hL1a hL1b hs h)
      rw [vStep_fst]
      exact scanStep_inv hK hs
    · exact h

theorem vOnlineRun_inv {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) :
    ∀ n, VInv u v T (vOnlineRun u v k p₁ r T n) := by
  have hdl := prefix_verifier_deadline (u := u) (v := v) (r := r) hk hK.period_pos
    hL1a hL1b (q := 0) (Nat.zero_le _)
  have hz : gsNextQ k p₁ r 0 = 0 := by unfold gsNextQ; split_ifs <;> omega
  rw [hz] at hdl
  intro n
  induction n with
  | zero =>
    refine ⟨le_refl _, ?_, Nat.zero_le _, ?_⟩
    · exact matchLen_zero u T _
    · intro _
      show u.length ≤ 0 + 2 * (v.length - 0)
      omega
  | succ n ih =>
    refine vRunIn_inv hK hk hL1a hL1b _ _ ?_ ih
    rw [vOnlineRun_fst]
    exact onlineRun_scanInv hK n

/-! ## 報告の同値：検証器はオラクルと一致する -/

/-- 報告状態では `checked = |u|` ⟺ `u` が本当に一致している。
（`→` は検証済み部分の正しさ、`←` は締切） -/
theorem vReportFlag_eq {u v T : List α} {n : ℕ} {z : VState} (h : VInv u v T z) :
    vReportFlag u v n z
      = (reportFlag v n z.1 &&
          decide (MatchLen u T (n - (u.length + v.length)) u.length)) := by
  obtain ⟨hpos, hml, hcle, hdead⟩ := h
  unfold vReportFlag reportFlag
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hq, hpn, hc⟩
    refine ⟨⟨hq, hpn⟩, ?_⟩
    rw [show n - (u.length + v.length) = z.1.pos - u.length from by omega]
    rw [hc] at hml
    exact hml
  · rintro ⟨⟨hq, hpn⟩, hfull⟩
    rw [show n - (u.length + v.length) = z.1.pos - u.length from by omega] at hfull
    have hdd := hdead hfull
    exact ⟨hq, hpn, by omega⟩

theorem vReportedIn_eq {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) {n : ℕ} :
    ∀ (m : ℕ) (z : VState), ScanInv v T z.1 → VInv u v T z →
      vReportedIn u v k p₁ r T n m z
        = (reportedIn v k p₁ r T n m z.1 &&
            decide (MatchLen u T (n - (u.length + v.length)) u.length)) := by
  intro m
  induction m with
  | zero => intro z _ h; exact vReportFlag_eq h
  | succ m ih =>
    intro z hs h
    have hs' : ScanInv v T (vStep u v k p₁ r T z).1 := by
      rw [vStep_fst]; exact scanStep_inv hK hs
    have hrec := ih (vStep u v k p₁ r T z) hs' (vStep_inv hK hk hL1a hL1b hs h)
    rw [vStep_fst] at hrec
    simp only [vReportedIn, reportedIn]
    rw [vReportFlag_eq h, hrec]
    by_cases he : Enabled v n z.1
    · rw [if_pos he, if_pos he]
      cases reportFlag v n z.1 <;>
        cases reportedIn v k p₁ r T n m (scanStep v k p₁ r T z.1) <;>
          cases (decide (MatchLen u T (n - (u.length + v.length)) u.length)) <;> rfl
    · rw [if_neg he, if_neg he]
      cases reportFlag v n z.1 <;>
        cases (decide (MatchLen u T (n - (u.length + v.length)) u.length)) <;> rfl

/-- **オラクルの除去**：インターリーブ検証器つきの機械の出力は、
オラクル版 `answer` の出力と一致する。 -/
theorem vAnswer_eq_answer {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 3 ≤ k)
    (hL1a : (k - 1) * u.length < (u ++ v).length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁) (n : ℕ) :
    vAnswer u v k p₁ r T n = answer u v k p₁ r T n := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [vAnswer, answer]
    rw [← vOnlineRun_fst u v k p₁ r T m]
    refine vReportedIn_eq hK hk hL1a hL1b _ _ ?_ (vOnlineRun_inv hK hk hL1a hL1b m)
    rw [vOnlineRun_fst]
    exact onlineRun_scanInv hK m

/-! ## 主定理 -/

/-- **インターリーブ検証器つき実時間 GS の正しさ**：
オラクルを含まない機械 `vAnswer`（1 ラウンドあたり単位操作 `≤ 3*(k+1)`）は、
`|x| ≤ n` なる各ラウンド `n` に「`x = u ++ v` が位置 `n − |x|` に出現するか」を
その場で答える。 -/
theorem vAnswer_correct {u v T : List α} {k p₁ r : ℕ} (hK : KSimple v k p₁ r)
    (hk : 3 ≤ k) (_hp : 0 < p₁)
    (hL1a : (k - 1) * u.length < u.length + v.length)
    (hL1b : (k - 2) * u.length < (k - 1) * p₁)
    (hv : 0 < v.length) (n : ℕ) (hn : u.length + v.length ≤ n) :
    vAnswer u v k p₁ r T n = decide (OccAt (u ++ v) T (n - (u.length + v.length))) := by
  have hL1a' : (k - 1) * u.length < (u ++ v).length := by
    simp only [List.length_append]; exact hL1a
  rw [vAnswer_eq_answer hK hk hL1a' hL1b n]
  have h := online_answer_correct (u := u) (T := T) (r := r) hK (by omega) hv n
    (by simp only [List.length_append]; exact hn)
  simpa only [List.length_append] using h

/-! ## 小例（オラクル版との一致を実際に確かめる） -/

section Examples

/-- `u = [1]`, `v = [0]*8`, `k = 8`, `p₁ = 1`, `r = 8`。出現はラウンド 9 のみ。 -/
example :
    vAnswer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 9 = true := by decide

example :
    vAnswer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 10 = false := by decide

example :
    vAnswer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 8 = false := by decide

/-- `u = []`（検証器は即完了）の場合はオラクル版と同じ挙動。 -/
example : vAnswer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 6 = true := by decide
example : vAnswer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 5 = false := by decide

/-- 1 ステップの単位操作：`v` の比較 1 ＋ `u` の比較 2（`u` が短ければそれ以下）。 -/
example : vStepCost ([1, 1] : List ℕ) [0, 0] [1, 1, 0, 0] (⟨2, 0⟩, 0) = 3 := by decide
example : vStepCost ([1] : List ℕ) [0, 0] [1, 0, 0] (⟨1, 0⟩, 0) = 2 := by decide

end Examples

end PalPeg
