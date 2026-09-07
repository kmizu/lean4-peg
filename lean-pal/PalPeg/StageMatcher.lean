import PalPeg.Assembly
import PalPeg.GSRealTime
import PalPeg.GSDecomp
import PalPeg.Manacher

/-!
# 二進段の照合オラクルを実時間 GS 照合器で実現する

`PalPeg.Assembly` の `MatchOracle` は「幅 `W` の段が反転パターン
`x = (w.take W).reverse` の出現を時刻 `n` に報告する」という *仕様だけ* の
インタフェースだった。本ファイルはそれを `PalPeg.GSRealTime` の
**実時間 Galil–Seiferas 照合器** `answer` で **実装** する。

## 定義

* `effPeriod` / `effReach` — `GSCore` の出力 `(p₁, r)` を走査側の `KSimple` が
  要求する形に正規化する（`p₁ = 0`（Python の `period = None`）は
  `p₁' = |v| + 1`, `r' = 0` に読み替える。`GSCore.ksimple_none` の形）。
* `stageMatch w W k s p₁ r n` — 幅 `W` の段の照合オラクル本体。
  パターン `x = (w.take W).reverse` を `u = x.take s`, `v = x.drop s` に切り、
  テキスト `T = w.drop W` に対する実時間走査のラウンド `n - W` の出力を返す。
* `middleFlag w W n` — 中央フラグ（まだ添字レベルのオラクル）。
* `gsOracles w k cut per rea` — `dyadicAnswer` に渡す段オラクルの族。

## 主定理

* `stageMatch_matchOracle` — `stageMatch` は `MatchOracle` を満たす。
* `stageMatch_take` — オンライン性：時刻 `n` の答えは `w.take m`（`n ≤ m`）だけに依存。
* `dyadic_gs_correct` / `dyadic_gs_mem_PAL` — 制御器 `dyadicAnswer` を
  実時間 GS 照合器で駆動したときの正当性。

## 実時間性についての注意

`stageMatch` の照合部分は本当に実時間（1 ラウンドあたり `gsRate k = k+1` 走査ステップ）
だが、`middleFlag` は依然として添字レベルのオラクルであり、その実時間実現は
別ファイル（`MiddleJob` 系）の仕事である。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## リスト側の補題 -/

theorem occursAt_nil (T : List α) : occursAt ([] : List α) T := by
  refine ⟨Nat.zero_le _, ?_⟩
  simp

/-- `occursAt` は「接尾辞に出現」なので、収まる範囲で先頭を捨てても変わらない。 -/
theorem occursAt_drop_iff {P T : List α} {d : ℕ} (h : d + P.length ≤ T.length) :
    occursAt P (T.drop d) ↔ occursAt P T := by
  unfold occursAt
  rw [List.length_drop, List.drop_drop,
    show d + (T.length - d - P.length) = T.length - P.length from by omega]
  constructor
  · rintro ⟨-, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨-, h2⟩; exact ⟨by omega, h2⟩

/-! ## `GSCore` の出力を `KSimple` の形に正規化する -/

/-- `p₁ = 0`（`period = None`）を走査側が使える周期に読み替える。 -/
def effPeriod (v : List α) (p₁ : ℕ) : ℕ := if p₁ = 0 then v.length + 1 else p₁

/-- `p₁ = 0` のときの到達域。 -/
def effReach (p₁ r : ℕ) : ℕ := if p₁ = 0 then 0 else r

/-- 分解 `GSCore x k s p₁ r` は、正規化した `(p₁', r')` で必ず `KSimple` を与える。 -/
theorem GSCore.ksimple_eff {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r) :
    KSimple (x.drop s) k (effPeriod (x.drop s) p₁) (effReach p₁ r) := by
  by_cases h : p₁ = 0
  · rw [effPeriod, effReach, if_pos h, if_pos h]
    exact H.ksimple_none h
  · rw [effPeriod, effReach, if_neg h, if_neg h]
    exact H.ksimple h

/-- `k`-繰り返し接頭辞をもたないパターンは `s = 0` で切れる（仮定が空でないことの確認）。 -/
theorem gsCore_zero_of_no_krep' {x : List α} {k : ℕ} (h : ∀ p, ¬ KRep x k p) :
    GSCore x k 0 0 0 :=
  ⟨Nat.zero_le _, fun _ => ⟨rfl, by simpa using h⟩, fun hne => absurd rfl hne,
    fun hne => absurd rfl hne, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩

variable [DecidableEq α]

/-! ## 走査のオンライン性（読んだ文字しか見ていない） -/

omit [DecidableEq α] in
theorem matchLen_take {u T : List α} {i q m : ℕ} (h : i + q ≤ m) :
    MatchLen u (T.take m) i q ↔ MatchLen u T i q := by
  unfold MatchLen
  refine forall_congr' (fun j => ?_)
  refine imp_congr_right (fun hj => ?_)
  rw [List.getElem?_take_of_lt (show i + j < m by omega)]

/-- `Enabled` な一歩はテキストを添字 `< n` でしか読まない。 -/
theorem scanStep_take {v T : List α} {k p₁ r n m : ℕ} {st : ScanState}
    (he : Enabled v n st) (hnm : n ≤ m) :
    scanStep v k p₁ r (T.take m) st = scanStep v k p₁ r T st := by
  unfold scanStep
  by_cases h1 : st.q = v.length
  · rw [if_pos h1, if_pos h1]
  · have hlt : st.pos + st.q < n := by
      rcases he with h | h
      · exact absurd h h1
      · exact h
    rw [if_neg h1, if_neg h1,
      List.getElem?_take_of_lt (show st.pos + st.q < m by omega)]

theorem runIn_take {v T : List α} {k p₁ r n m : ℕ} (hnm : n ≤ m) :
    ∀ (j : ℕ) (st : ScanState),
      runIn v k p₁ r (T.take m) n j st = runIn v k p₁ r T n j st := by
  intro j
  induction j with
  | zero => intro st; rfl
  | succ j ih =>
    intro st
    simp only [runIn]
    split_ifs with he
    · rw [scanStep_take he hnm]; exact ih _
    · rfl

theorem reportedIn_take {v T : List α} {k p₁ r n m : ℕ} (hnm : n ≤ m) :
    ∀ (j : ℕ) (st : ScanState),
      reportedIn v k p₁ r (T.take m) n j st = reportedIn v k p₁ r T n j st := by
  intro j
  induction j with
  | zero => intro st; rfl
  | succ j ih =>
    intro st
    simp only [reportedIn]
    split_ifs with he
    · rw [scanStep_take he hnm, ih]
    · rfl

theorem onlineRun_take {u v T : List α} {k p₁ r m : ℕ} :
    ∀ (n : ℕ), n ≤ m → onlineRun u v k p₁ r (T.take m) n = onlineRun u v k p₁ r T n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [onlineRun]
    rw [ih (by omega), runIn_take (show n + 1 ≤ m by omega)]

/-- **オンライン性**：ラウンド `m'` の答えは `T.take m`（`m' ≤ m`）だけに依存する
（有効なラウンド `|u| + |v| ≤ m'` において）。 -/
theorem answer_take {u v T : List α} {k p₁ r m' m : ℕ}
    (hm : m' ≤ m) (hx : u.length + v.length ≤ m') :
    answer u v k p₁ r (T.take m) m' = answer u v k p₁ r T m' := by
  cases m' with
  | zero => rfl
  | succ n =>
    have h1 : reportedIn v k p₁ r (T.take m) (n + 1) (gsRate k)
          (onlineRun u v k p₁ r (T.take m) n)
        = reportedIn v k p₁ r T (n + 1) (gsRate k) (onlineRun u v k p₁ r T n) := by
      rw [onlineRun_take n (by omega)]
      exact reportedIn_take (by omega) _ _
    have h2 : decide (MatchLen u (T.take m) (n + 1 - (u.length + v.length)) u.length)
        = decide (MatchLen u T (n + 1 - (u.length + v.length)) u.length) :=
      decide_eq_decide.mpr (matchLen_take (by omega))
    simp only [answer, h1, h2]

/-! ## 段の照合器 -/

/-- **幅 `W` の段の照合オラクル**。
パターンは `x = (w.take W).reverse`、その `GS` 分解は `s`（切断）, `p₁`（最小周期）,
`r`（到達域）で与えられ、テキストは `T = w.drop W`。
入力時刻 `n` の答えは、テキストのラウンド `n - W` における実時間走査の出力。 -/
def stageMatch (w : List α) (W k s p₁ r : ℕ) (n : ℕ) : Bool :=
  answer ((w.take W).reverse.take s) ((w.take W).reverse.drop s) k
    (effPeriod ((w.take W).reverse.drop s) p₁) (effReach p₁ r) (w.drop W) (n - W)

/-- 走査器の出力と段の仕様（接尾辞出現）との橋渡し。 -/
theorem answer_iff_occursAt {w u v : List α} {W k p₁ r : ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (huv : u ++ v = (w.take W).reverse)
    {n : ℕ} (h2W : 2 * W ≤ n) (hn : n ≤ w.length) :
    answer u v k p₁ r (w.drop W) (n - W) = true ↔ occursAt (w.take W).reverse (w.take n) := by
  have hWw : W ≤ w.length := by omega
  have hxlen : ((w.take W).reverse).length = W := by
    rw [List.length_reverse, List.length_take_of_le hWw]
  have hlen : (u ++ v).length = W := by rw [huv]; exact hxlen
  have hmain := online_answer_correct (T := w.drop W) hK hk hv (n - W) (by rw [hlen]; omega)
  rw [hmain, huv, hxlen, decide_eq_true_iff]
  have hbound : (n - W - W) + ((w.take W).reverse).length ≤ (w.drop W).length := by
    rw [hxlen, List.length_drop]; omega
  rw [occAt_iff_occursAt hbound, hxlen, show n - W - W + W = n - W from by omega,
    List.take_drop, show W + (n - W) = n from by omega]
  refine occursAt_drop_iff ?_
  rw [hxlen, List.length_take_of_le hn]
  omega

/-- **主定理**：`s < W` なる `GS` 分解が与えられれば、実時間 GS 照合器は
幅 `W` の段の `MatchOracle` を実現する。 -/
theorem stageMatch_matchOracle {w : List α} {W k s p₁ r : ℕ} (hk : 0 < k) (hs : s < W)
    (H : GSCore ((w.take W).reverse) k s p₁ r) :
    MatchOracle w W (stageMatch w W k s p₁ r) := by
  refine ⟨fun n h2W hn => ?_⟩
  have hWw : W ≤ w.length := by omega
  have hxlen : ((w.take W).reverse).length = W := by
    rw [List.length_reverse, List.length_take_of_le hWw]
  have hv : 0 < ((w.take W).reverse.drop s).length := by
    rw [List.length_drop, hxlen]; omega
  simp only [stageMatch]
  exact answer_iff_occursAt H.ksimple_eff hk hv (List.take_append_drop s _) h2W hn

/-- **オンライン性**：時刻 `n` の段の答えは接頭辞 `w.take m`（`2 * W ≤ n ≤ m`）だけで決まる。 -/
theorem stageMatch_take {w : List α} {W k s p₁ r n m : ℕ} (h2W : 2 * W ≤ n) (hnm : n ≤ m) :
    stageMatch (w.take m) W k s p₁ r n = stageMatch w W k s p₁ r n := by
  have hWm : W ≤ m := by omega
  have hpat : (w.take m).take W = w.take W := by
    rw [List.take_take, Nat.min_eq_left hWm]
  have hT : (w.take m).drop W = (w.drop W).take (m - W) := by
    rw [List.take_drop, show W + (m - W) = m from by omega]
  have hxle : ((w.take W).reverse).length ≤ W := by
    rw [List.length_reverse, List.length_take]
    omega
  have hsum : (((w.take W).reverse).take s).length + (((w.take W).reverse).drop s).length
      ≤ n - W := by
    rw [← List.length_append, List.take_append_drop]
    omega
  simp only [stageMatch, hpat, hT]
  exact answer_take (by omega) hsum

/-! ## 中央フラグ（まだ添字レベル） -/

/-- 中央部の回文性フラグ。 -/
def middleFlag (w : List α) (W : ℕ) (n : ℕ) : Bool :=
  decide (IsPal ((w.drop W).take (n - 2 * W)))

theorem middleFlag_middleOracle (w : List α) (W : ℕ) : MiddleOracle w W (middleFlag w W) :=
  ⟨fun _ _ _ => by simp [middleFlag]⟩

/-! ## 制御器への接続 -/

/-- `dyadicAnswer` に渡す段オラクルの族。幅 `0` の段だけは自明な `true`
（`(w.take 0).reverse = []` は常に接尾辞として出現する）。 -/
def gsOracles (w : List α) (k : ℕ) (cut per rea : ℕ → ℕ) :
    ℕ → (ℕ → Bool) × (ℕ → Bool) :=
  fun W => (if W = 0 then (fun _ => true) else stageMatch w W k (cut W) (per W) (rea W),
    middleFlag w W)

theorem gsOracles_spec {w : List α} {k : ℕ} {cut per rea : ℕ → ℕ} (hk : 0 < k)
    (hdec : ∀ W, 0 < W → 2 * W ≤ w.length →
      GSCore ((w.take W).reverse) k (cut W) (per W) (rea W) ∧ cut W < W) :
    ∀ W, MatchOracle w W (gsOracles w k cut per rea W).1 ∧
      MiddleOracle w W (gsOracles w k cut per rea W).2 := by
  intro W
  refine ⟨?_, middleFlag_middleOracle w W⟩
  simp only [gsOracles]
  by_cases h : W = 0
  · subst h
    rw [if_pos rfl]
    refine ⟨fun n _ _ => ?_⟩
    simp only [List.take_zero, List.reverse_nil]
    exact iff_of_true trivial (occursAt_nil _)
  · rw [if_neg h]
    by_cases hW2 : 2 * W ≤ w.length
    · obtain ⟨HW, hlt⟩ := hdec W (Nat.pos_of_ne_zero h) hW2
      exact stageMatch_matchOracle hk hlt HW
    · exact ⟨fun n h2 hn => absurd (le_trans h2 hn) hW2⟩

/-- **接続定理**：実時間 GS 照合器で駆動した二進段制御器は、
全時刻 `n ≤ |w|` で接頭辞 `w.take n` の回文性を正しく答える。 -/
theorem dyadic_gs_correct {w : List α} {k : ℕ} {cut per rea : ℕ → ℕ} (hk : 0 < k)
    (hdec : ∀ W, 0 < W → 2 * W ≤ w.length →
      GSCore ((w.take W).reverse) k (cut W) (per W) (rea W) ∧ cut W < W)
    (n : ℕ) (hn : n ≤ w.length) :
    dyadicAnswer w (gsOracles w k cut per rea) n = true ↔ IsPal (w.take n) :=
  dyadicAnswer_correct (gsOracles_spec hk hdec) n hn

/-- 系（`α = Fin 2`）：読み終えた時刻の答えは `w ∈ PAL` と一致する。 -/
theorem dyadic_gs_mem_PAL {w : List (Fin 2)} {k : ℕ} {cut per rea : ℕ → ℕ} (hk : 0 < k)
    (hdec : ∀ W, 0 < W → 2 * W ≤ w.length →
      GSCore ((w.take W).reverse) k (cut W) (per W) (rea W) ∧ cut W < W) :
    dyadicAnswer w (gsOracles w k cut per rea) w.length = true ↔ w ∈ PAL :=
  dyadicAnswer_length_iff_mem_PAL (gsOracles_spec hk hdec)

end PalPeg
