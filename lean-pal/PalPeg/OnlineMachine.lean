import PalPeg.StageMatcher
import PalPeg.GSVerifier

/-!
# オンライン認識器の全体をラウンド単位の状態機械として組み立てる

`PalPeg.Assembly` は段オラクルの *仕様* を、`PalPeg.StageMatcher` は照合オラクルの
実時間実現を、`PalPeg.GSVerifier` はオラクルを含まない照合機械を与えた。
本ファイルはそれらを **一つのラウンド単位の状態機械** に組み上げる。

機械は二つの部品に対してパラメトリックである。

* `MiddleImpl` / `MiddleImplSpec` — 中央フラグ（`MiddleOracle`）のラウンド実装。
* `PrepImpl` / `PrepImplSpec` — GS 前処理（`GSDecomp`）のラウンド実装。

いずれもラウンド `n` では `w.take n` しか読まない形で定義するので、
オンライン性は定義から従う（`stageState_take` / `fullState_take` / `runFull_take`）。

## 段のラウンド割り当て

幅 `W` の段は

* ラウンド `n = W` に生成され（`stage_created_at`）、
* `W < n < 2 * W` で前処理（`PrepImpl`）を回し、
* ラウンド `n = 2 * W` で分解 `(s, p₁, r)` を確定して照合器を起動し、
* `2 * W < n < 4 * W` は照合器を毎ラウンド `gsRate k` ステップ進め（`vRunIn`）、
* ラウンド `n = 4 * W` に退役する（`stage_retired`）。

照合器のテキストは `w.drop W`、入力ラウンド `n` に対応するテキストラウンドは `n - W`。

**注意（起動時の追い付き）**：分解が確定するのはラウンド `2 * W` なので、その時点で
照合器はテキストのラウンド `1 … W` を一気に処理しなければならない
（`stageRound` の `n = 2 * W` の枝の `vOnlineRun … S.W`）。この追い付きの費用を
`stageCost` は `W * gsRateInterleaved k` として明示的に計上する。したがって
定数の 1 ラウンド上界 `round_cost_le` は「そのラウンドに起動する段がない」
という仮定の下で述べ、無条件の（粗い）上界は `round_cost_le'` として別に述べる。
起動費用の総和は等比級数なので償却すれば `O(1)`／ラウンドだが、その償却は
本ファイルでは扱わない。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## §1 部品のインタフェース -/

/-- **中央フラグの実装**：段幅 `W` の中央部が回文かどうかを、時刻 `W` から
ラウンドごとに計算していく仕事。`step` はラウンド `n` に `w.take n` だけを読む。 -/
structure MiddleImpl (α : Type u) where
  /-- 内部状態。 -/
  State : Type
  /-- 段幅 `W` の段が生成された時点の状態。 -/
  init : ℕ → State
  /-- ラウンド `n`：`(w.take n, n)` を読んで状態を進める。 -/
  step : List α → ℕ → State → State
  /-- ラウンド `n` の答え。 -/
  flag : State → ℕ → Bool
  /-- そのラウンドの単位操作数。 -/
  cost : List α → ℕ → State → ℕ

/-- **前処理（分解）の実装**：段幅 `W` の段のパターン `(w.take W).reverse` の
GS 分解 `(s, p₁, r)` を、ラウンド `W` から `2 * W` までかけて計算する仕事。 -/
structure PrepImpl (α : Type u) where
  /-- 内部状態。 -/
  State : Type
  /-- 段幅 `W` の段が生成された時点の状態。 -/
  init : ℕ → State
  /-- ラウンド `n`：`(w.take n, n)` を読んで状態を進める。 -/
  step : List α → ℕ → State → State
  /-- 出力 `(s, p₁, r)`。 -/
  result : State → ℕ × ℕ × ℕ
  /-- そのラウンドの単位操作数。 -/
  cost : List α → ℕ → State → ℕ

/-- 中央フラグの仕事のラウンド `n` 終了時の状態（ラウンド `W` に生成、以後毎ラウンド一歩）。 -/
def MiddleImpl.runTo (I : MiddleImpl α) (w : List α) (W : ℕ) : ℕ → I.State
  | 0 => I.init W
  | n + 1 => if n + 1 ≤ W then I.init W else I.step (w.take (n + 1)) (n + 1) (I.runTo w W n)

/-- 前処理の仕事のラウンド `n` 終了時の状態（`W < n ≤ 2 * W` の間だけ動き、以後は凍結）。 -/
def PrepImpl.runTo (P : PrepImpl α) (w : List α) (W : ℕ) : ℕ → P.State
  | 0 => P.init W
  | n + 1 =>
      if n + 1 ≤ W then P.init W
      else if n + 1 ≤ 2 * W then P.step (w.take (n + 1)) (n + 1) (P.runTo w W n)
      else P.runTo w W n

theorem MiddleImpl.runTo_take (I : MiddleImpl α) (w : List α) (W : ℕ) :
    ∀ {n m : ℕ}, n ≤ m → I.runTo (w.take m) W n = I.runTo w W n := by
  intro n
  induction n with
  | zero => intro m _; rfl
  | succ n ih =>
    intro m hm
    simp only [MiddleImpl.runTo]
    rw [ih (show n ≤ m by omega), List.take_take, Nat.min_eq_left (by omega)]

theorem PrepImpl.runTo_take (P : PrepImpl α) (w : List α) (W : ℕ) :
    ∀ {n m : ℕ}, n ≤ m → P.runTo (w.take m) W n = P.runTo w W n := by
  intro n
  induction n with
  | zero => intro m _; rfl
  | succ n ih =>
    intro m hm
    simp only [PrepImpl.runTo]
    rw [ih (show n ≤ m by omega), List.take_take, Nat.min_eq_left (by omega)]

/-- 前処理はラウンド `2 * W` で凍結する。 -/
theorem PrepImpl.runTo_freeze (P : PrepImpl α) (w : List α) (W : ℕ) :
    ∀ {n : ℕ}, 2 * W ≤ n → P.runTo w W n = P.runTo w W (2 * W) := by
  intro n
  induction n with
  | zero => intro h; rw [show W = 0 by omega]
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge (2 * W) (n + 1) with hlt | hge
    · have : P.runTo w W (n + 1) = P.runTo w W n := by
        simp only [PrepImpl.runTo]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [this, ih (by omega)]
    · rw [show n + 1 = 2 * W by omega]

/-- 中央フラグ実装の仕様（正しさと 1 ラウンドの費用上界 `Cm`）。 -/
structure MiddleImplSpec (I : MiddleImpl α) (Cm : ℕ) : Prop where
  correct : ∀ (w : List α) (W n : ℕ), 0 < W → 2 * W ≤ n → n < 4 * W → n ≤ w.length →
    (I.flag (I.runTo w W n) n = true ↔ IsPal ((w.drop W).take (n - 2 * W)))
  cost_le : ∀ (t : List α) (n : ℕ) (st : I.State), I.cost t n st ≤ Cm

/-- 前処理実装の仕様（ラウンド `2 * W` に `GSDecomp` を出すことと費用上界 `Cp`）。 -/
structure PrepImplSpec (P : PrepImpl α) (k Cp : ℕ) : Prop where
  correct : ∀ (w : List α) (W : ℕ), 0 < W → 2 * W ≤ w.length →
    GSDecomp ((w.take W).reverse) k (P.result (P.runTo w W (2 * W))).1
      (P.result (P.runTo w W (2 * W))).2.1 (P.result (P.runTo w W (2 * W))).2.2
    ∧ (P.result (P.runTo w W (2 * W))).1 < W
  cost_le : ∀ (t : List α) (n : ℕ) (st : P.State), P.cost t n st ≤ Cp

/-! ## §2 インターリーブ検証器のオンライン性

`PalPeg.StageMatcher` はオラクル版 `answer` について「読んだ文字しか見ない」ことを
示した。ここでは同じことを `PalPeg.GSVerifier` の検証器つき機械について示す。
検証器が読む位置は `pos - |u| + checked < pos` なので、`|u| ≤ pos` さえあれば
走査ヘッドより手前で、到着済みである。 -/

variable [DecidableEq α]

theorem vComp_take {u T : List α} {pos c m : ℕ} (hu : u.length ≤ pos) (hpos : pos < m) :
    vComp u (T.take m) pos c = vComp u T pos c := by
  unfold vComp
  by_cases hc : c < u.length
  · rw [List.getElem?_take_of_lt (show pos - u.length + c < m by omega)]
  · rw [if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]

theorem vStep_take {u v T : List α} {k p₁ r n m : ℕ} {z : VState}
    (he : Enabled v n z.1) (hu : u.length ≤ z.1.pos) (hnm : n ≤ m) :
    vStep u v k p₁ r (T.take m) z = vStep u v k p₁ r T z := by
  unfold vStep
  by_cases h1 : z.1.q = v.length
  · rw [if_pos h1, if_pos h1, scanStep_take he hnm]
  · have hlt : z.1.pos + z.1.q < n := by
      rcases he with h | h
      · exact absurd h h1
      · exact h
    rw [if_neg h1, if_neg h1,
      List.getElem?_take_of_lt (show z.1.pos + z.1.q < m by omega)]
    by_cases h2 : T[z.1.pos + z.1.q]? = v[z.1.q]?
    · rw [if_pos h2, if_pos h2, scanStep_take he hnm,
        vComp_take hu (show z.1.pos < m by omega),
        vComp_take hu (show z.1.pos < m by omega)]
    · rw [if_neg h2, if_neg h2, scanStep_take he hnm]

theorem vStep_pos {u v T : List α} {k p₁ r : ℕ} (z : VState) :
    z.1.pos ≤ (vStep u v k p₁ r T z).1.pos := by
  rw [vStep_fst]; exact scanStep_pos_le _ _ _ _ _ _

theorem vRunIn_pos {u v T : List α} {k p₁ r n : ℕ} :
    ∀ (j : ℕ) (z : VState), z.1.pos ≤ (vRunIn u v k p₁ r T n j z).1.pos := by
  intro j
  induction j with
  | zero => intro z; exact le_rfl
  | succ j ih =>
    intro z
    simp only [vRunIn]
    split_ifs with he
    · exact le_trans (vStep_pos z) (ih _)
    · exact le_rfl

theorem vRunIn_take {u v T : List α} {k p₁ r n m : ℕ} (hnm : n ≤ m) :
    ∀ (j : ℕ) (z : VState), u.length ≤ z.1.pos →
      vRunIn u v k p₁ r (T.take m) n j z = vRunIn u v k p₁ r T n j z := by
  intro j
  induction j with
  | zero => intro z _; rfl
  | succ j ih =>
    intro z hz
    simp only [vRunIn]
    split_ifs with he
    · rw [vStep_take he hz hnm]
      exact ih _ (le_trans hz (vStep_pos z))
    · rfl

theorem vReportedIn_take {u v T : List α} {k p₁ r n m : ℕ} (hnm : n ≤ m) :
    ∀ (j : ℕ) (z : VState), u.length ≤ z.1.pos →
      vReportedIn u v k p₁ r (T.take m) n j z = vReportedIn u v k p₁ r T n j z := by
  intro j
  induction j with
  | zero => intro z _; rfl
  | succ j ih =>
    intro z hz
    simp only [vReportedIn]
    split_ifs with he
    · rw [vStep_take he hz hnm, ih _ (le_trans hz (vStep_pos z))]
    · rfl

theorem vOnlineRun_pos (u v : List α) (k p₁ r : ℕ) (T : List α) :
    ∀ n, u.length ≤ (vOnlineRun u v k p₁ r T n).1.pos := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact le_trans ih (vRunIn_pos _ _)

theorem vOnlineRun_take {u v T : List α} {k p₁ r m : ℕ} :
    ∀ {n : ℕ}, n ≤ m → vOnlineRun u v k p₁ r (T.take m) n = vOnlineRun u v k p₁ r T n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [vOnlineRun]
    rw [ih (by omega), vRunIn_take hn _ _ (vOnlineRun_pos u v k p₁ r T n)]

theorem vAnswer_take {u v T : List α} {k p₁ r m : ℕ} :
    ∀ {n : ℕ}, n ≤ m → vAnswer u v k p₁ r (T.take m) n = vAnswer u v k p₁ r T n := by
  intro n
  cases n with
  | zero => intro _; rfl
  | succ j =>
    intro hn
    simp only [vAnswer]
    rw [vOnlineRun_take (show j ≤ m by omega),
      vReportedIn_take hn _ _ (vOnlineRun_pos u v k p₁ r T j)]

/-! ## §3 機械 -/

/-- **一つの段の状態**。`W` は段幅、`prep` / `mid` は二つの仕事の状態、
`u`/`v`/`pe`/`re` はラウンド `2 * W` で確定する照合器のパラメタ、
`scan` は検証器つき走査状態、`matched` はそのラウンドの照合出力。 -/
structure StageState (α : Type u) (I : MiddleImpl α) (P : PrepImpl α) where
  /-- 段幅。 -/
  W : ℕ
  /-- 前処理の仕事の状態。 -/
  prep : P.State
  /-- 中央フラグの仕事の状態。 -/
  mid : I.State
  /-- 分解の短い接頭辞 `u`。 -/
  u : List α
  /-- 分解の本体 `v`。 -/
  v : List α
  /-- 正規化した周期。 -/
  pe : ℕ
  /-- 正規化した到達域。 -/
  re : ℕ
  /-- 検証器つき走査状態。 -/
  scan : VState
  /-- そのラウンドの照合出力。 -/
  matched : Bool

/-- 段の生成時（ラウンド `W`）の状態。 -/
def freshStage (I : MiddleImpl α) (P : PrepImpl α) (W : ℕ) : StageState α I P :=
  ⟨W, P.init W, I.init W, [], [], 0, 0, (⟨0, 0⟩, 0), false⟩

/-- **段の 1 ラウンド**。`t = w.take n` しか読まない。
`n ≤ W` は未生成、`W < n < 2*W` は前処理、`n = 2*W` は分解の確定と照合器の起動、
`2*W < n` は照合器を `gsRate k` ステップ進める（テキストは `w.drop W`、
テキストのラウンドは `n - W`）。 -/
def stageRound (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (t : List α) (n : ℕ)
    (S : StageState α I P) : StageState α I P :=
  if n ≤ S.W then S
  else if n < 2 * S.W then
    { S with prep := P.step t n S.prep, mid := I.step t n S.mid }
  else if n = 2 * S.W then
    let prep := P.step t n S.prep
    let res := P.result prep
    let x := (t.take S.W).reverse
    let u := x.take res.1
    let v := x.drop res.1
    let pe := effPeriod v res.2.1
    let re := effReach res.2.1 res.2.2
    { S with
        prep := prep
        mid := I.step t n S.mid
        u := u
        v := v
        pe := pe
        re := re
        scan := vOnlineRun u v k pe re (t.drop S.W) S.W
        matched := vAnswer u v k pe re (t.drop S.W) S.W }
  else
    { S with
        mid := I.step t n S.mid
        scan := vRunIn S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) (gsRate k) S.scan
        matched := vReportedIn S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) (gsRate k) S.scan }

/-- そのラウンドで段が使う単位操作数。 -/
def stageCost (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (t : List α) (n : ℕ)
    (S : StageState α I P) : ℕ :=
  if n ≤ S.W then 0
  else if n < 2 * S.W then I.cost t n S.mid + P.cost t n S.prep
  else if n = 2 * S.W then I.cost t n S.mid + P.cost t n S.prep + S.W * gsRateInterleaved k
  else I.cost t n S.mid +
    vRunCost S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) (gsRate k) S.scan

/-- 段幅 `W` の段のラウンド `n` 終了時の状態。 -/
def stageState (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (w : List α) (W : ℕ) :
    ℕ → StageState α I P
  | 0 => freshStage I P W
  | n + 1 => stageRound I P k (w.take (n + 1)) (n + 1) (stageState I P k w W n)

theorem stageState_succ (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (w : List α) (W n : ℕ) :
    stageState I P k w W (n + 1)
      = stageRound I P k (w.take (n + 1)) (n + 1) (stageState I P k w W n) := rfl

/-- **機械の全状態**：生きている段の状態の並び（`liveStages` により高々 2 個）。 -/
abbrev FullState (α : Type u) (I : MiddleImpl α) (P : PrepImpl α) := List (StageState α I P)

/-- ラウンド `n` 終了時の全状態。 -/
def fullState (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (w : List α) (n : ℕ) :
    FullState α I P :=
  (liveStages n).map (fun W => stageState I P k w W n)

/-- **出力**：`dyadicAnswer` と同じ形（小さい `n` は有限場合分け、`4 ≤ n` は
担当段 `stageOf n` の照合出力と中央フラグの論理積）。 -/
def output (I : MiddleImpl α) (P : PrepImpl α) (t : List α) (n : ℕ) (S : FullState α I P) :
    Bool :=
  if n < 2 then true
  else if n < 4 then decide (t[0]? = t[n - 1]?)
  else S.any (fun s => decide (s.W = stageOf n) && s.matched && I.flag s.mid n)

/-- **1 ラウンドの総費用**：生きている段の費用の和。 -/
def roundCost (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (w : List α) (n : ℕ) : ℕ :=
  ((liveStages n).map
    (fun W => stageCost I P k (w.take n) n (stageState I P k w W (n - 1)))).sum

/-! ### 段の状態の基本的な成分 -/

omit [DecidableEq α] in
theorem MiddleImpl.runTo_init (I : MiddleImpl α) (w : List α) (W : ℕ) :
    ∀ {n : ℕ}, n ≤ W → I.runTo w W n = I.init W := by
  intro n
  cases n with
  | zero => intro _; rfl
  | succ n => intro h; simp only [MiddleImpl.runTo, if_pos h]

omit [DecidableEq α] in
theorem PrepImpl.runTo_init (P : PrepImpl α) (w : List α) (W : ℕ) :
    ∀ {n : ℕ}, n ≤ W → P.runTo w W n = P.init W := by
  intro n
  cases n with
  | zero => intro _; rfl
  | succ n => intro h; simp only [PrepImpl.runTo, if_pos h]

variable (I : MiddleImpl α) (P : PrepImpl α) (k : ℕ) (w : List α) (W : ℕ)

theorem stageState_W : ∀ n, (stageState I P k w W n).W = W := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stageState_succ]
    unfold stageRound
    split_ifs <;> exact ih

theorem stageState_mid : ∀ n, (stageState I P k w W n).mid = I.runTo w W n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stageState_succ]
    unfold stageRound
    rw [stageState_W]
    split_ifs with h1 h2 h3
    · rw [ih, I.runTo_init w W (by omega), I.runTo_init w W (by omega)]
    · show I.step _ _ _ = _
      simp only [MiddleImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega), ih]
    · show I.step _ _ _ = _
      simp only [MiddleImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega), ih]
    · show I.step _ _ _ = _
      simp only [MiddleImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega), ih]

theorem stageState_prep : ∀ n, (stageState I P k w W n).prep = P.runTo w W n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stageState_succ]
    unfold stageRound
    rw [stageState_W]
    split_ifs with h1 h2 h3
    · rw [ih, P.runTo_init w W (by omega), P.runTo_init w W (by omega)]
    · show P.step _ _ _ = _
      simp only [PrepImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega),
        if_pos (show n + 1 ≤ 2 * W by omega), ih]
    · show P.step _ _ _ = _
      simp only [PrepImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega),
        if_pos (show n + 1 ≤ 2 * W by omega), ih]
    · show (stageState I P k w W n).prep = _
      simp only [PrepImpl.runTo, if_neg (show ¬ (n + 1 ≤ W) by omega),
        if_neg (show ¬ (n + 1 ≤ 2 * W) by omega), ih]

/-! ### 段のラウンドの分岐ごとの成分 -/

section Branches

variable {I} {P} {k} {t : List α} {n : ℕ} {S : StageState α I P}

theorem stageRound_act (hW : 0 < S.W) (hn : n = 2 * S.W) :
    (stageRound I P k t n S).u
        = ((t.take S.W).reverse).take (P.result (P.step t n S.prep)).1 ∧
      (stageRound I P k t n S).v
        = ((t.take S.W).reverse).drop (P.result (P.step t n S.prep)).1 ∧
      (stageRound I P k t n S).pe
        = effPeriod (((t.take S.W).reverse).drop (P.result (P.step t n S.prep)).1)
            (P.result (P.step t n S.prep)).2.1 ∧
      (stageRound I P k t n S).re
        = effReach (P.result (P.step t n S.prep)).2.1 (P.result (P.step t n S.prep)).2.2 ∧
      (stageRound I P k t n S).scan
        = vOnlineRun (stageRound I P k t n S).u (stageRound I P k t n S).v k
            (stageRound I P k t n S).pe (stageRound I P k t n S).re (t.drop S.W) S.W ∧
      (stageRound I P k t n S).matched
        = vAnswer (stageRound I P k t n S).u (stageRound I P k t n S).v k
            (stageRound I P k t n S).pe (stageRound I P k t n S).re (t.drop S.W) S.W := by
  unfold stageRound
  rw [if_neg (by omega), if_neg (by omega), if_pos hn]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stageRound_adv (h : 2 * S.W < n) :
    (stageRound I P k t n S).u = S.u ∧
      (stageRound I P k t n S).v = S.v ∧
      (stageRound I P k t n S).pe = S.pe ∧
      (stageRound I P k t n S).re = S.re ∧
      (stageRound I P k t n S).scan
        = vRunIn S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) (gsRate k) S.scan ∧
      (stageRound I P k t n S).matched
        = vReportedIn S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) (gsRate k) S.scan := by
  unfold stageRound
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Branches

/-! ### 段の照合器成分の同定 -/

/-- 段幅 `W` の段が（ラウンド `2 * W` に）出す分解 `(s, p₁, r)`。 -/
def stageRes : ℕ × ℕ × ℕ := P.result (P.runTo w W (2 * W))

/-- 分解の短い接頭辞。 -/
def stageU : List α := ((w.take W).reverse).take (stageRes P w W).1

/-- 分解の本体。 -/
def stageV : List α := ((w.take W).reverse).drop (stageRes P w W).1

/-- 正規化した周期。 -/
def stagePe : ℕ := effPeriod (stageV P w W) (stageRes P w W).2.1

/-- 正規化した到達域。 -/
def stageRe : ℕ := effReach (stageRes P w W).2.1 (stageRes P w W).2.2

/-- **段の照合器の同定**：ラウンド `2 * W` 以降、段の状態の照合成分は
`PalPeg.GSVerifier` の機械をテキスト `w.drop W`・テキストラウンド `n - W` で
走らせたものと一致する。 -/
theorem stage_active (hW : 0 < W) : ∀ {n : ℕ}, 2 * W ≤ n →
    (stageState I P k w W n).u = stageU P w W ∧
      (stageState I P k w W n).v = stageV P w W ∧
      (stageState I P k w W n).pe = stagePe P w W ∧
      (stageState I P k w W n).re = stageRe P w W ∧
      (stageState I P k w W n).scan
        = vOnlineRun (stageU P w W) (stageV P w W) k (stagePe P w W) (stageRe P w W)
            (w.drop W) (n - W) ∧
      (stageState I P k w W n).matched
        = vAnswer (stageU P w W) (stageV P w W) k (stagePe P w W) (stageRe P w W)
            (w.drop W) (n - W) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨m, hm⟩ : ∃ m, 2 * W = m + 1 := ⟨2 * W - 1, by omega⟩
    have h1 : 2 * W - 1 = m := by omega
    have hWm : (stageState I P k w W (2 * W - 1)).W = W := stageState_W I P k w W _
    have hst : stageState I P k w W (2 * W)
        = stageRound I P k (w.take (2 * W)) (2 * W) (stageState I P k w W (2 * W - 1)) := by
      rw [h1, hm]; exact stageState_succ I P k w W m
    have hprep : P.step (w.take (2 * W)) (2 * W) (stageState I P k w W (2 * W - 1)).prep
        = P.runTo w W (2 * W) := by
      rw [h1, stageState_prep, hm]
      simp only [PrepImpl.runTo, if_neg (show ¬ (m + 1 ≤ W) by omega),
        if_pos (show m + 1 ≤ 2 * W by omega)]
    have htake : (w.take (2 * W)).take W = w.take W := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have hdrop : (w.take (2 * W)).drop W = (w.drop W).take W := by
      rw [List.take_drop, show W + W = 2 * W from by omega]
    have hsub : 2 * W - W = W := by omega
    obtain ⟨hu, hv, hpe, hre, hscan, hmatched⟩ :=
      stageRound_act (I := I) (P := P) (k := k) (t := w.take (2 * W)) (n := 2 * W)
        (S := stageState I P k w W (2 * W - 1)) (by rw [hWm]; omega) (by rw [hWm])
    have hU : (stageRound I P k (w.take (2 * W)) (2 * W)
        (stageState I P k w W (2 * W - 1))).u = stageU P w W := by
      rw [hu, hWm, htake, hprep]; rfl
    have hV : (stageRound I P k (w.take (2 * W)) (2 * W)
        (stageState I P k w W (2 * W - 1))).v = stageV P w W := by
      rw [hv, hWm, htake, hprep]; rfl
    have hPe : (stageRound I P k (w.take (2 * W)) (2 * W)
        (stageState I P k w W (2 * W - 1))).pe = stagePe P w W := by
      rw [hpe, hWm, htake, hprep]; rfl
    have hRe : (stageRound I P k (w.take (2 * W)) (2 * W)
        (stageState I P k w W (2 * W - 1))).re = stageRe P w W := by
      rw [hre, hprep]; rfl
    refine ⟨by rw [hst]; exact hU, by rw [hst]; exact hV, by rw [hst]; exact hPe,
      by rw [hst]; exact hRe, ?_, ?_⟩
    · rw [hst, hscan, hU, hV, hPe, hRe, hWm, hdrop, hsub]
      exact vOnlineRun_take le_rfl
    · rw [hst, hmatched, hU, hV, hPe, hRe, hWm, hdrop, hsub]
      exact vAnswer_take le_rfl
  | succ n hn ih =>
    obtain ⟨hu, hv, hpe, hre, hscan, hmatched⟩ := ih
    have hWn : (stageState I P k w W n).W = W := stageState_W I P k w W n
    have hdrop : (w.take (n + 1)).drop W = (w.drop W).take (n + 1 - W) := by
      rw [List.take_drop, show W + (n + 1 - W) = n + 1 from by omega]
    obtain ⟨au, av, ape, are, ascan, amatched⟩ :=
      stageRound_adv (I := I) (P := P) (k := k) (t := w.take (n + 1)) (n := n + 1)
        (S := stageState I P k w W n) (by rw [hWn]; omega)
    rw [stageState_succ]
    refine ⟨by rw [au, hu], by rw [av, hv], by rw [ape, hpe], by rw [are, hre], ?_, ?_⟩
    · rw [ascan, hu, hv, hpe, hre, hscan, hWn, hdrop,
        vRunIn_take le_rfl _ _ (vOnlineRun_pos _ _ _ _ _ _ _),
        show n + 1 - W = (n - W) + 1 from by omega]
      rfl
    · rw [amatched, hu, hv, hpe, hre, hscan, hWn, hdrop,
        vReportedIn_take le_rfl _ _ (vOnlineRun_pos _ _ _ _ _ _ _),
        show n + 1 - W = (n - W) + 1 from by omega]
      rfl

/-! ## §4 正当性 -/

omit [DecidableEq α] in
/-- `GSDecomp` の L1 の第 2 評価は、`p₁ = 0` を正規化した周期に対しても成り立つ。 -/
theorem eff_L1b {x : List α} {k s p₁ r : ℕ} (hk : 3 ≤ k) (H : GSDecomp x k s p₁ r)
    (hx : x ≠ []) : (k - 2) * s < (k - 1) * effPeriod (x.drop s) p₁ := by
  by_cases hp : p₁ = 0
  · have hlen : (x.drop s).length = x.length - s := List.length_drop
    rw [effPeriod, if_pos hp, hlen]
    have h3 : 1 * ((x.length - s) + 1) ≤ (k - 1) * ((x.length - s) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [one_mul] at h3
    have hcb := H.cut_bound hx
    have h1 : (k - 1) * s = (k - 2) * s + s := by
      have hkk : k - 1 = (k - 2) + 1 := by omega
      rw [hkk]; ring
    omega
  · rw [effPeriod, if_neg hp]
    exact H.cut_period_bound hp

/-- **段の照合成分は `stageMatch` そのもの**：検証器つき機械の出力は
オラクル版の段照合器と一致する。 -/
theorem stage_matched {Cp : ℕ} (hk : 3 ≤ k) (hP : PrepImplSpec P k Cp) (hW : 0 < W)
    (hWlen : 2 * W ≤ w.length) {n : ℕ} (hn : 2 * W ≤ n) :
    (stageState I P k w W n).matched
      = stageMatch w W k (stageRes P w W).1 (stageRes P w W).2.1 (stageRes P w W).2.2 n := by
  obtain ⟨-, -, -, -, -, hm⟩ := stage_active I P k w W hW hn
  obtain ⟨H, hs⟩ :
      GSDecomp ((w.take W).reverse) k (stageRes P w W).1 (stageRes P w W).2.1
        (stageRes P w W).2.2 ∧ (stageRes P w W).1 < W := hP.correct w W hW hWlen
  have hxlen : ((w.take W).reverse).length = W := by
    rw [List.length_reverse, List.length_take_of_le (by omega)]
  have hx : (w.take W).reverse ≠ [] := by
    intro h
    rw [h, List.length_nil] at hxlen
    omega
  have hulen : (stageU P w W).length = (stageRes P w W).1 := by
    rw [stageU, List.length_take, hxlen, Nat.min_eq_left (by omega)]
  have hcat : stageU P w W ++ stageV P w W = (w.take W).reverse :=
    List.take_append_drop _ _
  have hK : KSimple (stageV P w W) k (stagePe P w W) (stageRe P w W) :=
    H.toGSCore.ksimple_eff
  have hcb : (k - 1) * (stageRes P w W).1 < W := by
    have hb := H.cut_bound hx
    rwa [hxlen] at hb
  have hL1a : (k - 1) * (stageU P w W).length
      < (stageU P w W ++ stageV P w W).length := by
    rw [hcat, hxlen, hulen]
    exact hcb
  have hL1b : (k - 2) * (stageU P w W).length < (k - 1) * (stagePe P w W) := by
    rw [hulen]
    exact eff_L1b hk H hx
  rw [hm]
  exact vAnswer_eq_answer hK hk hL1a hL1b (n - W)

/-! ### 出力の同定 -/

omit [DecidableEq α] in
theorem any_map_stage (g : ℕ → StageState α I P) (p : StageState α I P → Bool) :
    ∀ l : List ℕ, (l.map g).any p = l.any (fun x => p (g x)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, ih]

omit [DecidableEq α] in
theorem list_any_unique {l : List ℕ} {a : ℕ} (ha : a ∈ l) (g : ℕ → Bool)
    (hg : ∀ b ∈ l, b ≠ a → g b = false) : l.any g = g a := by
  cases hga : g a with
  | true => exact List.any_eq_true.mpr ⟨a, ha, hga⟩
  | false =>
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨x, hx, hgx⟩ := List.any_eq_true.mp h
    by_cases hxa : x = a
    · rw [hxa, hga] at hgx; exact Bool.noConfusion hgx
    · rw [hg x hx hxa] at hgx; exact Bool.noConfusion hgx

/-- **出力は `dyadicAnswer` を実時間 GS 照合器で駆動したものと一致する**。 -/
theorem output_eq_dyadic {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (hk : 3 ≤ k) {n : ℕ} (hn : n ≤ w.length) :
    output I P (w.take n) n (fullState I P k w n)
      = dyadicAnswer w (gsOracles w k (fun W => (stageRes P w W).1)
          (fun W => (stageRes P w W).2.1) (fun W => (stageRes P w W).2.2)) n := by
  unfold output dyadicAnswer
  split_ifs with h2 h4
  · rfl
  · rw [List.getElem?_take_of_lt (show 0 < n by omega),
      List.getElem?_take_of_lt (show n - 1 < n by omega)]
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨h2W, h4W⟩ := stageOf_spec (n := n) (by omega)
    have hW : 0 < stageOf n := by omega
    have hWlen : 2 * stageOf n ≤ w.length := by omega
    rw [fullState, any_map_stage]
    rw [list_any_unique (stageOf_mem_live hn4) _ ?_]
    · rw [stageState_W]
      simp only [decide_true, Bool.true_and]
      rw [stage_matched I P k w (stageOf n) hk hP hW hWlen h2W, stageState_mid]
      have hmid : I.flag (I.runTo w (stageOf n) n) n = middleFlag w (stageOf n) n := by
        rw [Bool.eq_iff_iff, middleFlag, decide_eq_true_iff]
        exact hI.correct w (stageOf n) n hW h2W h4W hn
      rw [hmid, stageAnswer, gsOracles]
      simp only [if_neg (show stageOf n ≠ 0 by omega)]
    · intro b _ hb
      rw [stageState_W]
      simp only [decide_eq_false_iff_not.mpr hb, Bool.false_and]

/-- **主定理（正当性）**：機械の出力は各ラウンド `n ≤ |w|` で
接頭辞 `w.take n` の回文性を正しく答える。 -/
theorem output_correct {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (hk : 3 ≤ k) {n : ℕ} (hn : n ≤ w.length) :
    output I P (w.take n) n (fullState I P k w n) = true ↔ IsPal (w.take n) := by
  rw [output_eq_dyadic I P k w hI hP hk hn]
  refine dyadic_gs_correct (by omega) (fun W hW hWlen => ⟨?_, ?_⟩) n hn
  · exact (hP.correct w W hW hWlen).1.toGSCore
  · exact (hP.correct w W hW hWlen).2

/-- 系（`α = Fin 2`）：読み終えた時刻の出力は `w ∈ PAL` と一致する。 -/
theorem output_mem_PAL {I : MiddleImpl (Fin 2)} {P : PrepImpl (Fin 2)} {k Cm Cp : ℕ}
    {w : List (Fin 2)} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp) (hk : 3 ≤ k) :
    output I P (w.take w.length) w.length (fullState I P k w w.length) = true ↔ w ∈ PAL := by
  rw [output_correct I P k w hI hP hk le_rfl, List.take_length]
  exact (mem_PAL_iff_isPal w).symm

/-! ## §5 1 ラウンドの費用 -/

omit [DecidableEq α] in
theorem list_sum_le (l : List ℕ) (b : ℕ) (h : ∀ x ∈ l, x ≤ b) : l.sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    have h3 : (l.length + 1) * b = b + l.length * b := by ring
    simp only [List.sum_cons, List.length_cons]
    omega

/-- 生きている段は高々 2 つなので、機械の状態も高々 2 段ぶんである。 -/
theorem fullState_length_le (n : ℕ) : (fullState I P k w n).length ≤ 2 := by
  rw [fullState, List.length_map]
  exact liveStages_length_le n

/-- **1 段・1 ラウンドの費用**（照合器を起動するラウンド `n = 2 * W` を除く）。 -/
theorem stageCost_le {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (t : List α) (n : ℕ) (S : StageState α I P) (h : n ≠ 2 * S.W) :
    stageCost I P k t n S ≤ gsRateInterleaved k + Cm + Cp := by
  unfold stageCost
  rw [if_neg h]
  split_ifs with h1 h2
  · omega
  · have hm := hI.cost_le t n S.mid
    have hp := hP.cost_le t n S.prep
    omega
  · have hm := hI.cost_le t n S.mid
    have hv := vRound_cost_le S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) S.scan
    omega

/-- 起動ラウンドも含めた粗い上界（起動時の追い付きは `W ≤ n` ラウンドぶん）。 -/
theorem stageCost_le' {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (t : List α) (n : ℕ) (S : StageState α I P) (hSn : S.W ≤ n) :
    stageCost I P k t n S ≤ n * gsRateInterleaved k + Cm + Cp := by
  have hmul : ∀ a b : ℕ, a ≤ b → a * gsRateInterleaved k ≤ b * gsRateInterleaved k :=
    fun a b h => Nat.mul_le_mul_right _ h
  unfold stageCost
  split_ifs with h1 h2 h3
  · omega
  · have hm := hI.cost_le t n S.mid
    have hp := hP.cost_le t n S.prep
    omega
  · have hm := hI.cost_le t n S.mid
    have hp := hP.cost_le t n S.prep
    have := hmul S.W n hSn
    omega
  · have hm := hI.cost_le t n S.mid
    have hv := vRound_cost_le S.u S.v k S.pe S.re (t.drop S.W) (n - S.W) S.scan
    have h1' := hmul 1 n (by omega)
    rw [one_mul] at h1'
    omega

/-- **1 ラウンドの総費用**（照合器の起動が起きないラウンド）：生きている段は
高々 2 つなので、単位操作は `2 * (gsRateInterleaved k + Cm + Cp)` 以下
（加法定数 `c₀ = 0`）。 -/
theorem round_cost_le {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (n : ℕ) (hno : ∀ W ∈ liveStages n, n ≠ 2 * W) :
    roundCost I P k w n ≤ 2 * (gsRateInterleaved k + Cm + Cp) := by
  unfold roundCost
  have hbound : ∀ x ∈ (liveStages n).map
      (fun W => stageCost I P k (w.take n) n (stageState I P k w W (n - 1))),
      x ≤ gsRateInterleaved k + Cm + Cp := by
    intro x hx
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
    refine stageCost_le I P k hI hP _ _ _ ?_
    rw [stageState_W]
    exact hno W hW
  have h1 := list_sum_le _ (gsRateInterleaved k + Cm + Cp) hbound
  rw [List.length_map] at h1
  exact le_trans h1 (Nat.mul_le_mul_right _ (liveStages_length_le n))

/-- 起動ラウンドも含めた無条件の（粗い）上界。 -/
theorem round_cost_le' {Cm Cp : ℕ} (hI : MiddleImplSpec I Cm) (hP : PrepImplSpec P k Cp)
    (n : ℕ) :
    roundCost I P k w n ≤ 2 * (n * gsRateInterleaved k + Cm + Cp) := by
  unfold roundCost
  have hbound : ∀ x ∈ (liveStages n).map
      (fun W => stageCost I P k (w.take n) n (stageState I P k w W (n - 1))),
      x ≤ n * gsRateInterleaved k + Cm + Cp := by
    intro x hx
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
    refine stageCost_le' I P k hI hP _ _ _ ?_
    rw [stageState_W]
    exact (liveStages_spec hW).1
  have h1 := list_sum_le _ (n * gsRateInterleaved k + Cm + Cp) hbound
  rw [List.length_map] at h1
  exact le_trans h1 (Nat.mul_le_mul_right _ (liveStages_length_le n))

/-! ## §6 オンライン性 -/

/-- 段の状態はラウンド `n` までに読んだ接頭辞だけで決まる。 -/
theorem stageState_take : ∀ {n m : ℕ}, n ≤ m →
    stageState I P k (w.take m) W n = stageState I P k w W n := by
  intro n
  induction n with
  | zero => intro m _; rfl
  | succ n ih =>
    intro m hm
    rw [stageState_succ, stageState_succ, ih (show n ≤ m by omega),
      List.take_take, Nat.min_eq_left (by omega)]

/-- **オンライン性**：機械の全状態も接頭辞だけで決まる。 -/
theorem fullState_take {n m : ℕ} (hnm : n ≤ m) :
    fullState I P k (w.take m) n = fullState I P k w n := by
  unfold fullState
  refine congrArg (fun f => (liveStages n).map f) ?_
  funext W'
  exact stageState_take I P k w W' hnm

/-- **`runFull_take`**：ラウンド `n` の状態は `w.take n` だけで決まる。 -/
theorem runFull_take (n : ℕ) :
    fullState I P k (w.take n) n = fullState I P k w n :=
  fullState_take I P k w le_rfl

end PalPeg
