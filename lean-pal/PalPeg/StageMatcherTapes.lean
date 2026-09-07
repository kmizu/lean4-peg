import PalPeg.PatternTapes
import PalPeg.VerifierFeed
import PalPeg.Metered
import PalPeg.StageMatcher

/-!
# 走査段（matcher フェーズ）の **固定動作数ラウンド** 機械

`PalPeg.VerifierFeed` §16–19 の供給つき機械 `VMachine'` は、1 ラウンドに
`gsRate k` **歩**（＝ `vscanOne''`）を実行する。1 歩の動作数は有界でないので、
実機のラウンドは固定本数でない。本ファイルは `PalPeg.Metered` の計量式
スケジューラを **テープ側に持ち上げ**、1 ラウンド＝固定本数の機械を与える。

## モデル

* 状態 `SMachine = (VMachine'（両待ち行列こみ）, rem)`。`rem = 0` がステップ境界。
* 1 歩のプログラムは `fstep`（= `tT` の供給 `vfillIf1'` ＋ `vscanOne''`）で、
  その動作数は `fcost ≤ 34 * |vprogram'| + 103`。
* **計量単位** `U`：1 計量動作 = `U` テープ動作。ステップの計量コストは
  `cst = ⌈fcost / U⌉`。前進（比較成功）歩のコストが `≤ U` になるように `U` を取れば
  `Metered.metered_answer_correct'` の `hadvance` が成り立つ（`fadvance` 仮定）。
* 1 動作 `sact` は `Metered.mact` と同じ会計：境界で `Enabled` なら開始、
  入り切らなければ `rem := cst - (残り予算)` として **駐機**（park）する。
  ステップは `rem` が尽きる瞬間に **原子的に** 適用されるので、テープの正しさは
  ステップ境界でのみ主張される（`VFeedInv'` はまさにその形）。
* 1 ラウンド：到着 `varrive'`（両待ち行列、`≤ 52`）→ `Txt2` の頭出し供給
  `vfillHead2`（`≤ 33`）→ ちょうど `B = mRate A B' k` 計量動作。
  ラウンドの動作予算は `85 + U * B`（`85 = 52 + 33`）。

## 定数

`vprogram'_amortized`（`GSVerifierTapes` §9）は
`|vprogram'| + 2·c' ≤ (8k+14)·ΔΦ + 18 + 2·c`。`fcost = 34·|vprogram'| + 103` なので
（`c` の項を落とした形で）

* `A  := 34 * (8 * k + 14)`
* `B' := 34 * 18 + 103 = 715`
* `B  := Metered.mRate A B' k = (k+1) * (A + B')`

計量化（単位 `U`）では `A' := A`, `B'' := B'` をそのまま `⌈·/U⌉` の外側評価に使う
（`⌈x/U⌉ ≤ x`）。`cst` と `fcost` の関係は仮定 `hcst` として明示的に持つ。
-/

namespace PalPeg
namespace StageMatcherTapes

open PalPeg.VerifierFeed

variable {sc : ℕ}

/-! ## 1. 状態と 1 歩 -/

/-- 計量式のテープ機械の状態：供給つき機械と、実行中ステップの残り計量動作数。 -/
structure SMachine (sc : ℕ) where
  /-- テープ（走査 8 本 ＋ 検証器 2 本 ＋ 待ち行列 2 本）。 -/
  M : VMachine' sc
  /-- 実行中ステップの残り計量動作数（`0` がステップ境界）。 -/
  rem : ℕ

/-- ゴースト射影：`Metered.MState` へ。 -/
def gm (S : SMachine sc) : MState := ⟨S.M.z.1, S.rem⟩

@[simp] theorem SMachine.mk_M (M : VMachine' sc) (j : ℕ) : (SMachine.mk M j).M = M := rfl
@[simp] theorem SMachine.mk_rem (M : VMachine' sc) (j : ℕ) : (SMachine.mk M j).rem = j := rfl

@[simp] theorem gm_st (S : SMachine sc) : (gm S).st = S.M.z.1 := rfl
@[simp] theorem gm_rem (S : SMachine sc) : (gm S).rem = S.rem := rfl

/-- **1 歩のプログラム**：`tT` の供給 ＋ 供給つき走査＋検証の一歩。 -/
def fstep (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) : VMachine' sc :=
  vscanOne'' blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)

/-- 1 歩のテープ動作数。 -/
def fcost (blank endSym mark : Fin sc) (k n : ℕ) (M : VMachine' sc) : ℕ :=
  34 * (GSVTapes.vprogram' blank endSym mark k (vfillIf1' blank mark n M).vt).length + 103

theorem fstep_z (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (fstep blank endSym mark u v k p₁ r n Text M).z = vStep u v k p₁ r Text M.z := by
  rw [fstep, vscanOne''_z, vfillIf1'_z]

theorem fstep_st (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (fstep blank endSym mark u v k p₁ r n Text M).z.1 = scanStep v k p₁ r Text M.z.1 := by
  rw [fstep_z, vStep_fst]

theorem fstep_cost (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (fstep blank endSym mark u v k p₁ r n Text M).cost ≤ M.cost + fcost blank endSym mark k n M := by
  have h1 := vfillIf1'_cost blank mark n M
  have h2 := vscanOne''_cost blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)
  show (vscanOne'' blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)).cost ≤ _
  unfold fcost
  omega

/-! ## 2. 計量単位 -/

/-- 天井除算 `⌈x / U⌉`。 -/
def uceil (U x : ℕ) : ℕ := (x + U - 1) / U

theorem le_mul_uceil {U : ℕ} (hU : 0 < U) (x : ℕ) : x ≤ U * uceil U x := by
  have h := Nat.div_add_mod (x + U - 1) U
  have hlt : (x + U - 1) % U < U := Nat.mod_lt _ hU
  unfold uceil
  omega

theorem uceil_le_self {U : ℕ} (hU : 0 < U) (x : ℕ) : uceil U x ≤ x := by
  unfold uceil
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have : (0 + U - 1) / U = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · have hle : x + U - 1 ≤ U * x := by
      have hx1 : x = 1 + (x - 1) := by omega
      have hsplit : U * x = U + U * (x - 1) := by
        conv_lhs => rw [hx1]
        rw [Nat.mul_add, Nat.mul_one]
      have h3 : x - 1 ≤ U * (x - 1) := Nat.le_mul_of_pos_left _ hU
      omega
    calc (x + U - 1) / U ≤ (U * x) / U := Nat.div_le_div_right hle
      _ = x := by rw [Nat.mul_div_cancel_left x hU]

/-! ## 3. 定数 -/

/-- `A = 34 * (8k + 14)`（`vprogram'_amortized` の償却係数 × 1 動作あたりの供給係数）。 -/
def stageA (k : ℕ) : ℕ := 34 * (8 * k + 14)

/-- `B' = 34 * 18 + 103 = 715`（償却の定数項 ＋ 1 歩の定数動作）。 -/
def stageB' : ℕ := 34 * 18 + 103

/-- `B = mRate A B' k = (k+1) * (A + B')`：1 ラウンドの計量動作数。 -/
def stageB (k : ℕ) : ℕ := mRate (stageA k) stageB' k

example : stageB' = 715 := rfl
example : stageA 8 = 2652 := by norm_num [stageA]
example : stageB 8 = 30303 := by norm_num [stageB, stageA, stageB', mRate]

/-- 償却評価の持ち上げ：`|vprogram'| ≤ (8k+14)·ΔΦ + 18` なら
`fcost ≤ stageA k · ΔΦ + stageB'`、したがって計量コストも同じ形で抑えられる。 -/
theorem fcost_le_of_amortized {blank endSym mark : Fin sc} {k n D : ℕ}
    {M : VMachine' sc}
    (h : (GSVTapes.vprogram' blank endSym mark k (vfillIf1' blank mark n M).vt).length
      ≤ (8 * k + 14) * D + 18) :
    fcost blank endSym mark k n M ≤ stageA k * D + stageB' := by
  unfold fcost stageA stageB'
  have h2 : 34 * (GSVTapes.vprogram' blank endSym mark k
      (vfillIf1' blank mark n M).vt).length ≤ 34 * ((8 * k + 14) * D + 18) :=
    Nat.mul_le_mul_left 34 h
  have e : 34 * ((8 * k + 14) * D + 18) = 34 * (8 * k + 14) * D + 34 * 18 := by ring
  omega

theorem uceil_fcost_le_of_amortized {blank endSym mark : Fin sc} {k n D U : ℕ}
    (hU : 0 < U) {M : VMachine' sc}
    (h : (GSVTapes.vprogram' blank endSym mark k (vfillIf1' blank mark n M).vt).length
      ≤ (8 * k + 14) * D + 18) :
    uceil U (fcost blank endSym mark k n M) ≤ stageA k * D + stageB' :=
  le_trans (uceil_le_self hU _) (fcost_le_of_amortized h)

/-! ## 4. 1 計量動作 -/

/-- **1 計量動作**（`Metered.mact` のテープ版）。境界（`rem = 0`）で `Enabled` なら
現ステップを開始し、コストが `1` 以下なら即完了、そうでなければ駐機する。
実行中なら残りを 1 減らし、尽きる瞬間に `fstep` を **原子的に** 適用する。 -/
def sact (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (cst : ScanState → ℕ) (n : ℕ) (S : SMachine sc) : SMachine sc :=
  if S.rem = 0 then
    (if Enabled v n S.M.z.1 then
        (if cst S.M.z.1 ≤ 1 then ⟨fstep blank endSym mark u v k p₁ r n Text S.M, 0⟩
          else ⟨S.M, cst S.M.z.1 - 1⟩)
      else S)
  else if S.rem = 1 then ⟨fstep blank endSym mark u v k p₁ r n Text S.M, 0⟩
  else ⟨S.M, S.rem - 1⟩

/-- `j` 個の計量動作。 -/
def sacts (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (cst : ScanState → ℕ) (n : ℕ) :
    ℕ → SMachine sc → SMachine sc
  | 0, S => S
  | j + 1, S => sacts blank endSym mark u v k p₁ r Text cst n j
      (sact blank endSym mark u v k p₁ r Text cst n S)

/-! ## 5. ゴーストの一致（`Metered` との対応） -/

section Ghost

variable {blank endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {U : ℕ}

/-- 抽象コスト関数がテープ側の 1 歩コストの計量値であること。 -/
def CostSpec (blank endSym mark : Fin sc) (k U : ℕ) (cst : ScanState → ℕ) : Prop :=
  ∀ (n : ℕ) (M : VMachine' sc), cst M.z.1 = uceil U (fcost blank endSym mark k n M)

theorem sact_ghost (n : ℕ) (S : SMachine sc) :
    gm (sact blank endSym mark u v k p₁ r Text cst n S)
      = mact v k p₁ r Text cst n (gm S) := by
  unfold sact mact gm
  simp only [gm_st, gm_rem]
  split_ifs <;> simp [fstep_st]

theorem sacts_ghost (n : ℕ) :
    ∀ (j : ℕ) (S : SMachine sc),
      gm (sacts blank endSym mark u v k p₁ r Text cst n j S)
        = macts v k p₁ r Text cst n j (gm S) := by
  intro j
  induction j with
  | zero => intro S; rfl
  | succ j ih => intro S; rw [sacts, macts, ih, sact_ghost]

end Ghost

/-! ## 5. 1 ラウンド -/

/-- ラウンドあたりの計量動作数 `B = mRate A B' k`。 -/
abbrev sRate (A B' k : ℕ) : ℕ := mRate A B' k

/-- **1 ラウンド**：到着（両待ち行列）→ `Txt2` の頭出し供給 → ちょうど `B` 計量動作。 -/
def sround (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (cst : ScanState → ℕ) (A B' n : ℕ) (a : Fin sc)
    (S : SMachine sc) : SMachine sc :=
  sacts blank endSym mark u v k p₁ r Text cst (n + 1) (sRate A B' k)
    ⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩

/-- **段の走行**：起動フェーズ後の絶対ラウンド `s, s+1, …` を回す。 -/
def stage (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (cst : ScanState → ℕ) (A B' s : ℕ) :
    ℕ → SMachine sc → SMachine sc
  | 0, S => S
  | n + 1, S =>
      sround blank endSym mark u v k p₁ r Text cst A B' (s + n) (Text.getD (s + n) blank)
        (stage blank endSym mark u v k p₁ r Text cst A B' s n S)

/-- ラウンドあたりのテープ動作予算：`85 = 52（到着）+ 33（`Txt2` 頭出し）` ＋ `U * B`。 -/
def roundBudget (U A B' k : ℕ) : ℕ := 85 + U * sRate A B' k

section Rounds

variable {blank endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' : ℕ}

theorem sround_ghost (n : ℕ) (a : Fin sc) (S : SMachine sc) :
    gm (sround blank endSym mark u v k p₁ r Text cst A B' n a S)
      = macts v k p₁ r Text cst (n + 1) (mRate A B' k) (gm S) := by
  rw [sround, sacts_ghost]
  congr 1
  show (⟨(vfillHead2 blank mark (varrive' blank mark a S.M)).z.1, S.rem⟩ : MState) = gm S
  rw [vfillHead2_z, varrive'_z]
  rfl

end Rounds

/-! ## 6. 起動ラウンドの吸収 -/

section Start

variable {α : Type} [DecidableEq α] {u v T : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ}
  {A B' : ℕ}

theorem macts_id_of_not_enabled {n : ℕ} {m : MState} (h0 : m.rem = 0)
    (he : ¬ Enabled v n m.st) :
    ∀ j, macts v k p₁ r T cst n j m = m := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have : mact v k p₁ r T cst n m = m := by
      unfold mact; rw [if_pos h0, if_neg he]
    rw [macts, this, ih]

/-- 起動ラウンド（`n ≤ |u|`）では計量式スケジューラは停止したまま。 -/
theorem metered_start (hv : 0 < v.length) :
    ∀ n, n ≤ u.length →
      metered u v k p₁ r T cst A B' n = (⟨⟨u.length, 0⟩, 0⟩ : MState) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [metered, ih (by omega)]
    refine macts_id_of_not_enabled (v := v) rfl ?_ _
    show ¬ Enabled v (n + 1) (⟨u.length, 0⟩ : ScanState)
    rintro (h | h)
    · simp only [] at h; omega
    · simp only [] at h; omega

end Start

/-! ## 7. 主定理 1：ゴーストの一致 -/

section Main

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' : ℕ}

/-- **`stage_round_spec`（ゴースト部分）**：ラウンド `n` 後のテープ機械のゴーストは、
`Metered.metered` の絶対ラウンド `|u| + n` の状態にちょうど一致する
（起動フェーズの `|u|` ラウンドは `metered_start` で吸収される）。 -/
theorem stage_round_spec (hv : 0 < v.length) {S₀ : SMachine sc}
    (h0 : gm S₀ = metered u v k p₁ r Text cst A B' u.length) :
    ∀ n, gm (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S₀)
      = metered u v k p₁ r Text cst A B' (u.length + n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have e : u.length + (n + 1) = (u.length + n) + 1 := by omega
    rw [stage, sround_ghost, ih, e, metered]

/-- 起動状態（`rem = 0`、走査状態 `⟨|u|, 0⟩`）は `metered … |u|` に一致する。 -/
theorem gm_start (hv : 0 < v.length) {S₀ : SMachine sc}
    (hz : S₀.M.z = ((⟨u.length, 0⟩ : ScanState), 0)) (hr : S₀.rem = 0) :
    gm S₀ = metered u v k p₁ r Text cst A B' u.length := by
  rw [metered_start (u := u) (v := v) (T := Text) (cst := cst) (A := A) (B' := B') hv
    u.length (Nat.le_refl _)]
  unfold gm
  rw [hr, hz]

end Main

/-! ## 8. 不変条件の保存 -/

section Inv

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' : ℕ}

/-- ラウンド内の不変条件。 -/
def SInner (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc)) (k p₁ r n : ℕ)
    (S : SMachine sc) : Prop :=
  VFeedInv' blank startSym endSym mark u v Text k p₁ r n S.M ∧
    Ok2 n S.M (S.M.z.1.pos - u.length + S.M.z.2) ∧
    (S.rem ≠ 0 → Enabled v n S.M.z.1)

/-- ラウンド境界の不変条件（`Ok2` はラウンド頭の供給で回復するので不要）。 -/
def SBnd (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc)) (k p₁ r n : ℕ)
    (S : SMachine sc) : Prop :=
  VFeedInv' blank startSym endSym mark u v Text k p₁ r n S.M ∧
    (S.rem ≠ 0 → Enabled v n S.M.z.1)

variable (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
  (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)

include hmb hk hv hend hendu hb hmT in
theorem sact_inner {n : ℕ} (hn : n ≤ Text.length) {S : SMachine sc}
    (h : SInner blank startSym endSym mark u v Text k p₁ r n S) :
    SInner blank startSym endSym mark u v Text k p₁ r n
      (sact blank endSym mark u v k p₁ r Text cst n S) := by
  obtain ⟨hF, hok, hE⟩ := h
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hmb hn hF
  have hfok : Ok2 n (vfillIf1' blank mark n S.M)
      ((vfillIf1' blank mark n S.M).z.1.pos - u.length
        + (vfillIf1' blank mark n S.M).z.2) := by
    unfold vfillIf1'
    split_ifs with hc
    · exact hok
    · exact hok
  have hstep : ∀ he : Enabled v n S.M.z.1,
      SInner blank startSym endSym mark u v Text k p₁ r n
        ⟨fstep blank endSym mark u v k p₁ r n Text S.M, 0⟩ := by
    intro he
    obtain ⟨s1, s2⟩ := vscanOne''_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
      (Text := Text) hk hmb hv hend hendu hb hmT hn (vfillIf1'_ready hF he) hfF hfok
    exact ⟨s1, s2, by simp⟩
  unfold sact
  split_ifs with h0 he hc h1
  · exact hstep he
  · exact ⟨hF, hok, fun _ => he⟩
  · exact ⟨hF, hok, hE⟩
  · exact hstep (hE h0)
  · exact ⟨hF, hok, fun _ => hE h0⟩

include hmb hk hv hend hendu hb hmT in
theorem sacts_inner {n : ℕ} (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (S : SMachine sc),
      SInner blank startSym endSym mark u v Text k p₁ r n S →
      SInner blank startSym endSym mark u v Text k p₁ r n
        (sacts blank endSym mark u v k p₁ r Text cst n j S) := by
  intro j
  induction j with
  | zero => intro S h; exact h
  | succ j ih =>
    intro S h
    exact ih _ (sact_inner hmb hk hv hend hendu hb hmT hn h)

include hmb hk hv hend hendu hb hmT in
/-- **1 ラウンドの不変条件**：`VFeedInv'` はラウンド境界（したがってステップ境界）で保たれる。 -/
theorem sround_bnd {n : ℕ} {a : Fin sc} (hn : n < Text.length) (ha : Text[n]? = some a)
    {S : SMachine sc} (h : SBnd blank startSym endSym mark u v Text k p₁ r n S) :
    SBnd blank startSym endSym mark u v Text k p₁ r (n + 1)
      (sround blank endSym mark u v k p₁ r Text cst A B' n a S) := by
  obtain ⟨hF, hE⟩ := h
  have hA := varrive'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hmb hn ha hF
  obtain ⟨hH, hok⟩ := vfillHead2_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
    hmb hb hmT (by omega : n + 1 ≤ Text.length) hA
  have hstart : SInner blank startSym endSym mark u v Text k p₁ r (n + 1)
      (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ : SMachine sc) := by
    refine ⟨hH, hok, ?_⟩
    intro hr
    have : (vfillHead2 blank mark (varrive' blank mark a S.M)).z = S.M.z := by
      rw [vfillHead2_z, varrive'_z]
    rw [show (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ :
      SMachine sc).M.z.1 = S.M.z.1 from by rw [this]]
    exact (hE hr).mono (Nat.le_succ n)
  have := sacts_inner (cst := cst) hmb hk hv hend hendu hb hmT
    (by omega : n + 1 ≤ Text.length) (sRate A B' k) _ hstart
  exact ⟨this.1, this.2.2⟩

include hmb hk hv hend hendu hb hmT in
/-- **段の走行の不変条件**：各ラウンド境界で `VFeedInv'` が成り立つ。 -/
theorem stage_bnd :
    ∀ (n : ℕ) (S : SMachine sc), u.length + n ≤ Text.length →
      SBnd blank startSym endSym mark u v Text k p₁ r u.length S →
      SBnd blank startSym endSym mark u v Text k p₁ r (u.length + n)
        (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S) := by
  intro n
  induction n with
  | zero => intro S _ h; exact h
  | succ n ih =>
    intro S hle h
    have e : u.length + (n + 1) = (u.length + n) + 1 := by omega
    rw [e]
    exact sround_bnd hmb hk hv hend hendu hb hmT (by omega : u.length + n < Text.length)
      (TextFeed.getD_eq (by omega)) (ih S (by omega) h)

end Inv

/-! ## 9. 動作数（予算）の会計 -/

section Cost

variable {blank endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' U : ℕ}

/-- 実行中ステップですでに払った計量動作数。 -/
def spend (cst : ScanState → ℕ) (S : SMachine sc) : ℕ :=
  if S.rem = 0 then 0 else cst S.M.z.1 - S.rem

theorem sact_cost (hU : 0 < U) (hcst : CostSpec (sc := sc) blank endSym mark k U cst)
    (n : ℕ) (S : SMachine sc) :
    (sact blank endSym mark u v k p₁ r Text cst n S).M.cost
        + U * spend cst (sact blank endSym mark u v k p₁ r Text cst n S)
      ≤ S.M.cost + U * spend cst S + U := by
  have hfc : fcost blank endSym mark k n S.M ≤ U * cst S.M.z.1 := by
    rw [hcst n S.M]; exact le_mul_uceil hU _
  have hstep := fstep_cost blank endSym mark u v k p₁ r n Text S.M
  unfold sact
  split_ifs with h0 he hc h1
  · have e1 : spend cst (⟨fstep blank endSym mark u v k p₁ r n Text S.M, 0⟩ :
        SMachine sc) = 0 := by simp [spend]
    have e2 : spend cst S = 0 := by simp [spend, h0]
    have hle : U * cst S.M.z.1 ≤ U * 1 := Nat.mul_le_mul_left U hc
    simp only [SMachine.mk_M, e1, e2, Nat.mul_one] at *
    omega
  · have e1 : spend cst (⟨S.M, cst S.M.z.1 - 1⟩ : SMachine sc) = 1 := by
      have hne : cst S.M.z.1 - 1 ≠ 0 := by omega
      simp only [spend, SMachine.mk_M, SMachine.mk_rem, if_neg hne]
      omega
    have e2 : spend cst S = 0 := by simp [spend, h0]
    simp only [SMachine.mk_M, e1, e2, Nat.mul_one]
    omega
  · omega
  · have e1 : spend cst (⟨fstep blank endSym mark u v k p₁ r n Text S.M, 0⟩ :
        SMachine sc) = 0 := by simp [spend]
    have e2 : spend cst S = cst S.M.z.1 - 1 := by
      simp only [spend, if_neg h0, h1]
      norm_num
    have h3 : cst S.M.z.1 ≤ (cst S.M.z.1 - 1) + 1 := by omega
    have h4 : U * cst S.M.z.1 ≤ U * ((cst S.M.z.1 - 1) + 1) := Nat.mul_le_mul_left U h3
    have h5 : U * ((cst S.M.z.1 - 1) + 1) = U * (cst S.M.z.1 - 1) + U := by ring
    simp only [SMachine.mk_M, e1, e2]
    omega
  · have hne : S.rem - 1 ≠ 0 := by omega
    have e1 : spend cst (⟨S.M, S.rem - 1⟩ : SMachine sc) = cst S.M.z.1 - (S.rem - 1) := by
      simp only [spend, SMachine.mk_M, SMachine.mk_rem, if_neg hne]
    have e2 : spend cst S = cst S.M.z.1 - S.rem := by simp only [spend, if_neg h0]
    have h2 : cst S.M.z.1 - (S.rem - 1) ≤ (cst S.M.z.1 - S.rem) + 1 := by omega
    have h3 : U * (cst S.M.z.1 - (S.rem - 1)) ≤ U * ((cst S.M.z.1 - S.rem) + 1) :=
      Nat.mul_le_mul_left U h2
    have h4 : U * ((cst S.M.z.1 - S.rem) + 1) = U * (cst S.M.z.1 - S.rem) + U := by ring
    simp only [SMachine.mk_M, e1, e2]
    omega

theorem sacts_cost (hU : 0 < U) (hcst : CostSpec (sc := sc) blank endSym mark k U cst)
    (n : ℕ) :
    ∀ (j : ℕ) (S : SMachine sc),
      (sacts blank endSym mark u v k p₁ r Text cst n j S).M.cost
          + U * spend cst (sacts blank endSym mark u v k p₁ r Text cst n j S)
        ≤ S.M.cost + U * spend cst S + U * j := by
  intro j
  induction j with
  | zero => intro S; simp [sacts]
  | succ j ih =>
    intro S
    have h1 := ih (sact blank endSym mark u v k p₁ r Text cst n S)
    have h2 := sact_cost (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text) hU hcst n S
    have e : U * (j + 1) = U * j + U := by ring
    rw [sacts]
    omega

/-- **1 ラウンドの動作数**：ちょうど `85 + U * B` テープ動作の予算に収まる
（`85 = 52`（到着）`+ 33`（`Txt2` 頭出し供給）、`B = mRate A B' k` 計量動作）。 -/
theorem sround_cost (hU : 0 < U) (hcst : CostSpec (sc := sc) blank endSym mark k U cst)
    (n : ℕ) (a : Fin sc) (S : SMachine sc) :
    (sround blank endSym mark u v k p₁ r Text cst A B' n a S).M.cost
        + U * spend cst (sround blank endSym mark u v k p₁ r Text cst A B' n a S)
      ≤ S.M.cost + U * spend cst S + roundBudget U A B' k := by
  have hAc := varrive'_cost blank mark a S.M
  have hHc := vfillHead2_cost blank mark (varrive' blank mark a S.M)
  have hsp : spend cst (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ :
      SMachine sc) = spend cst S := by
    unfold spend
    have : (vfillHead2 blank mark (varrive' blank mark a S.M)).z = S.M.z := by
      rw [vfillHead2_z, varrive'_z]
    simp only [this]
  have h1 := sacts_cost (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text) hU hcst
    (n + 1) (sRate A B' k)
    (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ : SMachine sc)
  rw [hsp] at h1
  simp only [SMachine.mk_M] at h1
  have hdef : sround blank endSym mark u v k p₁ r Text cst A B' n a S
      = sacts blank endSym mark u v k p₁ r Text cst (n + 1) (sRate A B' k)
        ⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ := rfl
  rw [hdef, roundBudget]
  omega

/-- **段全体の動作数**：`n` ラウンドで `n * (85 + U * B)` テープ動作以内。 -/
theorem stage_cost' (hU : 0 < U) (hcst : CostSpec (sc := sc) blank endSym mark k U cst) :
    ∀ (n : ℕ) (S : SMachine sc),
      (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S).M.cost
          + U * spend cst (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S)
        ≤ S.M.cost + U * spend cst S + n * roundBudget U A B' k := by
  intro n
  induction n with
  | zero => intro S; simp [stage]
  | succ n ih =>
    intro S
    have h1 := ih S
    have h2 := sround_cost (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text)
      (A := A) (B' := B') hU hcst
      (u.length + n) (Text.getD (u.length + n) blank)
      (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S)
    have e : (n + 1) * roundBudget U A B' k
        = n * roundBudget U A B' k + roundBudget U A B' k := by ring
    have hdef : stage blank endSym mark u v k p₁ r Text cst A B' u.length (n + 1) S
        = sround blank endSym mark u v k p₁ r Text cst A B' (u.length + n)
          (Text.getD (u.length + n) blank)
          (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S) := rfl
    rw [hdef]
    omega

theorem stage_cost (hU : 0 < U) (hcst : CostSpec (sc := sc) blank endSym mark k U cst)
    (n : ℕ) (S : SMachine sc) (h0 : S.rem = 0) :
    (stage blank endSym mark u v k p₁ r Text cst A B' u.length n S).M.cost
      ≤ S.M.cost + n * roundBudget U A B' k := by
  have h := stage_cost' (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text)
    (A := A) (B' := B') hU hcst n S
  have e : spend cst S = 0 := by simp [spend, h0]
  rw [e] at h
  omega

end Cost

/-! ## 10. 初期状態 -/

section Init

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' : ℕ}

/-- 段の初期状態：`initVM'` に起動フェーズ `vstartT'` を掛けたもの（`rem = 0`）。
起動フェーズ（`≤ 86 * |u|` 動作）は **段のセットアップ前処理** に計上する。 -/
def initSM (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc)) (k p₁ r : ℕ) :
    SMachine sc :=
  ⟨vstartT' blank mark Text u.length (initVM' blank startSym endSym mark u v Text k p₁ r), 0⟩

/-- **`stage_init`**：初期状態はラウンド境界不変条件を満たし、ゴーストは
`metered … |u|` に一致し、起動フェーズのコストは `≤ 86 * |u|`。 -/
theorem stage_init (hmb : mark ≠ blank) (hv : 0 < v.length)
    (hlen : u.length ≤ Text.length) :
    SBnd blank startSym endSym mark u v Text k p₁ r u.length
        (initSM blank startSym endSym mark u v Text k p₁ r) ∧
      gm (initSM blank startSym endSym mark u v Text k p₁ r)
        = metered u v k p₁ r Text cst A B' u.length ∧
      (initSM blank startSym endSym mark u v Text k p₁ r).M.cost ≤ 86 * u.length := by
  obtain ⟨h1, h2, h3⟩ := vstart_spec (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
    (startSym := startSym) (endSym := endSym) hmb hv hlen
  have hz : (initSM blank startSym endSym mark u v Text k p₁ r).M.z
      = ((⟨u.length, 0⟩ : ScanState), 0) := by
    show (vstartT' blank mark Text u.length
      (initVM' blank startSym endSym mark u v Text k p₁ r)).z = _
    rw [h2, vOnlineRun_start hv u.length (Nat.le_refl _)]
  exact ⟨⟨h1, by simp [initSM]⟩, gm_start (cst := cst) (A := A) (B' := B') hv hz rfl, h3⟩

end Init

/-! ## 11. 主定理 2：ラウンドの出力 -/

section Answer

variable {α : Type} [DecidableEq α] {u v Text : List α} {k p₁ r : ℕ}
  {cst : ScanState → ℕ} {A B' : ℕ}

/-- **`stage_answer_read`**：ラウンド `n`（絶対）に読み出される答えのビット
`Metered.manswer` は、その場で正しい（`Metered.metered_answer_correct'` の
インスタンス）。ゴーストは `stage_round_spec` によりテープ機械の状態そのもの。 -/
theorem stage_answer_read (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B') * (Phi k (scanStep v k p₁ r Text st) - Phi k st))
    (hadvance : ∀ st, st.q ≠ v.length → Text[st.pos + st.q]? = v[st.q]? → cst st ≤ 1)
    (n : ℕ) (hn : (u ++ v).length ≤ n) :
    manswer u v k p₁ r Text cst A B' n
      = decide (OccAt (u ++ v) Text (n - (u ++ v).length)) :=
  metered_answer_correct' hK hk hv hC hcost hadvance n hn

end Answer

/-! ## 12. 段の仕様（`StageMatcher` との橋渡し） -/

section Stage

variable {α : Type} [DecidableEq α] {w : List α} {S k s p₁ r : ℕ} {A B' : ℕ}
  {cst : ScanState → ℕ}

/-- **段の出力の意味**：`manswer` は `stageMatchH` と同じ真理値を返す。 -/
theorem stage_answer_stageMatchH (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B')
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    {n : ℕ} (h2S : 2 * S ≤ n) (hn : n ≤ w.length) :
    (manswer ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) k
        (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S)
        cst A B' (n - S) = true)
      ↔ occursAt (w.take (S / 2)).reverse (w.take n) := by
  have hxlen : ((w.take (S / 2)).reverse).length = S / 2 := by
    rw [List.length_reverse, List.length_take_of_le (by omega)]
  have hv : 0 < ((w.take (S / 2)).reverse.drop s).length := by
    rw [List.length_drop, hxlen]; omega
  have huv : ((w.take (S / 2)).reverse.take s) ++ ((w.take (S / 2)).reverse.drop s)
      = (w.take (S / 2)).reverse := List.take_append_drop s _
  have hlen : (((w.take (S / 2)).reverse.take s)
      ++ ((w.take (S / 2)).reverse.drop s)).length = S / 2 := by rw [huv]; exact hxlen
  rw [stage_answer_read (Text := w.drop S) H.ksimple_eff hk hv hC hcost hadvance (n - S)
    (by rw [hlen]; omega), decide_eq_true_iff]
  have hmain := answerH_iff_occursAt (w := w) (S := S) (k := k)
    (p₁ := effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (r := effReach p₁ r)
    H.ksimple_eff hk hv huv h2S hn
  rw [online_answer_correct (T := w.drop S) H.ksimple_eff hk hv (n - S)
    (by rw [hlen]; omega), decide_eq_true_iff] at hmain
  exact hmain

end Stage

end StageMatcherTapes
end PalPeg
