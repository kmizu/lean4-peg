import PalPeg.StageMatcherProg

/-!
# 走査段（matcher フェーズ）の **有限制御版** 固定動作数ラウンド機械 (`StageMatcherTapesX`)

`PalPeg.StageMatcherTapes` の計量式機械 `SMachine` / `sround` は、1 歩として
`VerifierFeed.vscanOne''`（＝ 動作列 `GSVTapes.vprogram'`）を走らせる。`vprogram'` は
**有限制御で実現できる形になっていない**（ずらし枝がオラクル的な巻き戻しを含む）。
有限制御で実現できる一歩の動作列は `GSVTapes.vprogramX`
（`PalPeg.GSVerifierFused`, 実現は `vencodes_stepX`）であり、その償却定数は
`StageMatcherProg.xA k = 9k+14`, `StageMatcherProg.xB = 16` である。

本ファイルは、その `vprogramX` 版の段ライフサイクルを組み立てる。

## 設計：一歩をインタフェース `XStep` に抽象化する

`VerifierFeed` には **供給つきの `vprogramX` 一歩**（`vscanOne''` の X 版）がまだ無い。
そこで一歩を

* `run`  … 供給（`vfillIf1'`）こみの一歩、
* `fc`   … その 1 歩のテープ動作数の上界、
* `ghost` … ゴースト（走査状態＋`checked`）は `vStep`、
* `cost`  … `fc` による動作数の上界、
* `inner` … `VFeedInv'` と `Ok2` の保存

の 5 つ組 `XStep` として抽象化し、段の機械・不変条件・動作数会計をすべてその上で
組み立てる。インタフェースは空ではない：**`vprogram'` 版の一歩 `fstep` は
`fc := fcost` で `XStep` の実例になる**（`fedStep`）。求める X 版は
`fc := fcostX = |vprogramX …| + 103` を満たす実例であり、そこだけが
`VerifierFeed` 側に残る仕事である。

## 定数

* `A := StageMatcherProg.xA k = 9k+14`, `B' := StageMatcherProg.xB = 16`
* 1 ラウンドの計量動作数 `B := StageMatcherProg.xRate k = mRate (xA k) xB k = (k+1)(9k+30)`
* 1 ラウンドのテープ動作予算 `roundBudgetX U k = 85 + U * xRate k`
  （`85 = 52`（到着）`+ 33`（`Txt2` 頭出し））

## `hcost`（`Metered` の義務）について

`Metered.metered_answer_correct'` は `cst st ≤ (A+B')·ΔΦ` を **走査状態だけの関数**
として要求する。`vprogramX` の一歩の費用は `vprogramX_cost` により

  `|vprogramX| ≤ (9k+14)·ΔΦ + 12 + 2·checked`

であり、`2·checked` の項は走査状態だけでは抑えられない（周期ずらし枝では
`checked ≤ 2q` に対し `ΔΦ = k·p₁` しか無く、`q ≤ r` は `k·p₁` に比べて
いくらでも大きい）。したがって `hcost` を満たすには **`Ψ = 2·checked` を含む
償却形**（`vprogramX_amortized`）を使うほかない。本ファイルはその形の義務
`XAmortized` を定義し、`uceil` へ持ち上げた版 `fcostX_amortized` を与える。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace StageMatcherTapesX

open PalPeg.VerifierFeed
open PalPeg.StageMatcherTapes
open PalPeg.StageMatcherProg

variable {sc : ℕ}

/-! ## 1. 一歩のインタフェース -/

/-- **供給つき一歩のインタフェース**。`StageMatcherTapes.fstep` の抽象化。 -/
structure XStep (sc : ℕ) (blank startSym endSym mark : Fin sc)
    (u v Text : List (Fin sc)) (k p₁ r : ℕ) where
  /-- 一歩（ラウンド番号 `n` の供給こみ）。 -/
  run : ℕ → VMachine' sc → VMachine' sc
  /-- 一歩のテープ動作数の上界。 -/
  fc : ℕ → VMachine' sc → ℕ
  /-- ゴーストはちょうど `vStep`。 -/
  ghost : ∀ (n : ℕ) (M : VMachine' sc), (run n M).z = vStep u v k p₁ r Text M.z
  /-- 動作数は `fc` で抑えられる。 -/
  cost : ∀ (n : ℕ) (M : VMachine' sc), (run n M).cost ≤ M.cost + fc n M
  /-- 供給つきの不変条件 `VFeedInv'` と `Ok2` を保つ。 -/
  inner : ∀ (n : ℕ) (M : VMachine' sc), n ≤ Text.length →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n M →
      Ok2 n M (M.z.1.pos - u.length + M.z.2) →
      Enabled v n M.z.1 →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n (run n M) ∧
        Ok2 n (run n M) ((run n M).z.1.pos - u.length + (run n M).z.2)

section Instances

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}

/-- **インタフェースは空ではない**：`vprogram'` 版の一歩 `StageMatcherTapes.fstep` は
`fc := StageMatcherTapes.fcost` で `XStep` の実例になる。 -/
def fedStep (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text) :
    XStep sc blank startSym endSym mark u v Text k p₁ r where
  run n M := fstep blank endSym mark u v k p₁ r n Text M
  fc n M := fcost blank endSym mark k n M
  ghost n M := fstep_z blank endSym mark u v k p₁ r n Text M
  cost n M := fstep_cost blank endSym mark u v k p₁ r n Text M
  inner n M hn hF hok he := by
    have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hmb hn hF
    have hfok : Ok2 n (vfillIf1' blank mark n M)
        ((vfillIf1' blank mark n M).z.1.pos - u.length
          + (vfillIf1' blank mark n M).z.2) := by
      unfold vfillIf1'
      split_ifs with hc
      · exact hok
      · exact hok
    exact vscanOne''_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
      (Text := Text) hk hmb hv hend hendu hb hmT hn (vfillIf1'_ready hF he) hfF hfok

/-- **X 版の一歩の動作数**：有限制御の動作列 `vprogramX` そのもの ＋ 供給と適用の定数
（`103 = 33`（`Txt2` 供給）`+ 70`）。 -/
def fcostX (blank endSym mark : Fin sc) (k n : ℕ) (M : VMachine' sc) : ℕ :=
  (GSVTapes.vprogramX blank endSym mark k (vfillIf1' blank mark n M).vt).length + 103

/-- **求める X 版の一歩**：`fc = fcostX` を満たす `XStep`。 -/
def IsX (X : XStep sc blank startSym endSym mark u v Text k p₁ r) : Prop :=
  ∀ (n : ℕ) (M : VMachine' sc), X.fc n M = fcostX blank endSym mark k n M

end Instances

/-! ## 2. 状態と 1 計量動作 -/

/-- 状態空間は `StageMatcherTapes.SMachine` と同一（テープ 12 本 ＋ 残り計量動作数）。
違うのは 1 歩に走る動作列（`vprogramX`）とその費用だけである。 -/
abbrev SMachineX (sc : ℕ) := SMachine sc

section Acts

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  (X : XStep sc blank startSym endSym mark u v Text k p₁ r) (cst : ScanState → ℕ)

/-- **1 計量動作**（`StageMatcherTapes.sact` の X 版）。 -/
def sactX (n : ℕ) (S : SMachineX sc) : SMachineX sc :=
  if S.rem = 0 then
    (if Enabled v n S.M.z.1 then
        (if cst S.M.z.1 ≤ 1 then ⟨X.run n S.M, 0⟩ else ⟨S.M, cst S.M.z.1 - 1⟩)
      else S)
  else if S.rem = 1 then ⟨X.run n S.M, 0⟩
  else ⟨S.M, S.rem - 1⟩

/-- `j` 個の計量動作。 -/
def sactsX (n : ℕ) : ℕ → SMachineX sc → SMachineX sc
  | 0, S => S
  | j + 1, S => sactsX n j (sactX X cst n S)

/-- **1 ラウンド**（`StageMatcherTapes.sround` の X 版）：到着（両待ち行列）→
`Txt2` の頭出し供給 → ちょうど `xRate k` 計量動作。 -/
def sroundX (n : ℕ) (a : Fin sc) (S : SMachineX sc) : SMachineX sc :=
  sactsX X cst (n + 1) (xRate k)
    ⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩

/-- **段の走行**：起動フェーズ後の絶対ラウンド `s, s+1, …` を回す。 -/
def stageX (s : ℕ) : ℕ → SMachineX sc → SMachineX sc
  | 0, S => S
  | n + 1, S =>
      sroundX X cst (s + n) (Text.getD (s + n) blank) (stageX s n S)

end Acts

/-- ラウンドあたりのテープ動作予算：`85 + U * xRate k`。 -/
def roundBudgetX (U k : ℕ) : ℕ := 85 + U * xRate k

theorem roundBudgetX_eq (U k : ℕ) : roundBudgetX U k = roundBudget U (xA k) xB k := rfl

/-! ## 3. ゴーストの一致 -/

section Ghost

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {X : XStep sc blank startSym endSym mark u v Text k p₁ r} {cst : ScanState → ℕ}

theorem run_st (n : ℕ) (M : VMachine' sc) :
    (X.run n M).z.1 = scanStep v k p₁ r Text M.z.1 := by
  rw [X.ghost, vStep_fst]

theorem sactX_ghost (n : ℕ) (S : SMachineX sc) :
    gm (sactX X cst n S) = mact v k p₁ r Text cst n (gm S) := by
  unfold sactX mact gm
  simp only [gm_st, gm_rem]
  split_ifs <;> simp [run_st]

theorem sactsX_ghost (n : ℕ) :
    ∀ (j : ℕ) (S : SMachineX sc),
      gm (sactsX X cst n j S) = macts v k p₁ r Text cst n j (gm S) := by
  intro j
  induction j with
  | zero => intro S; rfl
  | succ j ih => intro S; rw [sactsX, macts, ih, sactX_ghost]

theorem sroundX_ghost (n : ℕ) (a : Fin sc) (S : SMachineX sc) :
    gm (sroundX X cst n a S)
      = macts v k p₁ r Text cst (n + 1) (mRate (xA k) xB k) (gm S) := by
  rw [sroundX, sactsX_ghost]
  congr 1
  show (⟨(vfillHead2 blank mark (varrive' blank mark a S.M)).z.1, S.rem⟩ : MState) = gm S
  rw [vfillHead2_z, varrive'_z]
  rfl

/-- **`stageX_round_spec`**：ラウンド `n` 後のゴーストは `Metered.metered` の絶対ラウンド
`|u| + n` の状態にちょうど一致する（定数は `A := xA k`, `B' := xB`）。 -/
theorem stageX_round_spec (hv : 0 < v.length) {S₀ : SMachineX sc}
    (h0 : gm S₀ = metered u v k p₁ r Text cst (xA k) xB u.length) :
    ∀ n, gm (stageX X cst u.length n S₀)
      = metered u v k p₁ r Text cst (xA k) xB (u.length + n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have e : u.length + (n + 1) = (u.length + n) + 1 := by omega
    rw [stageX, sroundX_ghost, ih, e, metered]

/-- 起動状態（`rem = 0`、走査状態 `⟨|u|, 0⟩`）は `metered … |u|` に一致する。 -/
theorem gmX_start (hv : 0 < v.length) {S₀ : SMachineX sc}
    (hz : S₀.M.z = ((⟨u.length, 0⟩ : ScanState), 0)) (hr : S₀.rem = 0) :
    gm S₀ = metered u v k p₁ r Text cst (xA k) xB u.length :=
  gm_start (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (Text := Text)
    (cst := cst) (A := xA k) (B' := xB) hv hz hr

end Ghost

/-! ## 4. 不変条件の保存 -/

section Inv

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {X : XStep sc blank startSym endSym mark u v Text k p₁ r} {cst : ScanState → ℕ}

theorem sactX_inner {n : ℕ} (hn : n ≤ Text.length) {S : SMachineX sc}
    (h : SInner blank startSym endSym mark u v Text k p₁ r n S) :
    SInner blank startSym endSym mark u v Text k p₁ r n (sactX X cst n S) := by
  obtain ⟨hF, hok, hE⟩ := h
  have hstep : ∀ _he : Enabled v n S.M.z.1,
      SInner blank startSym endSym mark u v Text k p₁ r n
        (⟨X.run n S.M, 0⟩ : SMachineX sc) := by
    intro he
    obtain ⟨s1, s2⟩ := X.inner n S.M hn hF hok he
    exact ⟨s1, s2, by simp⟩
  unfold sactX
  split_ifs with h0 he hc h1
  · exact hstep he
  · exact ⟨hF, hok, fun _ => he⟩
  · exact ⟨hF, hok, hE⟩
  · exact hstep (hE h0)
  · exact ⟨hF, hok, fun _ => hE h0⟩

theorem sactsX_inner {n : ℕ} (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (S : SMachineX sc),
      SInner blank startSym endSym mark u v Text k p₁ r n S →
      SInner blank startSym endSym mark u v Text k p₁ r n (sactsX X cst n j S) := by
  intro j
  induction j with
  | zero => intro S h; exact h
  | succ j ih => intro S h; exact ih _ (sactX_inner hn h)

variable (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text)

include hmb hb hmT in
/-- **1 ラウンドの不変条件**：`VFeedInv'` はラウンド境界で保たれる。 -/
theorem sroundX_bnd {n : ℕ} {a : Fin sc} (hn : n < Text.length) (ha : Text[n]? = some a)
    {S : SMachineX sc} (h : SBnd blank startSym endSym mark u v Text k p₁ r n S) :
    SBnd blank startSym endSym mark u v Text k p₁ r (n + 1) (sroundX X cst n a S) := by
  obtain ⟨hF, hE⟩ := h
  have hA := varrive'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hmb hn ha hF
  obtain ⟨hH, hok⟩ := vfillHead2_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
    hmb hb hmT (by omega : n + 1 ≤ Text.length) hA
  have hstart : SInner blank startSym endSym mark u v Text k p₁ r (n + 1)
      (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ : SMachineX sc) := by
    refine ⟨hH, hok, ?_⟩
    intro hr
    have hz : (vfillHead2 blank mark (varrive' blank mark a S.M)).z = S.M.z := by
      rw [vfillHead2_z, varrive'_z]
    rw [show (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ :
      SMachineX sc).M.z.1 = S.M.z.1 from by rw [hz]]
    exact (hE hr).mono (Nat.le_succ n)
  have hres := sactsX_inner (X := X) (cst := cst) (by omega : n + 1 ≤ Text.length)
    (xRate k) _ hstart
  exact ⟨hres.1, hres.2.2⟩

include hmb hb hmT in
/-- **段の走行の不変条件**：各ラウンド境界で `VFeedInv'` が成り立つ。 -/
theorem stageX_bnd :
    ∀ (n : ℕ) (S : SMachineX sc), u.length + n ≤ Text.length →
      SBnd blank startSym endSym mark u v Text k p₁ r u.length S →
      SBnd blank startSym endSym mark u v Text k p₁ r (u.length + n)
        (stageX X cst u.length n S) := by
  intro n
  induction n with
  | zero => intro S _ h; exact h
  | succ n ih =>
    intro S hle h
    have e : u.length + (n + 1) = (u.length + n) + 1 := by omega
    rw [e]
    exact sroundX_bnd hmb hb hmT (by omega : u.length + n < Text.length)
      (TextFeed.getD_eq (by omega)) (ih S (by omega) h)

end Inv

/-! ## 5. 動作数（予算）の会計 -/

section Cost

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {X : XStep sc blank startSym endSym mark u v Text k p₁ r} {cst : ScanState → ℕ}
  {U : ℕ}

/-- 抽象コスト関数がインタフェースの 1 歩コストの計量値であること
（`StageMatcherTapes.CostSpec` の X 版）。 -/
def CostSpecX (X : XStep sc blank startSym endSym mark u v Text k p₁ r) (U : ℕ)
    (cst : ScanState → ℕ) : Prop :=
  ∀ (n : ℕ) (M : VMachine' sc), cst M.z.1 = uceil U (X.fc n M)

theorem sactX_cost (hU : 0 < U) (hcst : CostSpecX X U cst) (n : ℕ) (S : SMachineX sc) :
    (sactX X cst n S).M.cost + U * spend cst (sactX X cst n S)
      ≤ S.M.cost + U * spend cst S + U := by
  have hfc : X.fc n S.M ≤ U * cst S.M.z.1 := by
    rw [hcst n S.M]; exact le_mul_uceil hU _
  have hstep := X.cost n S.M
  unfold sactX
  split_ifs with h0 he hc h1
  · have e1 : spend cst (⟨X.run n S.M, 0⟩ : SMachineX sc) = 0 := by simp [spend]
    have e2 : spend cst S = 0 := by simp [spend, h0]
    have hle : U * cst S.M.z.1 ≤ U * 1 := Nat.mul_le_mul_left U hc
    simp only [SMachine.mk_M, e1, e2, Nat.mul_one] at *
    omega
  · have e1 : spend cst (⟨S.M, cst S.M.z.1 - 1⟩ : SMachineX sc) = 1 := by
      have hne : cst S.M.z.1 - 1 ≠ 0 := by omega
      simp only [spend, SMachine.mk_M, SMachine.mk_rem, if_neg hne]
      omega
    have e2 : spend cst S = 0 := by simp [spend, h0]
    simp only [SMachine.mk_M, e1, e2, Nat.mul_one]
    omega
  · omega
  · have e1 : spend cst (⟨X.run n S.M, 0⟩ : SMachineX sc) = 0 := by simp [spend]
    have e2 : spend cst S = cst S.M.z.1 - 1 := by
      simp only [spend, if_neg h0, h1]
      norm_num
    have h3 : cst S.M.z.1 ≤ (cst S.M.z.1 - 1) + 1 := by omega
    have h4 : U * cst S.M.z.1 ≤ U * ((cst S.M.z.1 - 1) + 1) := Nat.mul_le_mul_left U h3
    have h5 : U * ((cst S.M.z.1 - 1) + 1) = U * (cst S.M.z.1 - 1) + U := by ring
    simp only [SMachine.mk_M, e1, e2]
    omega
  · have hne : S.rem - 1 ≠ 0 := by omega
    have e1 : spend cst (⟨S.M, S.rem - 1⟩ : SMachineX sc) = cst S.M.z.1 - (S.rem - 1) := by
      simp only [spend, SMachine.mk_M, SMachine.mk_rem, if_neg hne]
    have e2 : spend cst S = cst S.M.z.1 - S.rem := by simp only [spend, if_neg h0]
    have h2 : cst S.M.z.1 - (S.rem - 1) ≤ (cst S.M.z.1 - S.rem) + 1 := by omega
    have h3 : U * (cst S.M.z.1 - (S.rem - 1)) ≤ U * ((cst S.M.z.1 - S.rem) + 1) :=
      Nat.mul_le_mul_left U h2
    have h4 : U * ((cst S.M.z.1 - S.rem) + 1) = U * (cst S.M.z.1 - S.rem) + U := by ring
    simp only [SMachine.mk_M, e1, e2]
    omega

theorem sactsX_cost (hU : 0 < U) (hcst : CostSpecX X U cst) (n : ℕ) :
    ∀ (j : ℕ) (S : SMachineX sc),
      (sactsX X cst n j S).M.cost + U * spend cst (sactsX X cst n j S)
        ≤ S.M.cost + U * spend cst S + U * j := by
  intro j
  induction j with
  | zero => intro S; simp [sactsX]
  | succ j ih =>
    intro S
    have h1 := ih (sactX X cst n S)
    have h2 := sactX_cost hU hcst n S
    have e : U * (j + 1) = U * j + U := by ring
    rw [sactsX]
    omega

/-- **1 ラウンドの動作数**：ちょうど `85 + U * xRate k` テープ動作の予算に収まる。 -/
theorem sroundX_cost (hU : 0 < U) (hcst : CostSpecX X U cst) (n : ℕ) (a : Fin sc)
    (S : SMachineX sc) :
    (sroundX X cst n a S).M.cost + U * spend cst (sroundX X cst n a S)
      ≤ S.M.cost + U * spend cst S + roundBudgetX U k := by
  have hAc := varrive'_cost blank mark a S.M
  have hHc := vfillHead2_cost blank mark (varrive' blank mark a S.M)
  have hsp : spend cst (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ :
      SMachineX sc) = spend cst S := by
    unfold spend
    have hz : (vfillHead2 blank mark (varrive' blank mark a S.M)).z = S.M.z := by
      rw [vfillHead2_z, varrive'_z]
    simp only [hz]
  have h1 := sactsX_cost (X := X) hU hcst (n + 1) (xRate k)
    (⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ : SMachineX sc)
  rw [hsp] at h1
  simp only [SMachine.mk_M] at h1
  have hdef : sroundX X cst n a S
      = sactsX X cst (n + 1) (xRate k)
        ⟨vfillHead2 blank mark (varrive' blank mark a S.M), S.rem⟩ := rfl
  rw [hdef, roundBudgetX]
  omega

/-- **段全体の動作数**：`n` ラウンドで `n * (85 + U * xRate k)` テープ動作以内。 -/
theorem stageX_cost' (hU : 0 < U) (hcst : CostSpecX X U cst) :
    ∀ (n : ℕ) (S : SMachineX sc),
      (stageX X cst u.length n S).M.cost + U * spend cst (stageX X cst u.length n S)
        ≤ S.M.cost + U * spend cst S + n * roundBudgetX U k := by
  intro n
  induction n with
  | zero => intro S; simp [stageX]
  | succ n ih =>
    intro S
    have h1 := ih S
    have h2 := sroundX_cost (X := X) hU hcst (u.length + n)
      (Text.getD (u.length + n) blank) (stageX X cst u.length n S)
    have e : (n + 1) * roundBudgetX U k = n * roundBudgetX U k + roundBudgetX U k := by ring
    have hdef : stageX X cst u.length (n + 1) S
        = sroundX X cst (u.length + n) (Text.getD (u.length + n) blank)
          (stageX X cst u.length n S) := rfl
    rw [hdef]
    omega

theorem stageX_cost (hU : 0 < U) (hcst : CostSpecX X U cst) (n : ℕ) (S : SMachineX sc)
    (h0 : S.rem = 0) :
    (stageX X cst u.length n S).M.cost ≤ S.M.cost + n * roundBudgetX U k := by
  have h := stageX_cost' (X := X) hU hcst n S
  have e : spend cst S = 0 := by simp [spend, h0]
  rw [e] at h
  omega

end Cost

/-! ## 6. 初期状態 -/

section Init

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {cst : ScanState → ℕ}

/-- **`stageX_init`**：`StageMatcherTapes.stage_init` の `A := xA k`, `B' := xB` 版。 -/
theorem stageX_init (hmb : mark ≠ blank) (hv : 0 < v.length)
    (hlen : u.length ≤ Text.length) :
    SBnd blank startSym endSym mark u v Text k p₁ r u.length
        (initSM blank startSym endSym mark u v Text k p₁ r) ∧
      gm (initSM blank startSym endSym mark u v Text k p₁ r)
        = metered u v k p₁ r Text cst (xA k) xB u.length ∧
      (initSM blank startSym endSym mark u v Text k p₁ r).M.cost ≤ 86 * u.length :=
  stage_init (cst := cst) (A := xA k) (B' := xB) hmb hv hlen

end Init

/-! ## 7. `hcost` の義務と `Ψ` 償却 -/

section Amortized

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}

/-- **`Ψ` 込みの償却義務**：`vprogramX_amortized` を計量値へ持ち上げた形。
`Metered` の `hcost`（`cst st ≤ (A+B')·ΔΦ`）はこの形に置き換えられねばならない。 -/
def XAmortized (U : ℕ) (blank endSym mark : Fin sc) (u v Text : List (Fin sc))
    (k p₁ r : ℕ) : Prop :=
  ∀ (n : ℕ) (M : VMachine' sc),
    uceil U (fcostX blank endSym mark k n M) + 2 * (vStep u v k p₁ r Text M.z).2
      ≤ xA k * (Phi k (vStep u v k p₁ r Text M.z).1 - Phi k M.z.1) + (xB + 103) + 2 * M.z.2

/-- **`XAmortized` の履行**：`vprogramX_amortized`（`Φ` と `Ψ = 2·checked` の償却）から。
供給後のテープが走査状態 `M.z` を符号化していること（`VEncodes'`）が仮定である。 -/
theorem fcostX_amortized {U : ℕ} (hU : 0 < U) (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    {n : ℕ} {M : VMachine' sc}
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r
      (vfillIf1' blank mark n M).vt M.z)
    (hq : M.z.1.q ≤ v.length) :
    uceil U (fcostX blank endSym mark k n M) + 2 * (vStep u v k p₁ r Text M.z).2
      ≤ xA k * (Phi k (vStep u v k p₁ r Text M.z).1 - Phi k M.z.1) + (xB + 103)
        + 2 * M.z.2 := by
  have h1 : uceil U (fcostX blank endSym mark k n M) ≤ fcostX blank endSym mark k n M :=
    uceil_le_self hU _
  have h2 := vprogramX_amortized (u := u) (v := v) (Text := Text) (p₁ := p₁) (r := r)
    hk hne hend hE hq
  simp only [fcostX] at h1 ⊢
  omega

/-- **`hadvance` の履行**（`StageMatcherProg.xcst_advance` の `fcostX` 版）。
比較枝の動作数は `≤ 12` なので、計量単位を `U ≥ 12 + 103 = 115` に取れば
前進ステップの計量費用は `1`（＝ 駐機しない）。 -/
theorem fcostX_advance {U : ℕ} (hU : 115 ≤ U) (hend : endSym ∉ v) {n : ℕ}
    {M : VMachine' sc} {z : VState}
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v Text k p₁ r
      (vfillIf1' blank mark n M).vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    uceil U (fcostX blank endSym mark k n M) ≤ 1 := by
  have h := vprogramX_adv_le (u := u) (v := v) (Text := Text) (p₁ := p₁) (r := r)
    hend hE hq hadv
  refine uceil_le_one (by omega) ?_
  simp only [fcostX]
  omega

end Amortized

/-! ## 8. 段の答え -/

section Answer

variable {α : Type} [DecidableEq α] {u v Text : List α} {k p₁ r : ℕ} {cst : ScanState → ℕ}

/-- **`stageX_answer_read`**：`A := xA k`, `B' := xB` での `Metered` の答えの正しさ。 -/
theorem stageX_answer_read (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (hcost : ∀ st, cst st ≤ (xA k + xB)
      * (Phi k (scanStep v k p₁ r Text st) - Phi k st))
    (hadvance : ∀ st, st.q ≠ v.length → Text[st.pos + st.q]? = v[st.q]? → cst st ≤ 1)
    (n : ℕ) (hn : (u ++ v).length ≤ n) :
    manswer u v k p₁ r Text cst (xA k) xB n
      = decide (OccAt (u ++ v) Text (n - (u ++ v).length)) :=
  stage_answer_read hK hk hv (by unfold xB; omega) hcost hadvance n hn

end Answer

/-! ## 9. 公理の確認 -/

#print axioms fedStep
#print axioms sactX_ghost
#print axioms sroundX_ghost
#print axioms stageX_round_spec
#print axioms gmX_start
#print axioms sactX_inner
#print axioms sroundX_bnd
#print axioms stageX_bnd
#print axioms sactX_cost
#print axioms sroundX_cost
#print axioms stageX_cost
#print axioms stageX_init
#print axioms fcostX_amortized
#print axioms fcostX_advance
#print axioms stageX_answer_read

end StageMatcherTapesX
end PalPeg
