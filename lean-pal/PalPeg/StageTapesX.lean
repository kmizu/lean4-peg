import PalPeg.StageTapes
import PalPeg.StageMatcherTapesX

/-!
# 段のライフサイクルの **有限制御版定数** (`StageTapesX`)

`PalPeg.StageTapes.stage_tapes_spec'` は、照合器の 1 歩の費用関数 `cst` と償却定数
`A`, `B'` に対して **完全にパラメトリック** である（使うのは `hC : 0 < A + B'`,
`hcost`, `hadvance` の 3 つだけで、`A`, `B'` 自体は `sround` のラウンド速度
`mRate A B' k` を通してしか効かない）。したがって、有限制御の一歩 `GSVTapes.vprogramX`
の償却定数

* `A  := StageMatcherProg.VerifierFeedX.xfA k = 9k + 14`
* `B' := StageMatcherProg.VerifierFeedX.xfB = 16`

をそのまま代入でき、1 ラウンドの計量動作数は
`mRate (VerifierFeedX.xfA k) VerifierFeedX.xfB k = StageMatcherProg.xRate k = (k+1)(9k+30)`
（`k = 8` なら `918`）、1 ラウンドのテープ動作予算は
`StageMatcherTapesX.roundBudgetX U k = 85 + U * xRate k` になる。本ファイルは
その代入版 `stage_tapes_specX` と、1 ラウンドの動作数上界 `CstageX` を与える。

## `ststate` の `sm` フェーズが走らせるプログラム（重要）

`StageTapes.ststate` の `sm` 成分は、絶対ラウンド `n > S + |u|` において

  `StageTapes.stround … = StageMatcherTapes.sround …`
  `→ StageMatcherTapes.sact → StageMatcherTapes.fstep`
  `= VerifierFeed.vscanOne'' … (VerifierFeed.vfillIf1' …)`

を走らせる。`vscanOne''` の検証器側は `VerifierFeed.vExtFed` ＋ `vscanApply` であり、
実際にテープへ適用される動作列は **`GSVTapes.vprogram'`**（`GSTapes.program'` ＋
`vExtActs'`）であって `GSVTapes.vprogramX` ではない。すなわち

* **本ファイルの `stage_tapes_specX` は「定数 `(A,B') = (VerifierFeedX.xfA k, VerifierFeedX.xfB)` での段の仕様」であり、
  段が実際に実行するプログラムは依然として `vprogram'` である。**
* `vprogramX` を実際に走らせる段を得るには、`VerifierFeed` に **供給つきの `vprogramX`
  一歩**（`vscanOne''` の X 版）が必要で、それが用意されれば
  `PalPeg.StageMatcherTapesX.XStep`（`run` / `fc = fcostX` / `ghost` / `cost` / `inner`）の
  実例が得られ、`StageMatcherTapesX.sroundX` / `stageX` がそのまま段の `sm` フェーズに
  差し替えられる（ゴースト `gm` と状態空間 `SMachine` は同一なので、`stround` の他の
  成分・不変条件・答えの読み出しは一切変わらない）。

## `hcost` について

`hcost : ∀ st, cst st ≤ (A + B') * ΔΦ` は **走査状態だけの関数**としての要求である。
`vprogramX` の一歩の費用は `StageMatcherProg.vprogramX_cost` により
`≤ (9k+14)·ΔΦ + 12 + 2·checked` であり、`2·checked` は走査状態だけでは抑えられない
（周期ずらし枝では `ΔΦ = k·p₁` に対し `checked ≤ 2q`、`q ≤ r` は `k·p₁` より
いくらでも大きくなりうる）。よって `hcost` をこの形のまま履行することはできず、
`Ψ = 2·checked` を含む償却形（`StageMatcherTapesX.XAmortized` /
`StageMatcherTapesX.fcostX_amortized`）を `Metered` 側で受け取れるように
一般化する必要がある。本ファイルはその一般化は行わず、`hcost` を仮定のまま
持ち上げる（`stage_tapes_spec'` と同じ形）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace StageTapesX

open PalPeg.PatternTapes
open PalPeg.MiddleTapes
open PalPeg.VerifierFeed
open PalPeg.StageMatcherTapes
open PalPeg.StageMatcherProg
open PalPeg.VerifierFeedX
open PalPeg.StageMatcherTapesX
open PalPeg.StageTapes

variable {sc : ℕ}

/-! ## 1. 1 ラウンドの動作数 -/

section Cost

variable {blank startSym endSym mark forb : Fin sc}

/-- **X 版の 1 ラウンドの動作数上界**：
`CmT' D + rateP Pre + 160 + 86 + (85 + U * xRate k)`。 -/
def CstageX (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (U k : ℕ) : ℕ :=
  Cstage D Pre U (VerifierFeedX.xfA k) VerifierFeedX.xfB k

theorem CstageX_eq (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (U k : ℕ) :
    CstageX D Pre U k = CmT' D + rateP Pre + rateS + 86 + roundBudgetX U k := rfl

/-- **`stage_round_actionsX`**：段の 1 ラウンドの動作数は `CstageX` 以下。 -/
theorem stage_round_actionsX (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (u : List (Fin sc)) (U k S : ℕ)
    (n : ℕ) (St : StageT sc) :
    stcost D Pre u U (VerifierFeedX.xfA k) VerifierFeedX.xfB k S n St ≤ CstageX D Pre U k :=
  stage_round_actions D Pre u U (VerifierFeedX.xfA k) VerifierFeedX.xfB k S n St

end Cost

/-! ## 2. 主定理 -/

section Answer

variable {blank startSym endSym mark : Fin sc}

/-- **`stage_tapes_specX`**：`StageTapes.stage_tapes_spec'` の
`A := StageMatcherProg.VerifierFeedX.xfA k`, `B' := StageMatcherProg.VerifierFeedX.xfB` 版（結論は同一）。
1 ラウンドの計量動作数は `StageMatcherProg.xRate k`、1 ラウンドの動作数上界は
`CstageX D Pre U k`（`stage_round_actionsX`）。仮定 `hC : 0 < A + B'` は
`VerifierFeedX.xfB = 16` から自動的に消える。 -/
theorem stage_tapes_specX
    {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark endSym}
    {leftSym one zero : Fin sc}
    {w : List (Fin sc)} {S k s p₁ r : ℕ} {cst : ScanState → ℕ} {init : StageT sc}
    (hmb : mark ≠ blank) (hS : 8 ≤ S) (hq : 4 * (S / 4) = S)
    (hres : Pre.res w (S / 2)
      = (s, effPeriod ((w.take (S / 2)).reverse.drop s) p₁, effReach p₁ r))
    (hkp : k * effPeriod ((w.take (S / 2)).reverse.drop s) p₁ ≤ 5 * S)
    (hpinit : PrepPre blank mark leftSym (S / 2) w (w.drop S) init.pg.ts)
    (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hcost : ∀ st, cst st ≤ (VerifierFeedX.xfA k + VerifierFeedX.xfB)
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hev : 2 * (S / 2) = S)
    (hminit : ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m init.md)
    {n : ℕ} (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hw : n ≤ w.length) :
    stAnswerBit ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s)
        (w.drop S) k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r)
        cst (VerifierFeedX.xfA k) VerifierFeedX.xfB S one n
        (ststate D Pre leftSym one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst
          (VerifierFeedX.xfA k) VerifierFeedX.xfB S w init (n - 1))
        (ststate D Pre leftSym one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst
          (VerifierFeedX.xfA k) VerifierFeedX.xfB S w init n) = true
      ↔ (occursAt (w.take (S / 2)).reverse (w.take n)
          ∧ IsPal ((w.drop (S / 2)).take (n - S))) :=
  stage_tapes_spec' (hmb := hmb) (hS := hS) (hq := hq) (hres := hres) (hkp := hkp)
    (hpinit := hpinit) (hk := hk) (hs := hs) (H := H) (hC := by unfold VerifierFeedX.xfB; omega)
    (hcost := hcost) (hadvance := hadvance) (hne := hne) (hleft := hleft) (hend := hend)
    (hev := hev) (hminit := hminit) (h1 := h1) (h2 := h2) (hw := hw)

end Answer

/-! ## 3. 公理の確認 -/

#print axioms CstageX_eq
#print axioms stage_round_actionsX
#print axioms stage_tapes_specX

end StageTapesX
end PalPeg
