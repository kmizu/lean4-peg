import PalPeg.StageTapes
import PalPeg.GSVerifierTapesZ

/-!
# 段のライフサイクルの **ジグザグ検証器版定数** (`StageTapesZ`)

`PalPeg.StageTapes.stage_tapes_spec'` は、照合器の 1 歩の費用関数 `cst` と償却定数
`A`, `B'` に対して **完全にパラメトリック** である（使うのは `hC : 0 < A + B'`,
`hcost`, `hadvance` の 3 つだけ）。本ファイルはそこへ、ジグザグ一歩
`GSVTapesZ.vprogramZ'` の**点ごとの**定数

* `A  := GSVTapesZ.zA k = 9k + 14`
* `B' := GSVTapesZ.zB = 16`

を代入した版 `stage_tapes_specZ` と、1 ラウンドの動作数上界 `CstageZ` を与える。
1 ラウンドの計量動作数は `mRate (9k+14) 16 k = (k+1)(9k+30)`（`k = 8` なら `918`）、
1 ラウンドのテープ動作予算は `StageMatcherTapes.roundBudget U (9k+14) 16 k
= 85 + U * mRate (9k+14) 16 k` になる。

## `X` 版との決定的な違い

`PalPeg.StageTapesX` の注意書きにあるとおり、`vprogramX` の一歩の費用は
`StageMatcherProg.vprogramX_cost` により `≤ (9k+14)·ΔΦ + 12 + 2·checked` であり、
`2·checked` は走査状態だけでは抑えられない（`PalPeg.PointwiseGap.rewind_not_pointwise`）。
すなわち `hcost : ∀ st, cst st ≤ (A + B') * ΔΦ` を `vprogramX` の実費用で履行することは
**できない**。

ジグザグ版ではこの項が消える：`GSVTapesZ.vprogramZ'_cost` は

  `|vprogramZ'| ≤ (9k+14)·ΔΦ + 16`

という **点ごとの** 上界であり、`Ψ = 2·checked` のような償却項を含まない
（ずらしのとき `U` を巻き戻さないため）。したがって `hcost` を
`cst := fun st => |vprogramZ'|` の形で**構造的な仮定だけから**履行できる道が開ける。
本ファイルは `stage_tapes_spec'` と同じく `cst` をパラメータのまま持ち上げ、
`hcost` / `hadvance` を仮定として残す（`Metered` は**一切変更しない**）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace StageTapesZ

open PalPeg.PatternTapes
open PalPeg.MiddleTapes
open PalPeg.VerifierFeed
open PalPeg.StageMatcherTapes
open PalPeg.StageTapes
open PalPeg.GSVTapesZ

variable {sc : ℕ}

/-! ## 1. 償却定数 -/

/-- ジグザグ版の償却係数 `A_Z = 9k + 14`。 -/
abbrev zfA (k : ℕ) : ℕ := GSVTapesZ.zA k

/-- ジグザグ版の償却定数 `B_Z = 16`。 -/
abbrev zfB : ℕ := GSVTapesZ.zB

example : zfA 8 = 86 := by norm_num [zfA, GSVTapesZ.zA]
example : zfB = 16 := rfl

/-- 1 ラウンドの計量動作数：`mRate (9k+14) 16 k = (k+1)(9k+30)`。 -/
def zRate (k : ℕ) : ℕ := PalPeg.mRate (zfA k) zfB k

example : zRate 8 = 918 := by norm_num [zRate, PalPeg.mRate, zfA, GSVTapesZ.zA, GSVTapesZ.zB]

/-! ## 2. 1 ラウンドの動作数 -/

section Cost

variable {blank startSym endSym mark forb leftSym : Fin sc}

/-- **ジグザグ版の 1 ラウンドの動作数上界**：
`CmT' D + rateP Pre + rateS + 86 + roundBudget U (9k+14) 16 k`。 -/
def CstageZ (D : DecompOnTapes sc blank startSym endSym mark leftSym)
    (Pre : PrepOnTapes sc blank mark forb) (U k : ℕ) : ℕ :=
  Cstage D Pre U (zfA k) zfB k

theorem CstageZ_eq (D : DecompOnTapes sc blank startSym endSym mark leftSym)
    (Pre : PrepOnTapes sc blank mark forb) (U k : ℕ) :
    CstageZ D Pre U k
      = CmT' D + rateP Pre + rateS + 86 + roundBudget U (zfA k) zfB k := rfl

/-- **`stage_round_actionsZ`**：段の 1 ラウンドの動作数は `CstageZ` 以下。 -/
theorem stage_round_actionsZ (D : DecompOnTapes sc blank startSym endSym mark leftSym)
    (Pre : PrepOnTapes sc blank mark forb) (u : List (Fin sc)) (U k S : ℕ)
    (n : ℕ) (St : StageT sc) :
    stcost D Pre u U (zfA k) zfB k S n St ≤ CstageZ D Pre U k :=
  stage_round_actions D Pre u U (zfA k) zfB k S n St

end Cost

/-! ## 3. 主定理 -/

section Answer

variable {blank startSym endSym mark leftSym : Fin sc}

/-- **`stage_tapes_specZ`**：`StageTapes.stage_tapes_spec'` の
`A := GSVTapesZ.zA k = 9k+14`, `B' := GSVTapesZ.zB = 16` 版（結論は同一）。

1 ラウンドの計量動作数は `zRate k = (k+1)(9k+30)`、1 ラウンドの動作数上界は
`CstageZ D Pre U k`（`stage_round_actionsZ`）。仮定 `hC : 0 < A + B'` は
`zfB = 16` から自動的に消える。残る仮定 `hcost` / `hadvance` は
**構造的なもの**（`cst` が走査状態だけの関数として `(A+B')·ΔΦ` 以下であること、
前進枝で `cst ≤ 1` であること）であり、ジグザグ一歩の点ごとの費用
`GSVTapesZ.vprogramZ'_cost`（`≤ (9k+14)·ΔΦ + 16`、**`2·checked` の項なし**）と
整合する。 -/
theorem stage_tapes_specZ
    {D : DecompOnTapes sc blank startSym endSym mark leftSym}
    {Pre : PrepOnTapes sc blank mark endSym}
    {one zero : Fin sc}
    {w : List (Fin sc)} {S k s p₁ r : ℕ} {cst : ScanState → ℕ} {init : StageT sc}
    (hmb : mark ≠ blank) (hS : 8 ≤ S) (hq : 4 * (S / 4) = S)
    (hres : Pre.res w (S / 2)
      = (s, effPeriod ((w.take (S / 2)).reverse.drop s) p₁, effReach p₁ r))
    (hkp : k * effPeriod ((w.take (S / 2)).reverse.drop s) p₁ ≤ 5 * S)
    (hpinit : PrepPre blank mark leftSym (S / 2) w (w.drop S) init.pg.ts)
    (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hcost : ∀ st, cst st ≤ (zfA k + zfB)
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w) (hstart : startSym ∉ w)
    (hev : 2 * (S / 2) = S)
    (hminit : ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m init.md)
    {n : ℕ} (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hw : n ≤ w.length) :
    stAnswerBit ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s)
        (w.drop S) k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r)
        cst (zfA k) zfB S one n
        (ststate D Pre one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst
          (zfA k) zfB S w init (n - 1))
        (ststate D Pre one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst
          (zfA k) zfB S w init n) = true
      ↔ (occursAt (w.take (S / 2)).reverse (w.take n)
          ∧ IsPal ((w.drop (S / 2)).take (n - S))) :=
  stage_tapes_spec' (hmb := hmb) (hS := hS) (hq := hq) (hres := hres) (hkp := hkp)
    (hpinit := hpinit) (hk := hk) (hs := hs) (H := H)
    (hC := by show 0 < GSVTapesZ.zA k + GSVTapesZ.zB; unfold GSVTapesZ.zB; omega)
    (hcost := hcost) (hadvance := hadvance) (hne := hne) (hleft := hleft) (hend := hend)
    (hstart := hstart) (hev := hev) (hminit := hminit) (h1 := h1) (h2 := h2) (hw := hw)

end Answer

/-! ## 4. 公理の確認 -/

#print axioms CstageZ_eq
#print axioms stage_round_actionsZ
#print axioms stage_tapes_specZ

end StageTapesZ
end PalPeg
