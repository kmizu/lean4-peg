import PalPeg.CloseoutPackRun49
import PalPeg.GalilEndOfInput

/-!
# `MatchRest.canRNext` は run の報告点で偽 — 機械検査済み

`CloseoutPackRun49.MatchRest` の 4 場のうち `canRNext : canRight (right s.right)` は
**mode の guard を持たない**。ところが `PreTrace.report w.length` が与える
`ReportPointAt.atPrefix`（`GalilLedgerAssembly:51`）は

    position (st (Tc w.length)).vm.right = 2 * w.length - 1

を**等式で**主張する。`GalilEndOfInput.not_canRight_iff` により
`¬ canRight p ↔ position p = 2 * |w|` なので、右ヘッドは 1 歩進むと動けなくなる。
よって trace の最終点で `canRNext` は偽。

**これは「過剰量化した名前付き葉」の 8 例目で、今回は自分が撒いたもの**
（`obligation_matchRest_alongTrace` を `∀ j ≤ Tc w.length` で書いた）。
正しい切り方は「着地状態の `canRight` は trace が `j+1` で与える」——
`scanRightHeadCanRight_alongTrace` / `shiftRightHeadCanRight_alongTrace` が
どちらも無償で持っているので、消費者側に渡せばよい。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.MatchRestRefute

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilFinalAssembly PalPeg.CloseoutPackRun49

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **報告点では右ヘッドは 1 歩で入力端に着く。** -/
theorem notCanRightNext_at_reportPoint {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ¬ canRight (right (st (Tc w.length)).vm.right) := by
  obtain ⟨-, ⟨r, hScanInv⟩, -, hAtPrefix, -⟩ := hPreTrace.report w.length hw le_rfl
  have hCanRight : canRight (st (Tc w.length)).vm.right := by
    by_contra hContra
    rw [PalPeg.GalilEndOfInput.not_canRight_iff _ w hScanInv.rightRep hScanInv.rightPresent]
      at hContra
    omega
  have hLeftNonempty : 0 < (st (Tc w.length)).vm.right.head.left.length :=
    (represented_position _ w hScanInv.rightRep hScanInv.rightPresent).1
  have hStep : position (right (st (Tc w.length)).vm.right)
      = position (st (Tc w.length)).vm.right + 1 :=
    right_position _ hCanRight hLeftNonempty
  rw [PalPeg.GalilEndOfInput.not_canRight_iff _ w
    (right_word _ w hScanInv.rightRep hCanRight)
    (right_present _ w hScanInv.rightRep hScanInv.rightPresent hCanRight)]
  omega

/-- **`MatchRest` を trace 全域で要求すると `False`。**（条件付き反証: 証人は
`PreTrace`、それ自体は `H_bootIMW` / `H_oracleIMW` 待ち。）

計画書 §10.5 に関わるので明記する: `obligation_matchRest_alongTrace` は
**この形のままでは偽**であり、再切り出しが必要。 -/
theorem matchRest_alongTrace_false {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hMatchRest : ∀ j, j ≤ Tc w.length →
      MatchRest w (st j).ctl (st j).vm) : False :=
  notCanRightNext_at_reportPoint centre place entry q first hw hPreTrace
    (hMatchRest (Tc w.length) le_rfl).canRNext

end

#print axioms notCanRightNext_at_reportPoint
#print axioms matchRest_alongTrace_false

end PalPeg.MatchRestRefute
