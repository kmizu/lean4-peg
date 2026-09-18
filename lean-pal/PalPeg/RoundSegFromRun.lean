import PalPeg.CloseoutRoundSeg
import PalPeg.ShiftPhaseDeterminism
import PalPeg.MatchedRunSnoc
import PalPeg.CloseoutReadsOrigin

/-!
# `RoundSeg` を run の実際の状態で

`CloseoutRoundSeg` は `hSP` の残差を `RoundSeg`（＝ `CompareRounds h _ 1 _`）と
`H_fresh` の 2 つに絞った。`GalilScaffoldTopRoundS.round_next` は 1 ラウンドを
**構成**して `CompareRounds` を返すが、その着地は構成した状態
`shiftLens.set s2 ⟨t', .watch v, cycle⟩` であって run の実際の着地ではない。

ここはその段差だけを埋める:

* `roundSeg_of_compareRounds` — `RoundSeg` は `CompareRounds` の包みでしかない
  （周期長が両端で一致すればよい）。
* `compareRounds_at_actual` — 構成した着地での `CompareRounds` を run の実際の
  着地へ移す。移せる理由は shift 相が決定的だから（`ShiftPhaseDeterminism`）で、
  `Fair` は要らない。scan 側は `MatchedRunSnoc.onlyMatchedRun_of_steps` が
  最初から実際の状態で出しているので段差がない。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RoundSegFromRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.CloseoutRoundSeg PalPeg.ShiftPhaseDeterminism

/-- **`RoundSeg` は `CompareRounds` の包み。**  両端の watch は状態が決めるので
全称量化は無償、周期長の一致だけが中身。 -/
theorem roundSeg_of_compareRounds {w : List (Fin 2)} {s s' : GalilVM} {h : ℕ}
    {w0 v : GalilScaffoldChainWatch.State}
    (hChainStart : s.chain = ChainVM.watch w0) (hPeriodStart : periodLength w0 = h)
    (hChainEnd : s'.chain = ChainVM.watch v) (hPeriodEnd : periodLength v = h)
    (hCompareRounds : CompareRounds h (toOnly s w0) 1 (toOnly s' v)) :
    RoundSeg w s s' := by
  intro wch wch' hch hch'
  rw [hChainStart] at hch
  cases hch
  rw [hChainEnd] at hch'
  cases hch'
  refine ⟨by rw [hPeriodEnd, hPeriodStart], ?_⟩
  rw [hPeriodStart]
  exact hCompareRounds

/-- **構成した着地での `CompareRounds` を run の実際の着地へ移す。**

`x` は shift 入口（`scan_shift` tick の行き先）。構成側（`round_next` /
`terminal_shift_steps` / `shift_phase_stepsAll_S`）と実際の run はどちらもそこから
出発して shift 相を抜けるので、`shift_landing_eq` で着地が一致する。 -/
theorem compareRounds_at_actual {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {s : GalilVM} {w0 v : GalilScaffoldChainWatch.State} {h : ℕ}
    {x yc ya : State GalilVM} {Kc Ka : ℕ}
    (hCompareRounds : CompareRounds h (toOnly s w0) 1 (toOnly yc.vm v))
    (hShiftEntry : x.ctl.mode = Mode.shift)
    (hConstructed : Steps (galilFrameS P q first) delay Kc x yc)
    (hExitConstructed : yc.ctl.mode ≠ Mode.shift)
    (hRemainingConstructed : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Kc →
      (galilFrameS P q first).remainingPos z.vm)
    (hActual : Steps (galilFrameS P q first) delay Ka x ya)
    (hExitActual : ya.ctl.mode ≠ Mode.shift)
    (hRemainingActual : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Ka →
      (galilFrameS P q first).remainingPos z.vm) :
    CompareRounds h (toOnly s w0) 1 (toOnly ya.vm v) := by
  obtain ⟨hLandingEq, -⟩ := shift_landing_eq hShiftEntry hActual hExitActual hRemainingActual
    hConstructed hExitConstructed hRemainingConstructed
  rw [hLandingEq]
  exact hCompareRounds

/-- **`RoundSeg` を run の実際の状態で**（上の 2 本の合成）。 -/
theorem roundSeg_at_actual {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {s : GalilVM} {w0 v : GalilScaffoldChainWatch.State} {h : ℕ}
    {x yc ya : State GalilVM} {Kc Ka : ℕ}
    (hCompareRounds : CompareRounds h (toOnly s w0) 1 (toOnly yc.vm v))
    (hChainStart : s.chain = ChainVM.watch w0) (hPeriodStart : periodLength w0 = h)
    (hChainEnd : ya.vm.chain = ChainVM.watch v) (hPeriodEnd : periodLength v = h)
    (hShiftEntry : x.ctl.mode = Mode.shift)
    (hConstructed : Steps (galilFrameS P q first) delay Kc x yc)
    (hExitConstructed : yc.ctl.mode ≠ Mode.shift)
    (hRemainingConstructed : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Kc →
      (galilFrameS P q first).remainingPos z.vm)
    (hActual : Steps (galilFrameS P q first) delay Ka x ya)
    (hExitActual : ya.ctl.mode ≠ Mode.shift)
    (hRemainingActual : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Ka →
      (galilFrameS P q first).remainingPos z.vm) :
    RoundSeg w s ya.vm :=
  roundSeg_of_compareRounds hChainStart hPeriodStart hChainEnd hPeriodEnd
    (compareRounds_at_actual hCompareRounds hShiftEntry hConstructed hExitConstructed
      hRemainingConstructed hActual hExitActual hRemainingActual)

/-- **`OriginAt` がラウンドを 1 つ越える（run の実際の状態で）。**
`CloseoutRoundSeg.originAt_of_roundSeg` との合成。これが `H_readsShift` の
唯一の供給元（`CloseoutReadsOrigin.h_readsShift_of_originAt`）。 -/
theorem originAt_at_actual {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {s : GalilVM} {w0 v : GalilScaffoldChainWatch.State} {h : ℕ}
    {x yc ya : State GalilVM} {Kc Ka : ℕ}
    (hOriginStart : PalPeg.CloseoutOriginAt.OriginAt w s)
    (hCompareRounds : CompareRounds h (toOnly s w0) 1 (toOnly yc.vm v))
    (hChainStart : s.chain = ChainVM.watch w0) (hPeriodStart : periodLength w0 = h)
    (hChainEnd : ya.vm.chain = ChainVM.watch v) (hPeriodEnd : periodLength v = h)
    (hShiftEntry : x.ctl.mode = Mode.shift)
    (hConstructed : Steps (galilFrameS P q first) delay Kc x yc)
    (hExitConstructed : yc.ctl.mode ≠ Mode.shift)
    (hRemainingConstructed : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Kc →
      (galilFrameS P q first).remainingPos z.vm)
    (hActual : Steps (galilFrameS P q first) delay Ka x ya)
    (hExitActual : ya.ctl.mode ≠ Mode.shift)
    (hRemainingActual : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Ka →
      (galilFrameS P q first).remainingPos z.vm) :
    PalPeg.CloseoutOriginAt.OriginAt w ya.vm :=
  originAt_of_roundSeg hOriginStart
    (roundSeg_at_actual hCompareRounds hChainStart hPeriodStart hChainEnd hPeriodEnd
      hShiftEntry hConstructed hExitConstructed hRemainingConstructed hActual hExitActual
      hRemainingActual)
    (fun _ _ => ⟨w0, hChainStart⟩)

#print axioms roundSeg_of_compareRounds
#print axioms compareRounds_at_actual
#print axioms roundSeg_at_actual
#print axioms originAt_at_actual


/-- **`H_readsShift` を run の実際の状態で。**

`shiftPal_of_run_B` の 2 残差のうち 1 つがこれ。鎖は

    OriginAt（前ラウンド起点）
      → roundSeg_at_actual（このファイル、shift 相の決定性で実状態へ）
      → CloseoutReadsOrigin.originShift_of_roundSeg
      → CloseoutReadsOrigin.h_readsShift_of_originShift
      → H_readsShift

で、新しい名前付きの葉はゼロ。残るのは「`OriginAt` を前ラウンド起点で持つ run 不変量」
に仕立てる部分（tick 搬送）と `round_next` の入力の配線。 -/
theorem readsShift_at_actual {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {s : GalilVM} {w0 v : GalilScaffoldChainWatch.State} {h : ℕ}
    {x yc ya : State GalilVM} {Kc Ka : ℕ} {cOut : Control}
    (hOriginStart : PalPeg.CloseoutOriginAt.OriginAt w s)
    (hCompareRounds : CompareRounds h (toOnly s w0) 1 (toOnly yc.vm v))
    (hChainStart : s.chain = ChainVM.watch w0) (hPeriodStart : periodLength w0 = h)
    (hChainEnd : ya.vm.chain = ChainVM.watch v) (hPeriodEnd : periodLength v = h)
    (hShiftEntry : x.ctl.mode = Mode.shift)
    (hConstructed : Steps (galilFrameS P q first) delay Kc x yc)
    (hExitConstructed : yc.ctl.mode ≠ Mode.shift)
    (hRemainingConstructed : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Kc →
      (galilFrameS P q first).remainingPos z.vm)
    (hActual : Steps (galilFrameS P q first) delay Ka x ya)
    (hExitActual : ya.ctl.mode ≠ Mode.shift)
    (hRemainingActual : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay j x z → j < Ka →
      (galilFrameS P q first).remainingPos z.vm) :
    PalPeg.CloseoutRoundUnique.H_readsShift w cOut ya.vm :=
  PalPeg.CloseoutReadsOrigin.h_readsShift_of_originShift
    (PalPeg.CloseoutReadsOrigin.originShift_of_roundSeg hOriginStart
      (roundSeg_at_actual hCompareRounds hChainStart hPeriodStart hChainEnd hPeriodEnd
        hShiftEntry hConstructed hExitConstructed hRemainingConstructed hActual hExitActual
        hRemainingActual)
      (fun _ _ => ⟨w0, hChainStart⟩))

#print axioms readsShift_at_actual

end PalPeg.RoundSegFromRun
