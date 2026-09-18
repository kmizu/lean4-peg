import PalPeg.BranchSupply
import PalPeg.CloseoutBundleRun
import PalPeg.CopyPhaseNoShift

/-!
# `ShiftPal` を trace 形で（`hSP` の正しい形）

**2026-09-19（n112）**: 公理 `obligation_shiftPalAtScanStates` は

    ∀ w x, BigPack2MG7W … w x → ScanNR x → ShiftPal … w x.vm

という**一状態述語**の形で、`ShiftPal` の結論「chain の周期が入力語 `w` の本物の周期で
ある」という**履歴の事実**を要求していた。`BigPack2MG7W` の場を一次情報で全部展開すると、
chain の周期テープの中身と `w` を結びつける場が 1 つも無い（`w` に触れる場はヘッド、
chain に触れる場はカウンタ）。`hpack` が偽だったのと同じ欠陥で、**偽の疑いが濃い**
（機械検査した反証はまだ無いので `REFUTED` とは書かない）。

正しい形は run/trace 形。`CloseoutRoundBundle.RoundBundle` を trace に沿って運び、
各 scan 点で `shiftPal_of_roundBundle` が読み出す。起点は `st 1`——boot の 1 手目は
`init` で、`initVM` は `t.chain = .idle` を置くから（`AuxPack` は boot では偽なので
`st 0` からは始められない: `AuxPackNotAtBoot`）。

残差は 3 つで、どれも trace 形かつ狭い:

| 残差 | 形 |
|---|---|
| `AuxPack` | trace 形（`BranchSupply.auxPack_alongTrace_afterFirstStep` で**放電済み**） |
| `canRight right` | trace 形（`BranchSupply.canRightAtScanOrShift_alongTrace` で**放電済み**） |
| `H_readsShift` | trace 形（`RoundSegFromRun.readsShift_at_actual` が実状態で出す） |
| `H_freshShiftAtShiftEntry` | tick 形（shift 入口に狭めた版、`first_round` から） |
| `hfresh`（`periodOnly = false` 分岐） | 状態ごと |

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ShiftPalAlongTrace

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFinalAssembly
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutRoundUnique PalPeg.CloseoutRoundBundle PalPeg.CloseoutBundleRun
open PalPeg.BranchSupply

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`init` の行き先は chain が idle。**  `initVM` が `t.chain = .idle` を置く。 -/
theorem chainIdle_after_init {w : List (Fin 2)} (x y : State GalilVM)
    (hTick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hMode : x.ctl.mode = Mode.init) : y.vm.chain = ChainVM.idle := by
  obtain ⟨hInit, -⟩ := init_tick_target_is_scan centre place entry q first x y hTick hMode
  obtain ⟨-, -, -, -, -, -, -, -, -, hChain, -, -, -, -, -⟩ : initVM entry x.vm y.vm := hInit
  exact hChain

/-- **`RoundBundle` を trace に沿って（`st 1` から）。** -/
theorem roundBundle_alongTrace {w : List (Fin 2)}
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hTcPos : 1 ≤ Tc w.length)
    (hAuxPack : ∀ j, 1 ≤ j → j ≤ Tc w.length → AuxPack (st j).ctl (st j).vm)
    (hReadsShift : ∀ j, 1 ≤ j → j ≤ Tc w.length → H_readsShift w (st j).ctl (st j).vm)
    (hFreshShift : ∀ j, 1 ≤ j → j < Tc w.length →
      H_freshShiftAtShiftEntry centre place entry q first w (st j).ctl (st j).vm (st (j+1)).vm) :
    ∀ j, 1 ≤ j → j ≤ Tc w.length → RoundBundle w (st j).ctl (st j).vm := by
  have hBase : RoundBundle w (st 1).ctl (st 1).vm := by
    refine roundBundle_of_idle ?_
    refine chainIdle_after_init centre place entry q first (st 0) (st 1)
      (hPreTrace.trace.tick 0 (by omega)) ?_
    rw [hPreTrace.start]; rfl
  intro j
  induction j with
  | zero => intro hIndexPos; exact absurd hIndexPos (by omega)
  | succ n ih =>
    intro _ hIndexLeTc
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact hBase
    · exact roundBundle_tick_B centre place entry q first (c := (st n).ctl) (s := (st n).vm)
        (c' := (st (n+1)).ctl) (t := (st (n+1)).vm)
        (ih hn (by omega))
        (hAuxPack n hn (by omega)).coupled.block
        (fun hShift => copyIdle_shift_of_auxPack (hAuxPack n hn (by omega)) hShift)
        (hReadsShift n hn (by omega))
        (hFreshShift n hn (by omega))
        (hPreTrace.trace.tick n (by omega))

/-- **`ShiftPal` を trace の scan 点で**（`hSP` の正しい形）。 -/
theorem shiftPal_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hTcPos : 1 ≤ Tc w.length)
    (hReadsShift : ∀ j, 1 ≤ j → j ≤ Tc w.length → H_readsShift w (st j).ctl (st j).vm)
    (hFreshShift : ∀ j, 1 ≤ j → j < Tc w.length →
      H_freshShiftAtShiftEntry centre place entry q first w (st j).ctl (st j).vm (st (j+1)).vm)
    (hFreshBranch : ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).vm.periodOnly = false →
      ShiftPal centre place entry q first w (st j).vm) :
    ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).ctl.mode = Mode.scan →
      (st j).ctl.replaying = false → ShiftPal centre place entry q first w (st j).vm := by
  have hAuxPack := auxPack_alongTrace_afterFirstStep centre place entry q first hw
    hPreTraceIMW.base.pre
  have hCanRight := canRightAtScanOrShift_alongTrace centre place entry q first hw hPreTraceIMW
  have hBundle := roundBundle_alongTrace centre place entry q first hPreTraceIMW.base.pre hTcPos
    hAuxPack hReadsShift hFreshShift
  intro j hIndexPos hIndexLeTc hMode hNotReplaying
  exact shiftPal_of_roundBundle centre place entry q first hMode hNotReplaying
    (hBundle j hIndexPos hIndexLeTc)
    (hCanRight j hIndexLeTc (Or.inl hMode))
    (hFreshBranch j hIndexPos hIndexLeTc)


/-! ## `periodOnly = false` 分岐の**空虚な半分**

`obligation_shiftPalAtFreshChainAlongTrace`（n132 の原子 3 本目）は
`periodOnly = false` の点で `ShiftPal` を要求する。そこで chain の相で場合分けすると:

* **`CopyOrBack`（lag 正）** — 比較の行き先に `shiftGuardVM` が立たないので **空虚**（下の定理）
* `.watch`（準備完了、まだ shift していない） — 本体。DP 正当性の帰結のはず

`shiftGuardVM` は `zero w.lag = true` を要求するが、copy/back から 1 手で生まれる watch は
lag をそのまま受け継ぐ（`backDone`）か `inc` する（`Outer.queued`）ので、誕生 chain の
正 lag が保たれて guard が落ちる（`CopyPhaseNoShift.tick_not_watch_or_posLag`）。 -/

/-- **`CopyOrBack`（lag 正）の点では `ShiftPal` は空虚に成り立つ。** -/
theorem shiftPal_of_copyOrBack {w : List (Fin 2)} {s : GalilVM}
    (hPhase : PalPeg.CopyPhaseTick.CopyOrBack s.chain)
    (hLag : PalPeg.CopyPhaseTickMatched.LagPos s.chain) :
    ShiftPal centre place entry q first w s := by
  intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
  exfalso
  obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchainAt, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hCompare
  have hNotIdle : s.chain ≠ ChainVM.idle := PalPeg.CopyPhaseTick.copyOrBack_not_idle hPhase
  have hTick : ChainTick a s.chain vs.chain := by
    rcases hchainAt with ⟨-, hct⟩ | ⟨hidle, -, -⟩ | ⟨hidle, -, -⟩
    · exact hct
    · exact absurd hidle hNotIdle
    · exact absurd hidle hNotIdle
  have hChainEq : s'.chain = vs.chain := by
    rw [hteq, afterBirth_chain]
    split <;> rfl
  rw [hChainEq] at hChain
  obtain ⟨wg, hwg, hZeroLag, -, -, -, -⟩ := hGuard
  rw [hChainEq] at hwg
  rcases PalPeg.CopyPhaseNoShift.tick_not_watch_or_posLag hPhase hLag hTick with hNot | ⟨wv, hEq, hZeroFalse⟩
  · exact hNot wch hChain
  · rw [hwg] at hEq
    cases hEq
    rw [hZeroFalse] at hZeroLag
    exact absurd hZeroLag (by decide)

#print axioms shiftPal_of_copyOrBack

end

#print axioms chainIdle_after_init
#print axioms roundBundle_alongTrace
#print axioms shiftPal_alongTrace

end PalPeg.ShiftPalAlongTrace
