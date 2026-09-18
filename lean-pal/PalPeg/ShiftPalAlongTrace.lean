import PalPeg.BranchSupply
import PalPeg.CloseoutBundleRun
import PalPeg.CopyPhaseNoShift
import PalPeg.GalilPeriodUnion
import PalPeg.CloseoutShiftLocalFree

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

/-! ## `periodOnly = false` 分岐の**空虚な半分**

`obligation_shiftPalAtFreshChainAlongTrace`（n132 の原子 3 本目）は
`periodOnly = false` の点で `ShiftPal` を要求する。そこで chain の相で場合分けすると:

* **`CopyOrBack`（lag 正）** — 比較の行き先に `shiftGuardVM` が立たないので **空虚**（下の定理）
* `.watch`（準備完了、まだ shift していない） — 本体。DP 正当性の帰結のはず

`shiftGuardVM` は `zero w.lag = true` を要求するが、copy/back から 1 手で生まれる watch は
lag をそのまま受け継ぐ（`backDone`）か `inc` する（`Outer.queued`）ので、誕生 chain の
正 lag が保たれて guard が落ちる（`CopyPhaseNoShift.tick_not_watch_or_posLag`）。 -/

/-- **chain が watch でない点では `ShiftPal` は空虚に成り立つ**——`CopyOrBack` も
`CopyInv` も lag も要らない。純粋に構成子の形だけ。

`shiftGuardVM` は `w.machine.control.phase = 4` を要求するが、copy/back から 1 手で
生まれる watch の control は `watchControl v` で `phase = 0`、`Outer` を通しても
`phase ≤ 1`（`CopyPhaseNoShift.tick_watch_phase_ne_four`）。
**これで「found 時の半径が正」への依存がこの経路から消えた**（n134 の版は `LagPos` を
取っていたが不要だった）。 -/
theorem shiftPal_of_chainNotWatch {w : List (Fin 2)} {s : GalilVM}
    (hNotWatch : ∀ wv : GalilScaffoldChainWatch.State, s.chain ≠ ChainVM.watch wv) :
    ShiftPal centre place entry q first w s := by
  intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
  exfalso
  obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchainAt, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hCompare
  have hChainEq : s'.chain = vs.chain := by
    rw [hteq, afterBirth_chain]
    split <;> rfl
  obtain ⟨wg, hwg, -, hPhase4, -, -, -⟩ := hGuard
  rw [hChainEq] at hwg
  rcases hchainAt with ⟨-, hct⟩ | ⟨-, -, hzidle⟩ | ⟨-, -, hbirth⟩
  · exact PalPeg.CopyPhaseNoShift.tick_watch_phase_ne_four_of_notWatch hNotWatch hct wg hwg hPhase4
  · rw [hzidle] at hwg; exact ChainVM.noConfusion hwg
  · cases a with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hbirth
      rw [hbirth] at hwg
      exact ChainVM.noConfusion hwg
    | true =>
      simp only [if_true, chainStart] at hbirth
      rw [hwg] at hbirth
      cases hbirth

#print axioms shiftPal_of_chainNotWatch

/-! ## `periodOnly = false` ＋ watch の本体（残差を名前付きに絞った形）

n141 で数学の芯（`PalPeg.reshift_of_palAt_pair`）が完成したので、`ShiftPalAt` の
結論をその適用として書き、**残差を名前付き仮説として上に出す**。

残差は 5 つで、どれも「chain の履歴」か「台帳」:

| 残差 | 何か | 材料 |
|---|---|---|
| `hIn` / `hOut` | この watch の周期テープが DP の `Candidate` から来たという履歴 | `GalilPrepLeast.prep_watch_start_least` ＋ `CloseoutWatchPhase3.palAt_pair_of_candidate` |
| `hLo` (`2h ≤ r₀`) / `hHi` (`r₀ ≤ 4h`) | 半径と周期の台帳 | `GalilReplayBudgetProof.found_radius_le_two_period`（found 時 `radius ≤ 2h`）＋ 一致比較ぶんの伸び |
| `hCaught` | chain が周期 `2h` 分遅れて入力に追随している | `periodOnly = true` 側では `RoundScan.pred` が同じ形を持つ |

**入力側の添字化はここで済ませている**（`GalilRoundPeriod.right_read_index` ＋
`ScanInvariant.rightPos`）ので、`hCaught` は純粋に chain 側の事実。 -/

/-- **`periodOnly = false` ＋ watch での `ShiftPal` の結論。**  残差は上表の 5 つだけ。 -/
theorem shiftPalAt_fresh_of_candidate {w : List (Fin 2)} {s s' : GalilVM}
    {wch : GalilScaffoldChainWatch.State} {h r₀ : ℕ}
    (hChain : s'.chain = ChainVM.watch wch)
    (hGuard : shiftGuardVM s')
    (hRight : s'.right = right s.right)
    (hCan : canRight s.right)
    (hScanInv : ScanInvariant w (position s.center) r₀ s.left s.right)
    (hPeriod : periodLength wch = h)
    (hIn : Manacher.PalAt (encoded w) (position s.center - h) h)
    (hOut : Manacher.PalAt (encoded w) (position s.center - 2 * h) (2 * h))
    (hPos : 0 < h) (hLo : 2 * h ≤ r₀) (hHi : r₀ ≤ 4 * h)
    (hEnd : position s.center + r₀ + 1 < (encoded w).length)
    (hCaught : (encoded w)[position s.center + r₀ + 1 - 2 * h]? =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus) :
    1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
      Manacher.PalAt (encoded w) (position s.center + periodLength wch)
        (r₀ + 1 - periodLength wch) := by
  obtain ⟨wg, hwg, -, -, -, -, hsym⟩ := hGuard
  have hwe : wg = wch := by rw [hChain] at hwg; cases hwg; rfl
  rw [hwe] at hsym
  have hread : GalilScaffoldInputHead.read (right s.right) =
      (encoded w)[position s.center + r₀ + 1]? := by
    rw [PalPeg.GalilRoundPeriod.right_read_index s.right w hScanInv.rightRep
      hScanInv.rightPresent hCan, hScanInv.rightPos]
  have hsym' : GalilScaffoldChainConsume.symbol wch.machine.control.period.focus =
      (encoded w)[position s.center + r₀ + 1]? := by
    rw [← hread, ← hRight]; exact hsym
  have hpredIdx : (encoded w)[position s.center + r₀ + 1]? =
      (encoded w)[position s.center + r₀ + 1 - 2 * h]? := by
    rw [← hsym']; exact hCaught.symm
  refine ⟨by omega, by omega, ?_⟩
  rw [hPeriod]
  exact PalPeg.reshift_of_palAt_pair (encoded w) (position s.center) h r₀
    hIn hOut hScanInv.palindrome hPos hLo hHi hEnd hpredIdx

#print axioms shiftPalAt_fresh_of_candidate

/-- **(NAMED) 準備直後の watch の台帳。**  `shiftPalAt_fresh_of_candidate` の 5 残差を
1 つの場にまとめたもの。`ShiftPal` の `periodOnly = false` 分岐に必要な全部で、
3 種類しかない（n144）:

* `hIn` / `hOut` — period テープの**中身**（DP の `Candidate` 由来）
* `0 < h` / `2h ≤ r₀` / `r₀ ≤ 4h` / `hEnd` — 半径と周期の**大小**
* 最後の等式 — period テープの**位相**（`RoundScan.pred` の `periodOnly = false` 版） -/
def FreshShiftLedger (w : List (Fin 2)) (s s' : GalilVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch wch →
    ∀ r₀ : ℕ, ScanInvariant w (position s.center) r₀ s.left s.right →
      Manacher.PalAt (encoded w) (position s.center - periodLength wch) (periodLength wch) ∧
      Manacher.PalAt (encoded w) (position s.center - 2 * periodLength wch)
        (2 * periodLength wch) ∧
      0 < periodLength wch ∧
      2 * periodLength wch ≤ r₀ ∧ r₀ ≤ 4 * periodLength wch ∧
      position s.center + r₀ + 1 < (encoded w).length ∧
      (encoded w)[position s.center + r₀ + 1 - 2 * periodLength wch]? =
        GalilScaffoldChainConsume.symbol wch.machine.control.period.focus

/-- **`ShiftPal` を `FreshShiftLedger` 1 つから。**  比較の行き先の右ヘッドが
`right s.right` であることは `compareFound` の `hvr` から出る（`afterBirth` /
`afterCompare` / `afterMismatch` はどれも右ヘッドを `vs.right` にする）。 -/
theorem shiftPal_of_freshShiftLedger {w : List (Fin 2)} {s : GalilVM}
    (hCan : canRight s.right)
    (hLedger : ∀ s' : GalilVM,
      compareFound (PofC centre place entry w) q first s s' → FreshShiftLedger w s s') :
    ShiftPal centre place entry q first w s := by
  intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
  obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchainAt, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := id hCompare
  have hRight : s'.right = right s.right := by
    rw [hteq, afterBirth_right]
    cases a with
    | false => rw [if_neg (by simp)]; exact hvr
    | true => rw [if_pos rfl]; exact hvr
  obtain ⟨hIn, hOut, hPos, hLo, hHi, hEnd, hCaught⟩ :=
    hLedger s' hCompare wch hChain r₀ hScanInv
  exact shiftPalAt_fresh_of_candidate hChain hGuard hRight hCan hScanInv rfl
    hIn hOut hPos hLo hHi hEnd hCaught

#print axioms shiftPal_of_freshShiftLedger

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
    (hFreshLedger : ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).vm.periodOnly = false →
      ∀ s' : GalilVM, compareFound (PofC centre place entry w) q first (st j).vm s' →
        FreshShiftLedger w (st j).vm s') :
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
    (fun hpo => shiftPal_of_freshShiftLedger centre place entry q first
      (hCanRight j hIndexLeTc (Or.inl hMode))
      (hFreshLedger j hIndexPos hIndexLeTc hpo))


/-! ## run 形（`InvLPC` 起点から到達する scan 状態）

trace 形とまったく同じ 3 残差に落ちる。**起点の違いだけ**:

| 入力 | trace 形の出どころ | run 形の出どころ |
|---|---|---|
| chain が idle | `chainIdle_after_init`（boot の 1 手目） | `CloseoutShiftLocalFree.chainIdle_of_invS`（`InvLPC` の `InvS`） |
| `AuxPack` | `auxPack_alongTrace_afterFirstStep` | `CloseoutPackRun2.auxPack_steps` ＋ `InvLPC` の 3 場 |
| `canRight right` | `canRightAtScanOrShift_alongTrace`（trace 予算） | **消費者が持っている**（`BigPack2MG7W''.extra : Extra7` の `scanAvail`） |

`canRight` を仮説に取るのは過剰量化の解消。唯一の消費者
`CloseoutMarksPack.packRunR_MW_marksFree` は帰納段で `BigPack2MG7W''` を持っており、
その `Extra7.scanAvail` が scan・非 replay 点でちょうど `canRight` を与える。
以前の形はそれを捨てていた。 -/
theorem shiftPal_alongRun {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hInvLPC : PalPeg.GalilInvPlus2.InvLPC w c r)
    (hReadsShift : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      H_readsShift w z.ctl z.vm)
    (hFreshShift : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      H_freshShiftAtShiftEntry centre place entry q first w z.ctl z.vm z'.vm)
    (hFreshLedger : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      z.vm.periodOnly = false → ∀ s' : GalilVM,
        compareFound (PofC centre place entry w) q first z.vm s' →
          FreshShiftLedger w z.vm s')
    (m : ℕ) (z : State GalilVM)
    (hSteps : Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z)
    (hMode : z.ctl.mode = Mode.scan) (hNotReplaying : z.ctl.replaying = false)
    (hCanRight : canRight z.vm.right) :
    ShiftPal centre place entry q first w z.vm :=
  shiftPal_of_run_B centre place entry q first
    (PalPeg.CloseoutShiftLocalFree.chainIdle_of_invS hInvLPC.1.1.1.1) hSteps
    (fun _ _ hz' => PalPeg.CloseoutPackRun2.auxPack_steps centre place entry q first
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hInvLPC)
      ⟨PalPeg.CloseoutPackRun.coupled_of_invLPC hInvLPC,
        PalPeg.CloseoutPackRun.front_of_invLPC hInvLPC,
        PalPeg.CloseoutPackRun.copyPack_of_invLPC hInvLPC⟩ hz')
    hReadsShift hFreshShift hMode hNotReplaying hCanRight
    (fun hpo => shiftPal_of_freshShiftLedger centre place entry q first hCanRight
      (hFreshLedger m z hSteps hpo))

end

#print axioms shiftPal_alongRun
#print axioms chainIdle_after_init
#print axioms roundBundle_alongTrace
#print axioms shiftPal_alongTrace

end PalPeg.ShiftPalAlongTrace
