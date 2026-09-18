import PalPeg.CloseoutOracleW
import PalPeg.CloseoutPackRun40

/-!
# `ShiftLocalS` を run 沿いに持つことだけを入力にする — `hfour` 不要の経路

## 1. コピペの括り出し

`RadPack` → `TrailF` → `needL'` の 3 段は、いま**4 回**書かれている：

| 版 | 場所 | `ShiftLocalS` の作り方 |
|---|---|---|
| S | `CloseoutShiftS.radPack_ptS` / `trailF_ptS` | `ChainPosInv` ＋ `hfour` |
| S3 | `CloseoutWatchSupply.radPack_ptS3` / `trailF_ptS3` | `ChainPosInv2` ＋ `ChainPack`（`hpack` は偽） |
| S4 | `CloseoutVerSide.radPack_ptS4` / `trailF_ptS4` | `ChainPosInv2` ＋ `VerRun` |
| （本ファイル） | — | `ChainPosInv'`（前提追加なし） |

3 段の本体は `hShiftLocalS : ∀ i ≤ Tc w.length, ShiftLocalS … (st i)` しか使っていない
（`radPack_ptS` の最初の `have` がそれで、以降 `hfour`/`hbg`/`hmatch`/`hsd`/`hChainPosInv2AtOrigin`/`hreach`
は一切現れない）。よって **`hShiftLocalS` を引数に取る形**で 1 度だけ書けば 4 版すべてが乗る。
それが §2 の `radPack_alongTrace_of_shiftLocalS` / `trailF_alongTrace_of_shiftLocalS` /
`needBound_of_shiftLocalS_alongTrace`。

## 2. `hfour` は前提追加なしで消える

`CloseoutPackRun40` は `ChainPosInv'`（`ChainPosInv` の `Coupled` を `Coupled'` に
差し替えただけ）と

* `watchShiftS_of_chainPosInv'`（:407）— **`H_fourOther` を取らない**。
  `Other'`（5h 版）は `Coupled'.watch` の場から出てくるので `four_of_other'` が直接効く。
* `chainPosInv'_tick`（:435）— 必要な分岐前提は **`H_bgP` / `H_matchP` / `H_shiftDoneP` の
  3 本だけ**。`final30` が既に取っている 3 本と同一。
* `coupled'_of_idle`（:87）— boot は無条件。

を持っている。したがって `hfour` は**何も足さずに落ちる**。

（`final31` は `hav` を、`final36`/`final37` は `hpack` を代わりに取っていたが、
どちらも偽: `ConsumeAvailRefute.hav_false` / `CloseoutPackRefute.hpack_false`。）

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ShiftLocalRun

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun43
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftWeak
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutLPack PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun30
open PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6 PalPeg.CloseoutPackRun12
open PalPeg.GalilTrailSane PalPeg.GalilChainCoupling PalPeg.GalilBranchInvariants
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun8
open PalPeg.GalilTrailChain PalPeg.GalilFinalAssembly PalPeg.GalilThrottledRun
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3 PalPeg.CloseoutRadPack4
open PalPeg.GalilTrailRad PalPeg.GalilTrailProof PalPeg.GalilTrailAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailFront
open PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun38 PalPeg.GalilBranchInvariants
open PalPeg.CloseoutOracleW PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun40

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 2. `RadPack` / `TrailF` / `needL'` を `hShiftLocalS` だけから -/

/-- **`RadPack` along the trace from pointwise `ShiftLocalS`.**  This is
`CloseoutShiftS.radPack_ptS` with its first `have` taken as an argument; the
rest of that proof never mentions `hfour`/`hbg`/`hmatch`/`hsd`/`hChainPosInv2AtOrigin`. -/
theorem radPack_alongTrace_of_shiftLocalS {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hShiftLocalS : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i))
    (hLPackM2AtTarget : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'' := by
    intro i hIndexLeTc hs s'' t'' hcmp hmt hg hb
    obtain ⟨rad, hscan, hcan, hh⟩ :=
      halfBound_of_shiftLocalS centre place entry q first (hLPackM2AtTarget i hIndexLeTc) (hShiftLocalS i hIndexLeTc) hs hcmp hmt hg hb
    exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
      hscan hcan hcmp hb hh
  have hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain := fun i hIndexLeTc hs s'' t'' =>
    saneVer_of_shiftLocalS centre place entry q first (hShiftLocalS i hIndexLeTc) hs
  have hLagCan := radLedger_pt centre place entry q first hw hPreTrace hll
  have hS := shiftOrd_ptS centre place entry q first hw hPreTrace hll hen
  have hVerRun := verSane_ptS centre place entry q first hw hPreTrace hll hsv
  exact fun i hIndexLeTc => radPack_of_parts (hLagCan i hIndexLeTc) (hS i hIndexLeTc) (hll i hIndexLeTc) (hVerRun i hIndexLeTc)

/-- **`TrailF` along the trace from pointwise `ShiftLocalS`.** -/
theorem trailF_alongTrace_of_shiftLocalS {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hShiftLocalS : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i))
    (hLPackM2AtTarget : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hSanePack := sanePack_pt centre place entry q first hw hPreTrace hll
  have hrad := radPack_alongTrace_of_shiftLocalS centre place entry q first hw hPreTrace hShiftLocalS hLPackM2AtTarget hll
  have hscan := scanT_pt centre place entry q first hw hPreTrace hrad hSanePack hm
  have hLandingObligations := chainBudget_pt centre place entry q first hw hPreTrace hrad hSanePack hm
  have hVerRun := verF_trace centre place entry q first hPreTrace hm hscan hLandingObligations
  exact fun i hIndexLeTc => trailF_of_scanT (hscan i hIndexLeTc) (hVerRun i hIndexLeTc).ver (hVerRun i hIndexLeTc).lagPos

/-- **`needL'` over `PreTraceIMW` from pointwise `ShiftLocalS`.**  The four
`needIMW'_le_*` variants differ only in how they build `hShiftLocalS`. -/
theorem needBound_of_shiftLocalS_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hShiftLocalS : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hbase := hPreTrace.base.pre
  have hLPackM2AtTarget : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm :=
    fun i hIndexLeTc => (hPreTrace.packs i hIndexLeTc).pack
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hIndexLeTc => leftLive_of_lpackM (hLPackM2AtTarget i hIndexLeTc)
  intro m hm i hIndexLeTc
  exact needL'_le_of_trailF w st m i
    (trailF_alongTrace_of_shiftLocalS centre place entry q first hw hbase hShiftLocalS hLPackM2AtTarget hll hm i hIndexLeTc)

/-! ## 3. `ChainPosInv'` を run 沿いに運ぶ（`hfour` なし） -/

/-- `ChainPosInv'` は idle chain で無条件。 -/
theorem chainPosInvCoupled'_at_idle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hIndexLeTc : s.chain = ChainVM.idle) : ChainPosInv' w c s :=
  ⟨coupled'_of_idle hIndexLeTc, fun _ hni => absurd hIndexLeTc hni⟩

/-- **`ChainPosInv'` along a run.**  `final30` の 3 分岐前提だけで閉じる。 -/
theorem chainPosInvCoupled'_alongRun {w : List (Fin 2)}
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv' w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ChainPosInv' w y.ctl y.vm := by
  induction h with
  | zero x => exact hx
  | @succ n x z y ht _ ih =>
    exact ih (chainPosInv'_tick centre place entry q first hbg hmatch hsd hx ht)

/-- **`ShiftLocalS` from `ChainPosInv'`** — `CloseoutShiftS.shiftLocalS_of_chainPosInv`
with `hfour` gone. -/
theorem shiftLocalS_of_chainPosInvCoupled' {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainPosInv' w x.ctl x.vm) : ShiftLocalS centre place entry q first w x := by
  by_cases hIndexLeTc : x.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hIndexLeTc
  · exact shiftLocalS_of_watchShiftS centre place entry q first hIndexLeTc
      (watchShiftS_of_chainPosInv' centre place entry q first h)

/-- **`ShiftLocalS` at every state of a run, with no `hfour`.** -/
theorem shiftLocalS_alongRun_of_chainPosInvCoupled' {w : List (Fin 2)}
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv' w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    ShiftLocalS centre place entry q first w y :=
  shiftLocalS_of_chainPosInvCoupled' centre place entry q first
    (chainPosInvCoupled'_alongRun centre place entry q first hbg hmatch hsd hx h)

/-- **`needIMW'_le_W` with `H_fourOther` gone.**  Same three branch hypotheses
as `given_globalScanLandings_and_fourOther`, and the boot obligation is a theorem. -/
theorem needBound_without_fourOther {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hbg : H_bgP centre place entry q first w) (hmatch : H_matchP centre place entry q first w)
    (hsd : H_shiftDoneP centre place entry q first w)
    (hChainPosInv2AtOrigin : ChainPosInv' w (st 0).ctl (st 0).vm) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 :=
  needBound_of_shiftLocalS_alongTrace centre place entry q first hw hPreTrace
    (fun i hIndexLeTc => shiftLocalS_alongRun_of_chainPosInvCoupled' centre place entry q first hbg hmatch hsd hChainPosInv2AtOrigin
      (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.base.pre.trace i hIndexLeTc))

end

#print axioms radPack_alongTrace_of_shiftLocalS
#print axioms trailF_alongTrace_of_shiftLocalS
#print axioms needBound_of_shiftLocalS_alongTrace
#print axioms chainPosInvCoupled'_at_idle
#print axioms chainPosInvCoupled'_alongRun
#print axioms shiftLocalS_of_chainPosInvCoupled'
#print axioms shiftLocalS_alongRun_of_chainPosInvCoupled'
#print axioms needBound_without_fourOther

end PalPeg.ShiftLocalRun
