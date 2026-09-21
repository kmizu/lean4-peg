import PalPeg.CloseoutMarksPack
import PalPeg.BranchSupply
import PalPeg.CloseoutFinalFour
import PalPeg.CloseoutFinalVer

/-!
# `given_landingObligationsAlongRun` — 4 分岐義務を run 形に弱めた最上位

`given_globalRun41Landings_and_verifierRun`（`CloseoutFinalVer`、9 前提）の中 4 本
（`H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger`）は
`∀ (c : Control) (s : GalilVM), …` で**任意の状態**を量化していた。
`chainPosInv2_tick` はそれらを自分の `(c, s)` でしか使わないので
（`CloseoutPackRun41` の `LandingObligationsAt` / `chainPosInv2_tick_of_landingObligationsAt` に局所化した）、
run 形の 1 本 `BranchSupply.LandingObligationsAlongRun` に**まとめると同時に弱められる**。

* `landingObligationsAlongRun_of_globalHypotheses` があるので global 4 本を持つ呼び出し側はそのまま乗る。
* **逆は無い**。run 形のほうが真に弱く、放電できるのはこちらだけ
  （`LPackM2.shiftGeom` も chain 側台帳 `ChainPositionLedger` も入力供給も、
  run に沿ってしか存在しない）。

これは束ねただけの `hpack` とは違う: `hpack` は run の事実を**一状態述語**として
書いたので偽になった（`CloseoutPackRefute.hpack_false`）。`LandingObligationsAlongRun` は逆向きで、
一状態述語の族を**run に沿って**量化し直したものなので、`chainPosInv2_of_idle` の
反例に当たらない。

## 本数の誠実な読み方

`given_landingObligationsAlongRun` の Prop 引数は 6 本だが、**`hLandingObligations` は 4 つの義務の束**である。
義務の個数で数えれば `final39`（7 本すべて別々）より多い。
**前進は本数ではなく「global → run 形」の弱化**で、放電できる形になったことである。
正本の最上位は引き続き `given_globalScanLandings`（7 本、束ねていない）とする。

| 定理 | Prop 引数 | 義務の実数 | 偽の前提 |
|---|---|---|---|
| `given_globalScanLandings`（`CloseoutFinalFour`、**正本**） | 7 | 7（global 3 ＋ 他 4） | なし |
| `given_landingObligationsAlongRun`（本ファイル、**放電の作業場**） | 6 | 9（run 形 4 ＋ `hver` ＋ 他 4） | なし |
| `given_globalRun41Landings_and_verifierRun`（`CloseoutFinalVer`） | 9 | 9 | なし |
| `given_consumeAvailEverywhere_FALSE_HYP` | 9 | — | `hav`（`ConsumeAvailRefute.hav_false`） |
| `given_chainPackAtAnyState_andMore_FALSE_HYP` / `final37` | 5 / 4 | — | `hpack`（`CloseoutPackRefute.hpack_false`） |

**全体 build 成功・標準公理のみ・無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalBranch

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
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutShiftFinal PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutFinalW PalPeg.ShiftLocalRun
open PalPeg.CloseoutFinalW PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2
open PalPeg.CloseoutChainPack PalPeg.CloseoutWatchSupply PalPeg.CloseoutFinalS2
open PalPeg.CloseoutFinalPack
open PalPeg.CloseoutVerSide
open PalPeg.CloseoutFinalW3
open PalPeg.CloseoutFinalW4
open PalPeg.CloseoutVerSide PalPeg.CloseoutFinalW3 PalPeg.CloseoutFinalW4
open PalPeg.CloseoutFinalW5 PalPeg.CloseoutWatchSupply
open PalPeg.CloseoutFinalW PalPeg.CloseoutFinalFour PalPeg.CloseoutFinalVer
open PalPeg.CloseoutVerSide PalPeg.BranchSupply PalPeg.CloseoutPackRun41

/-- **`given_globalRun41Landings_and_verifierRun` の中 4 本を run 形 1 本にした最上位。**
Prop 引数 6 本・反証済みゼロ。ただし `hLandingObligations` は 4 義務の束なので、**本数の削減ではなく
「global → run 形」の弱化**である（正本は `given_globalScanLandings`）。

| 前提 | 内容 |
|---|---|
| `hSP` | scan 状態の `ShiftPal`（`CloseoutBundleRun.shiftPal_of_run` が経路） |
| `hme` | `H_marksEntry'`（残差は `WindowInOrigin`、`CloseoutMarksFree`） |
| `hor` | `CycleOracleMC3`（11 葉） |
| `hC` | `H_realizeLIMW'`（局所実現） |
| `hLandingObligations` | **`LandingObligationsAlongRun`** — run の各点で `LandingObligationsAt`（4 分岐義務の run 形） |
| `hver` | `VerRun` — chain の verifier が入力を表現し lag が正規（run 形） |
-/
theorem given_landingObligationsAlongRun (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hLandingObligations : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → LandingObligationsAlongRun centreC placeC entry q first w (st 0))
    (hver : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → VerRun centreC placeC entry q first w (st 0))
    (hCanRightAtAnyScanOrShiftState : ∀ z : GalilScaffoldTop.State GalilVM,
      z.ctl.mode = GalilScaffoldController.Mode.scan ∨
        z.ctl.mode = GalilScaffoldController.Mode.shift →
      GalilScaffoldChainVerifier.canRight z.vm.right)
    :
    RecognizedByTotalPEG PAL :=
  given_needBound entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MW centreC placeC entry q first (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC
    (fun w st _ hw h => needBound_of_landingObligationsAlongRun centreC placeC entry q first hw h
      (by rw [h.base.pre.start]; exact chainPosInv2_of_idle (boot_chain_idle w))
      (hLandingObligations w st h.base.pre.start) (hver w st h.base.pre.start)
      (fun _ z _ => hCanRightAtAnyScanOrShiftState z))

/-- **`given_landingObligationsAlongRun` の `hLandingObligations` から半径台帳を落とした版。**

`LandingObligationsAt.shiftDone` は `canRight s.right` と半径台帳の連言だったが、後者は
`CloseoutRadPack.RadLedger.le`（`position center + value radius ≤ position right`）と
`ScanInvariant.rightPos` だけで出る（`BranchSupply.radiusLe_of_radLedger`）。
`RadLedger` は `CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけで
trace の全点に与えるので、**新規入力ゼロで内部調達できる**。

残る義務は `LandingObligationsAtSansRadiusLedger` の 4 場（`bg` / `matchLand` / `entryLand` / **`shiftCan`**）で、
`shiftCan` は `canRight s.right` のみ。`canRight` の経路は
`CloseoutClockFront.canRight_of_run`（front ポテンシャル ＋ 長さ予算、mode 条件なし）で、
右ヘッドの `Represents`/`focus ≠ none` は shift 相では `LPackM2.shiftGeom` の `RRep` が持つ。 -/
theorem given_landingObligationsSansRadiusLedger (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      LandingObligationsAlongTraceSansRadiusLedger centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM)
      (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc) :
    RecognizedByTotalPEG PAL :=
  given_needBound entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MW centreC placeC entry q first (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC
    (fun w st Tc hw h => needBound_of_landingObligationsSansRadiusLedger centreC placeC entry q first hw h
      (by rw [h.base.pre.start]; exact chainPosInv2_of_idle (boot_chain_idle w))
      (hres w st Tc h) (hChainVerifierSupply w st Tc hw h)
      (canRightAtScanOrShift_alongTrace centreC placeC entry q first hw h))


/-- **The canonical pre-loaded trace of every non-empty word**, from the cycle oracle on packed
runs.  The boot landing is unconditional. -/
theorem canonicalPreTrace_exists (entry q : ℕ) (first : Fin 9)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry)
      (PalPeg.CloseoutCheckW.ReportOnPackedRun centreC placeC entry q first) w)
    (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc ∧
        PalPeg.CloseoutCheckW.CanonTrace entry w st Tc ∧
        (∀ m, 1 ≤ m → m ≤ w.length →
          (st (Tc m)).ctl.mode = PalPeg.GalilScaffoldController.Mode.scan) ∧
        ∀ m, 1 ≤ m → m ≤ w.length →
          PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first w
            (st (Tc m)).ctl (st (Tc m)).vm :=
  PalPeg.CloseoutCheckW.preTraceOnPackedRun_exists centreC placeC entry q first
    (h_bootRefreshedIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    hor w hw


/-- **The lookahead need along a pre-loaded trace**: before checkpoint `m+1` a tick needs at
most `m+1` letters.  The chain position invariant at the origin is that of the boot state. -/
theorem needBound_alongPreTrace (entry q : ℕ) (first : Fin 9)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM)
      (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    {w : List (Fin 2)} {st : ℕ → GalilScaffoldTop.State GalilVM} {Tc : ℕ → ℕ}
    (hw : 0 < w.length)
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 :=
  needBound_of_scanLandingObligations centreC placeC entry q first hw hPreTrace
    (by rw [hPreTrace.base.pre.start]; exact chainPosInv2_of_idle (boot_chain_idle w))
    (hres w st Tc hPreTrace) (hChainVerifierSupply w st Tc hw hPreTrace)

/-- **`shiftDone` 義務を完全に放電した最上位。**

`LandingObligationsAt.shiftDone` の 2 節はどちらも新規入力ゼロで出る：

* 半径台帳 ← `CloseoutRadPack.RadLedger.le` ＋ `ScanInvariant.rightPos`
  （`RadLedger` は `CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` から trace 全点に）
* `canRight s.right` ← trace 予算。終端の報告点 `ReportPointAt.atPrefix`
  （`position right = 2|w| − 1`）から front ポテンシャルの単調性で**後ろ向き**に伝播し
  （`front_tick_mono`、`position right ≤ front`）、shift 相の右ヘッドの
  `Represents`/`focus ≠ none` は `LPackM2.shiftGeom` の `RRep` が持つ。
  1 手目以降 `mode ≠ init` は定理（`tick_target_mode_ne_init`: `Tick` に `mode := .init` へ行く
  構成子が無い）なので `frontPack_trace` が使える。

残る義務は `ScanLandingObligationsAt` の **3 場**（`bg` / `matchLand` / `entryLand`）と `hver`。 -/
theorem given_scanLandingObligations (entry q : ℕ) (first : Fin 9)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry)
      (PalPeg.CloseoutCheckW.ReportOnPackedRun centreC placeC entry q first) w)
    (hC : H_realizeCanonical centreC placeC entry q first)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM)
      (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc) :
    RecognizedByTotalPEG PAL :=
  given_preTraceIMW_on entry q first (PalPeg.CloseoutCheckW.CanonTrace entry)
    (fun w hw => by
      obtain ⟨st, Tc, hpreTrace, hcanonical, -⟩ := canonicalPreTrace_exists entry q first hor w hw
      exact ⟨st, Tc, hpreTrace, hcanonical⟩)
    hC
    (fun w st Tc hw h => needBound_alongPreTrace entry q first hres hChainVerifierSupply hw h)

#print axioms given_scanLandingObligations

#print axioms given_landingObligationsSansRadiusLedger

#print axioms given_landingObligationsAlongRun

end PalPeg.CloseoutFinalBranch
