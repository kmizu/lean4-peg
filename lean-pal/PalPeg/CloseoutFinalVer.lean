import PalPeg.CloseoutFinalW5

/-!
# `given_globalRun41Landings_and_verifierRun` — `hfour` / `hav` / `hpack` がすべて消えた最上位

`given_globalScanLandings_and_fourOther`（`CloseoutFinalW`、8 前提・反証済みゼロ）が正直な最上位だったが、
その `hfour : H_FourSemiperiodsLeDistance` は**既存の部品で消える**：`CloseoutPackRun41.ChainPositionInvariantWithShiftPhase` は
`Coupled'`（Run40）を場に持ち、`four_of_other'`（`CloseoutPackRun40:368`）が
`H_FourSemiperiodsLeDistance` の結論そのものを与えるので、`watchShiftS_of_chainPosInv2` は `hfour` を
取らない。

ところが `hfour` を落とした既存の 2 経路はどちらも**偽の前提**を代わりに取っていた：

| 定理 | 前提数 | 偽の前提 | 機械検査 |
|---|---|---|---|
| `final31`（`CloseoutFinalS2`） | 9 | `hav`（`ConsumeAvail` を全状態に量化） | `ConsumeAvailRefute.hav_false` |
| `final36`（`CloseoutFinalW3`） | 5 | `hpack`（`ChainPositionInvariantWithShiftPhase → ChainPack`） | `CloseoutPackRefute.hpack_false` |
| `final37`（`CloseoutFinalW4`） | 4 | 同上 | 同上 |

`CloseoutWatchSupply` が `ConsumeAvail` を 4 つの局所供給事実に分解し、
`CloseoutVerSide` がそのうち残る 2 つを**run 形**の `VerRun` にまとめ
（`chainPosInv2_of_idle` の反例に当たらない形）、`needIMW'_le_W4` で `hpack` を外した。
`CloseoutFinalW5.given_bootOracleRealize_and_verifierRun` はそれを受けているが、**最上位が張られていなかった。**

本ファイルがそれを張る。残り 9 前提は**すべて run 形または状態局所**で、反証済みは無い。

| 前提 | 内容 |
|---|---|
| `hSP` | scan 状態の `ShiftPal`（`CloseoutBundleRun.shiftPal_of_run` が経路） |
| `hme` | `H_marksEntry'` |
| `hor` | `CycleOracleMC3` |
| `hC` | `H_realizeLIMW'`（局所実現） |
| `hbgP` `hmatchP` `hentry` `hsdP` | `chainPosInv2_tick` の 4 分岐（`CloseoutPackRun48` に放電器あり） |
| `hver` | `VerRun`（chain の verifier が入力を表現し lag が正規、run の scan 各点で） |

**前提数は 8 → 9 で増えているが、偽の前提がゼロのまま `hfour` が消えた。**
`hfour`（数値的結合）が `hver`（入力供給、既に解けている `repR` と同型）に置き換わった
ことが前進で、数字はこれから `CloseoutPackRun48` の 4 放電器で戻す。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalVer

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

/-- **`given_globalScanLandings_and_fourOther` から `H_FourSemiperiodsLeDistance` が消えた最上位。9 前提・反証済みゼロ。**

`hfour` は `ChainPositionInvariantWithShiftPhase` が自前で閉じるので不要。`final31` の `hav` と
`final36`/`final37` の `hpack` はどちらも偽なので、その代わりに `CloseoutVerSide` の
**run 形** `VerRun` を取る。 -/
theorem given_globalRun41Landings_and_verifierRun (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hbgP : ∀ w : List (Fin 2), H_BackgroundLandingChainLedger centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_MatchLandingChainLedger centreC placeC entry q first w)
    (hentry : ∀ w : List (Fin 2), H_ShiftEntryChainLedger centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_ShiftExitRadiusLedger centreC placeC entry q first w)
    (hver : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → VerRun centreC placeC entry q first w (st 0)) :
    RecognizedByTotalPEG PAL :=
  given_bootOracleRealize_and_verifierRun entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MW centreC placeC entry q first (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC hbgP hmatchP hentry hsdP
    (fun w st hst => by rw [hst]; exact chainPosInv2_of_idle (boot_chain_idle w))
    hver

#print axioms given_globalRun41Landings_and_verifierRun

end PalPeg.CloseoutFinalVer
