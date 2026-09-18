import PalPeg.PalInPeg
import PalPeg.BranchSupply

/-!
# `PalInPeg.unconditional` — 目標そのもの。穴は `axiom` で明示する

**これが目標の形**: `RecognizedByTotalPEG PAL` を**前提ゼロ**で（＝閉じた項として）持つ。
いま足りない 6 個の義務を `axiom` として明示し、`#print axioms unconditional` を
そのまま TODO リストにする。

```
#print axioms PalPeg.PalInPeg.unconditional
-- 標準 3 公理（propext / Classical.choice / Quot.sound）だけになったら証明完了
```

`PalPeg/Axioms.lean` に `#guard_msgs in #print axioms unconditional` を置いてあるので、
**1 個外すたびに guard が壊れて更新を強制される**（ラチェット）。逆に、うっかり
新しい穴を開けても guard が壊れるので気づける。

コウタの指示（2026-09-19）:
* 「unconditional はつくっておいて、前提の and でうめりゃいいのでは。その前提を
  いったん axiom にしといて外していく」
* 「トップダウンにまずそれを書いておいてビルド通すために前提をいったん axiom に
  しておく。で、検証したい前提ごとに axiom をはずして全部外せたら証明完了」

## 7 個の義務と現状（詳細は `CLAUDE_RESUME.md` / `PART_INDEX.md` §2a）

| axiom | 内容 | 現状 |
|---|---|---|
| `obligation_shiftPalAtScanStates` | scan 状態で `ShiftPal` | `CloseoutBundleRun.shiftPal_of_run` が経路。残差は `ChainPositionInvariantWithShiftPhase`(run) ＋ `H_readsShift` ＋ `H_freshShift` ＋ `periodOnly = false` 分岐 |
| `obligation_marksEntry` | `H_marksEntry'` | `CloseoutMarksFree.marksInv'_of_marksRun` が経路。残差は `WindowInOrigin`（run 形、copy 状態）＋ `EntryCounters`（scan 状態） |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge` ＋ `CloseoutOracle8`。11 葉 |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現） | **producer なし。最大の未知**（5 機械の鎖の 2→3 段） |
| `obligation_backgroundLandingPayload` | `H_BackgroundLandingPayload` | `CloseoutPackRun38.posPayload_background` → `H_bgRes`。trace 形なら `BranchSupply.backgroundLanding_of_supply` で 4 供給に分解し、`hRightHeadRep` はタダ、`hVerifierRep`/`hLagCan` は `VerRun`、残るは `BgStartP2`（→ `CentreLedger` → `radiusExact`） |
| `obligation_matchLandingPayload` | `H_MatchLandingPayload` | `CloseoutPackRun38` (:221) → `H_matchRes` |
| `obligation_shiftExitPayload` | `H_ShiftExitPayload` | `CloseoutPackRun38` (:316、恒等) → `CloseoutShiftDoneP.posPayload_of_shiftGeom` で `ShiftGeom`（`LPackM2` にありタダ）＋ `ChainSideAt` に分割 |

**無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false

namespace PalPeg.PalInPeg

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.GalilFinalAssembly2 PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackW PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun16 PalPeg.CloseoutFinalW PalPeg.CloseoutPackRun34
open PalPeg.GalilFinalAssembly (boot)

/-! ## 未証明の義務（外すべき `axiom`）-/

/-- **(OBLIGATION)** scan 状態で `ShiftPal`。 -/
axiom obligation_shiftPalAtScanStates (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm

/-- **(OBLIGATION)** `H_marksEntry'`。 -/
axiom obligation_marksEntry (entry q : ℕ) (first : Fin 9) :
    ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first

/-- **(OBLIGATION)** `CycleOracleMC3`。 -/
axiom obligation_cycleOracle (entry q : ℕ) (first : Fin 9) :
    ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w

/-- **(OBLIGATION)** 局所実現 `H_realizeLIMW'`。最大の未知。 -/
axiom obligation_localRealization (entry q : ℕ) (first : Fin 9) :
    H_realizeLIMW' centreC placeC entry q first

/-- **(OBLIGATION)** trace の各点での 3 つの scan landing 義務
（`bg` / `matchLand` / `entryLand`）。**trace 形なので放電可能**（global 形の
`H_BackgroundLandingPayload` 等は材料が run に沿ってしか無いので原理的に落ちない）。
`shift_done` 出口の義務は既に完全放電済み（半径台帳は `RadLedger`、
`canRight` は trace 予算）。 -/
axiom obligation_scanLandingObligationsAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc

/-- **(OBLIGATION)** chain の verifier が入力を表現し lag が正規であること（run 形）。
`ConsumeAvail` を全状態に量化した版は**偽**（`ConsumeAvailRefute.hav_false`）なので、
run 形の `VerRun` がその正しい代替。 -/
axiom obligation_verifierRunAlongRun (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM),
      st 0 = boot w → PalPeg.CloseoutVerSide.VerRun centreC placeC entry q first w (st 0)

/-! ## 目標 -/

/-- **目標**: `PAL ∈ PEG` を前提ゼロで。いまは上の 7 個の `axiom` に依存している。
`#print axioms unconditional` が標準 3 公理だけになったら証明完了。 -/
theorem unconditional : RecognizedByTotalPEG PAL :=
  given_scanLandingObligations 0 0 0
    (obligation_shiftPalAtScanStates 0 0 0)
    (obligation_marksEntry 0 0 0)
    (obligation_cycleOracle 0 0 0)
    (obligation_localRealization 0 0 0)
    (obligation_scanLandingObligationsAlongTrace 0 0 0)
    (obligation_verifierRunAlongRun 0 0 0)

#print axioms unconditional

end PalPeg.PalInPeg
