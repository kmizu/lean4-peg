import PalPeg.PalInPeg
import PalPeg.BranchSupply

/-!
# `PalInPeg.unconditional` — 目標そのもの。穴は `axiom` で明示する

**これが目標の形**: `RecognizedByTotalPEG PAL` を**前提ゼロ**で（＝閉じた項として）持つ。
いま足りない 10 個の原子的な義務を `axiom` として明示し、`#print axioms unconditional` を
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

## 10 個の原子的義務と、それぞれの経路（2026-09-19 実測）

| axiom | 内容 | 経路と残り |
|---|---|---|
| `obligation_shiftPalAtScanStates` | scan 状態で `ShiftPal` | `CloseoutBundleRun.shiftPal_of_run`。残差は `ChainPositionInvariantWithShiftPhase`(run) ＋ `H_readsShift` ＋ `H_freshShift` ＋ `periodOnly = false` 分岐。**global 形なので run 形に書き換えてから使う** |
| `obligation_verifierRunAlongRun` | `VerRun`（verifier が入力を表現、lag 正規） | `chainPos_step_of_supply` が要求する 4 局所事実の残り 2 つ。`ConsumeAvail` の全状態版は偽（`ConsumeAvailRefute.hav_false`） |
| `obligation_matchLanding_alongTrace` | `scan_match` 着地 | `CloseoutPackRun49.matchRes2_of_lpackM3`（`LPackM3` は §5e で運べる）＋ `h_matchP2_of_target`。残差は `MatchRest` の 4 場: `repV`（←`VerRun`）/ `repVmid`（verifier 1 歩先、`right_word` で出るはず）/ `replayPay`（replaying 時の payload）/ `canRNext`（`canRight (right right)`、`canRight_next_of_bound` に `m < w.length` の**厳密**予算が要る） |
| `obligation_shiftEntryLanding_alongTrace` | `scan_shift` 入口 | `beginShiftVM'` は `immediate`（1 consume）を当てる。`ShiftPhaseChainLedger` の確立 |
| `obligation_chainBackLag_alongTrace` | chain `.back` 相の lag 形状 | **producer なし**。`LagCan` は `.watch` 相のみ。`.back` は `ChainStep.copyEnd` が `.copy` の lag を持ち込むところで確立される。`CloseoutChainPack` / `CloseoutChainSideR` に同名の場があるのでその証明を参照 |
| `obligation_shiftExitLedger_alongTrace` | `shift_done` での `CentreLedger` | 3 節のうち `canRight center` / `Sane center` は §5b でタダ。残るは等式 `radiusExact`。scan 状態では `LPackM3` からタダなので、**shift 相へ運ぶ**のが仕事: `beginShiftVM` は center/radius/right を触らず（§5d）、`shiftTick` は center +1・radius −1・right 不変で保存する。side condition は `canRight s.center`（shift 相では `CentreRep` が無いので要調達）と `0 < value s.radius`（`RadLedger.shiftBud` ＋ `remainingPos` から出る） |
| `obligation_rewindMargin_alongTrace` | rewind 相の `2 ≤ position left` | **producer なし**。`LPackM2.centreOrder` は `position left ≤ position center`（上界）なので別物。CLAUDE.md は「`CentreMargin` 1 葉に集約」と記録 |
| `obligation_marksEntry` | `H_marksEntry'` | `CloseoutMarksFree.marksInv'_of_marksRun`（origin）＋ `CloseoutMarksPack.bigPack2MG7W''_tick_M`（tick）。残差は `WindowInOrigin`（run 形、copy 状態）＋ `EntryCounters`（scan 状態）＋ 側条件 `first ≠ 4`。**`EntryCounters` は `RadiusRep`（＝`radiusExact` と同内容）を含むので `shiftExitLedger` と材料を共有する** |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`。11 葉（CLAUDE.md §3） |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現） | **producer なし。最大の未知**（5 機械の鎖の 2→3 段） |

### 放電済み（この近傍のタダ飯）

`bg` 場（`scan_wait`/`scan_count` 着地）、`shift_done` の半径上界と `canRight`、
`Extra7.scanAvail`（＝`hee`/`het`）、`AuxPack`（1 手目以降）、`LPackM3` の運搬、
`LTickLeaves3.initLedger` / `.replayLedger`、`CentreLedger` の `canRight`/`Sane` 2 節、
`CentreLive`、`FrontPack`、`Coupled`、`CopyPack`。

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

/-! ### scan landing 義務 — 原子に分解した 5 つ（すべて trace 形）

束ねると「公理を 1 個外す」が測れなくなるので 1 場ずつに分けた。
**すべて trace 形**（`PreTraceIMW` を取り `st j` で述べる）である点が本質:
状態全体に量化した global 形は、放電の材料（`LPackM2`・chain 側台帳・入力供給）が
run に沿ってしか存在しないので**原理的に落ちない**。`hpack` / `hav` が偽だったのと
同じ病。

`bg` 場（`scan_wait` / `scan_count` 着地）は放電済みなのでここに無い。 -/

/-- **(OBLIGATION)** `scan_match` 着地の位置台帳（trace 形）。 -/
axiom obligation_matchLanding_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length →
        PalPeg.BranchSupply.MatchLandingAt centreC placeC entry q first w (st j).ctl (st j).vm

/-- **(OBLIGATION)** `scan_shift` 入口の shift 相台帳（trace 形）。 -/
axiom obligation_shiftEntryLanding_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length →
        PalPeg.BranchSupply.ShiftEntryLandingAt centreC placeC entry q first w
          (st j).ctl (st j).vm

/-- **(OBLIGATION)** chain の `.back` 相の lag 形状（trace 形）。 -/
axiom obligation_chainBackLag_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length → PalPeg.BranchSupply.ChainBackLagAt (st j).vm

/-- **(OBLIGATION)** `shift_done` での `CentreLedger`（trace 形）。 -/
axiom obligation_shiftExitLedger_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length →
        PalPeg.BranchSupply.ShiftExitLedgerAt centreC placeC entry q first w
          (st j).ctl (st j).vm

/-- **(OBLIGATION)** rewind 相での `2 ≤ position left`（trace 形）。 -/
axiom obligation_rewindMargin_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length → PalPeg.BranchSupply.RewindMarginAt (st j).ctl (st j).vm

/-- **(OBLIGATION)** chain の verifier が入力を表現し lag が正規（run 形）。 -/
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
    (fun w st Tc hPreTraceIMW =>
      PalPeg.BranchSupply.scanLandingObligations_alongTrace_of_atoms centreC placeC 0 0 0
        hPreTraceIMW
        (fun x hBig hScanNR => obligation_shiftPalAtScanStates 0 0 0 w x hBig hScanNR)
        (obligation_verifierRunAlongRun 0 0 0 w st hPreTraceIMW.base.pre.start)
        (obligation_chainBackLag_alongTrace 0 0 0 w st Tc hPreTraceIMW)
        (obligation_shiftExitLedger_alongTrace 0 0 0 w st Tc hPreTraceIMW)
        (obligation_rewindMargin_alongTrace 0 0 0 w st Tc hPreTraceIMW)
        (obligation_matchLanding_alongTrace 0 0 0 w st Tc hPreTraceIMW)
        (obligation_shiftEntryLanding_alongTrace 0 0 0 w st Tc hPreTraceIMW))
    (obligation_verifierRunAlongRun 0 0 0)

#print axioms unconditional

end PalPeg.PalInPeg
