import PalPeg.PalInPeg
import PalPeg.BranchSupply

/-!
# `PalInPeg.unconditional` — 目標そのもの。穴は `axiom` で明示する

**これが目標の形**: `RecognizedByTotalPEG PAL` を**前提ゼロ**で（＝閉じた項として）持つ。
いま足りない 8 個の原子的な義務を `axiom` として明示し、`#print axioms unconditional` を
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
| `obligation_matchLanding_alongTrace` | `scan_match` 着地 | `CloseoutPackRun49.matchRes2_of_lpackM3`（`LPackM3` は §5e で運べる）＋ `h_matchP2_of_target`。残差は `MatchRest` の 3 場: `repV`（←`VerRun`）/ `repVmid`（verifier 1 歩先、`right_word` で出るはず）/ `replayPay`（replaying 時の payload）。`canRNext` は**反証済みで削除**（`MatchRestRefute`） |
| `obligation_shiftEntryLanding_alongTrace` | `scan_shift` 入口 | `beginShiftVM'` は `immediate`（1 consume）を当てる。`ShiftPhaseChainLedger` の確立 |
| `obligation_chainBackLag_alongTrace` | chain `.back` 相の lag 形状 | **producer なし**。`LagCan` は `.watch` 相のみ。`.back` は `ChainStep.copyEnd` が `.copy` の lag を持ち込むところで確立される。`CloseoutChainPack` / `CloseoutChainSideR` に同名の場があるのでその証明を参照 |
| `obligation_shiftExitLedger_alongTrace` | `shift_done` での `CentreLedger` | 3 節のうち `canRight center` / `Sane center` は §5b でタダ。残るは等式 `radiusExact`。scan 状態では `LPackM3` からタダなので、**shift 相へ運ぶ**のが仕事: `beginShiftVM` は center/radius/right を触らず（§5d）、`shiftTick` は center +1・radius −1・right 不変で保存する。side condition は `canRight s.center`（shift 相では `CentreRep` が無いので要調達）と `0 < value s.radius`（`RadLedger.shiftBud` ＋ `remainingPos` から出る） |
| `obligation_rewindMargin_alongTrace` | rewind 相の `2 ≤ position left` | **producer なし**。`LPackM2.centreOrder` は `position left ≤ position center`（上界）なので別物。CLAUDE.md は「`CentreMargin` 1 葉に集約」と記録 |
| `obligation_marksEntry` | `H_marksEntry'` | `CloseoutMarksFree.marksInv'_of_marksRun`（origin）＋ `CloseoutMarksPack.bigPack2MG7W''_tick_M`（tick）。残差は `WindowInOrigin`（run 形、copy 状態）＋ `EntryCounters`（scan 状態）＋ 側条件 `first ≠ 4`。**`EntryCounters` は `RadiusRep`（＝`radiusExact` と同内容）を含むので `shiftExitLedger` と材料を共有する** |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`。11 葉（CLAUDE.md §3） |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現） | **producer なし**（5 機械の鎖の 2→3 段）。難易度は宣言しない——`LagCan` / `CentreRep` と同じ「切り方の誤り」の可能性が高い |

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

/-- **(OBLIGATION)** 局所実現 `H_realizeLIMW'`。producer が無い。 -/
axiom obligation_localRealization (entry q : ℕ) (first : Fin 9) :
    H_realizeLIMW' centreC placeC entry q first

/-! ### scan landing 義務 — 原子に分解した 5 つ（すべて trace 形）

束ねると「公理を 1 個外す」が測れなくなるので 1 場ずつに分けた。
**すべて trace 形**（`PreTraceIMW` を取り `st j` で述べる）である点が本質:
状態全体に量化した global 形は、放電の材料（`LPackM2`・chain 側台帳・入力供給）が
run に沿ってしか存在しないので**原理的に落ちない**。`hpack` / `hav` が偽だったのと
同じ病。

`bg` 場（`scan_wait` / `scan_count` 着地）は放電済みなのでここに無い。 -/

/-! `MatchRes2` の残差 `MatchRest` は**放電済み**
（`BranchSupply.matchRest_alongTrace`、新規入力は `CentreMargin` だけ）。

4 場すべてが消えた経緯:

| 場 | 決着 |
|---|---|
| `canRNext` | **偽**（`MatchRestRefute.matchRest_alongTrace_false`）。着地側の 1 歩分に切り直し |
| `repV` | `CloseoutVerSide.VerRun` の第 1 成分そのもの |
| `replayPay` | `ChainPositionInvariantWithShiftPhase.payload` の guard を `ScanNR` から `mode = scan` へ広げたら源で両 replay 分岐が出た |
| `repVmid` | `ChainVerifierRepresents`（chain の verifier が 3 相すべてで入力を表現）を 1 手進めるだけ |

`ChainVerifierRepresents` の側条件はゼロ。`right` は入力端で no-op なので
（`representsAfterRight_free`）`canRight` の供給が一切要らず、誕生の
`Represents s.center.head w` だけが外部入力で、それは `HeadsRepresent.centre`。 -/

/-- **(OBLIGATION)** rewind 相での中心の余裕
`r + pairOff c + 2 ≤ position s.center`（trace 形）。

もとは `RewindMarginAt`（`2 ≤ position left`）だったが、`CloseoutPackRun13` の
`rcouple_of_run`（**葉なし**）で `RCouple` が trace 全域でタダになるので、
`rewindMargin_of_centreMargin` によりこの 1 葉に縮んだ
（`BranchSupply.rewindMarginAt_alongTrace`）。

`position p = if p.gap then 2·|left| else 2·|left| − 1` なので、これは
**リストの長さの算術**であって幾何ではない。内容は「rewind が中心を使い切る前に
FIRST で止まる」＝ marks テープと入力ヘッドの整合なので、
`obligation_marksEntry` と材料を共有する。 -/
axiom obligation_centreMargin_alongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, j ≤ Tc w.length → PalPeg.CloseoutPackRun13.CentreMargin (st j).ctl (st j).vm

/-! chain の verifier 側供給（旧 `obligation_verifierRunAlongRun`）は**放電済み**
（`BranchSupply.chainVerifierSupply_alongTrace`、新規入力は `CentreMargin` だけ）。

`VerRun` は `Steps` で到達可能な**任意の**状態に量化していたので trace からは出なかった
（`Tick` は決定的でない）。trace の点で述べた `ChainVerifierSupplyAlongTrace` に
切り直すと、`VerRep` は `ChainVerifierRepresents` の `.watch` 場、
`LagCan` は `ChainLagCanonical` の `.watch` 場で、どちらも搬送済み。

**過剰量化の 10 例目。run 形と trace 形は別物で、trace 形のほうが真に弱い。** -/

/-! ## 目標 -/

/-- **目標**: `PAL ∈ PEG` を前提ゼロで。いまは上の 5 個の `axiom` に依存している。
`#print axioms unconditional` が標準 3 公理だけになったら証明完了。 -/
theorem unconditional : RecognizedByTotalPEG PAL :=
  given_scanLandingObligations 0 0 0
    (obligation_shiftPalAtScanStates 0 0 0)
    (obligation_marksEntry 0 0 0)
    (obligation_cycleOracle 0 0 0)
    (obligation_localRealization 0 0 0)
    (fun w st Tc hPreTraceIMW =>
      PalPeg.BranchSupply.scanLandingObligations_alongTrace_of_matchRest centreC placeC 0 0 0
        hPreTraceIMW
        (fun x hBig hScanNR => obligation_shiftPalAtScanStates 0 0 0 w x hBig hScanNR)
        (PalPeg.BranchSupply.shiftExitLedgerAt_alongTrace centreC placeC 0 0 0
          hPreTraceIMW (PalPeg.BranchSupply.marksInv_alongTrace centreC placeC 0 0 0
            hPreTraceIMW.base.pre (obligation_marksEntry 0 0 0 w)))
        (PalPeg.BranchSupply.marksInv_alongTrace centreC placeC 0 0 0 hPreTraceIMW.base.pre
          (obligation_marksEntry 0 0 0 w))
        (obligation_centreMargin_alongTrace 0 0 0 w st Tc hPreTraceIMW)
        (PalPeg.BranchSupply.matchRest_alongTrace centreC placeC 0 0 0 hPreTraceIMW
          (PalPeg.BranchSupply.marksInv_alongTrace centreC placeC 0 0 0 hPreTraceIMW.base.pre
            (obligation_marksEntry 0 0 0 w))))
    (fun w st Tc hw hPreTraceIMW =>
      PalPeg.BranchSupply.chainVerifierSupply_alongTrace centreC placeC 0 0 0 hw hPreTraceIMW
        (PalPeg.BranchSupply.marksInv_alongTrace centreC placeC 0 0 0 hPreTraceIMW.base.pre
          (obligation_marksEntry 0 0 0 w))
        (hPreTraceIMW.base.tc1 ▸ hPreTraceIMW.base.pre.mono 1 w.length hw le_rfl))

#print axioms unconditional

end PalPeg.PalInPeg
