# PART_INDEX — どこにどの部品があるか

> **2026-09-19 更新: 地図の正本は Lean 側に移した。**
> `markdown の索引は黙って腐る`（今日それで 3 回失敗した）ので、在り処の正本は
> **カーネルが検査する 2 本**にした。名前が動けば build が壊れる。
>
> * **`PalPeg/Canonical.lean`** — 正本の鎖（`pal_in_peg_final30` の閉包 526 本）の
>   意味のある別名。番号名（`final30` / `PackRun49` / `Oracle8`）はここで引ける。
> * **`PalPeg/Workbench.lean`** — 作ったが未配線の 64 本の根（閉包 583 本）。
>   **主定理との関係を層ごとに明記**してある。
>
> このファイルに残すのは、markdown でしか書けないもの（検索コマンド、反証の在り処、
> 数え直しの記録）だけ。**部品を探すときはまず上の 2 本を読む。**


**作成日**: 2026-09-19。**作成理由**: `PalPeg/` は 1142 ファイルあり、名前を思い出して
`grep` で歩く運用では**既にある部品を見落とす**。実際に見落とした：

- `CloseoutTerminalN.roundStepC_of_alignN`（`MatchTickN` を取る消費者）は既に存在したのに、
  「配線が必要」と書いていた。
- `CloseoutMarksFree.marks_steps_free`（`H_marksEntry'` を不要にする）も既に存在した。
- **`CloseoutPackRun49`（`LPackM3`）は未登録のまま放置されていた。**`CentreLedger` を
  run に沿って運ぶ部品で、「中心台帳は `ChainPack` にしか無い」と書いたのは誤りだった。

**この索引は「読んだ結果」ではなく「在り処」を記録する。** 内容の正しさは各ファイルの
`#print axioms` と全体 build で確認する。

## 0. 検索コマンド（索引が古い可能性に備えて）

```sh
cd lean-pal
# 未登録モジュール（build に出てこない = grep しても通っているとは限らない）
ls PalPeg/*.lean | sed 's|PalPeg/||; s|\.lean$||' | sort > /tmp/e.txt
grep '^import PalPeg\.' PalPeg.lean | sed 's|^import PalPeg\.||' | sort > /tmp/r.txt
comm -23 /tmp/e.txt /tmp/r.txt
# ある名前の producer を全ファイルから
grep -rn "<名前>" PalPeg/*.lean | grep -E 'theorem|def |structure '
# False を結論とする定理の全列挙（反証の在り処）
grep -rn ": False" PalPeg/*.lean
```

## 1. 最上位の定理

`pal_in_peg_final*` は **47 本**ある。番号は「いつ書いたか」であって「何であるか」ではない。
2026-09-19 に前提を数え直した結果（以前「正本は `final30`」と書いたが、`final31`〜`final36`
を確認していなかった。以下は確認済み）：

| 定理 | ファイル | 前提数 | 反証済みを含むか |
|---|---|---|---|
| **`pal_in_peg_final30`** | `CloseoutFinalW` | **8**（`hSP` `hme` `hor` `hC` `hfour` `hbgP` `hmatchP` `hsdP`） | **なし** ← **正本** |
| `pal_in_peg_final31` | `CloseoutFinalS2` | 9（`hfour` が消え `hentry` ＋ `hav` が増えた） | なし |
| `pal_in_peg_final33` | `CloseoutFinalPack` | 8 | **2 つ**（`hpack`、`hbudget` = `ScanBudget`） |
| `pal_in_peg_final36` | `CloseoutFinalW3` | **5**（`hSP` `hme` `hor` `hC` `hpack`） | 1 つ（`hpack`） |
| `pal_in_peg_final37` | `CloseoutFinalW4` | 4（`hSP` `hor` `hC` `hpack`） | 1 つ（`hpack`） |
| `pal_in_peg_final5MW4` | `CloseoutFinalW5` | `final5MW3` の `hpk` を `VerRun` に置換 | 通る |

**8 未満にする道**: `final36` は 5 前提で偽は `hpack` 1 本だけ。ただし `final36` は
`hpack` から 4 供給（`H_bgP2` / `H_matchP2` / `H_shiftEntry2` / `H_shiftDoneRad2`）を
導いており、それらは `∀ c s` 量化。`LPackM3` は**特定の状態**で `MatchRes2` を出すので
`∀ c s` には届かない。`final31` はその 4 供給を前提として持つので 9 本になる。
**したがって 8 未満にするには 4 供給を run 形（`∀ m z, Steps … m x z → …`）にする
threading が必要で、それが残っている本体。**

## 1b. 依存閉包（2026-09-19 実測）

| 指標 | 本数 |
|---|---|
| 実在モジュール | 1143 |
| **正本 `final30` の推移的 import 閉包** | **526** |
| 閉包の外 | 617 |
| `PalPeg.lean` 登録 | 1101 |
| 登録されていて閉包の外 | 583 |

つまり正本が使うのは 526 本で、登録済み 1101 本のうち 583 本は正本に効かない。
20 分の全体 build の半分以上が正本外。**ただし閉包の外にも健全で有用なものがある**
（`CloseoutPackRun49` / `CloseoutWatchRound53` / `CloseoutRealize1` はそこから回収した）。
登録を外すなら、外す前にここに在り処を記録すること。

## 2. `hSP`（`ShiftPal`）の鎖

| 部品 | 在り処 | 状態 |
|---|---|---|
| `ShiftPal` の定義 | `CloseoutPackRun29:87` | — |
| 束から `ShiftPal` | `CloseoutRoundBundle.shiftPal_of_roundBundle` | 証明済み |
| 束が idle で成立 | `CloseoutBundleRun.roundBundle_of_idle` | 証明済み |
| 束が run を運ばれる | `CloseoutBundleRun.roundBundle_steps_B`（`ChainPosInv2` 不要、`AuxPack` で足りる） | 証明済み |
| run から `ShiftPal` | `CloseoutBundleRun.shiftPal_of_run_B` | 証明済み |
| `H_readsShift` | `CloseoutReadsOrigin.h_readsShift_of_originAt` / `_of_originShift` / `_of_rounds` | `OriginShift` に還元 |
| `OriginAt` / `Entry` 運搬 | `CloseoutOriginAt`, `CloseoutOriginRounds.originAt_of_rounds`, `CloseoutRoundSeg` | 証明済み |
| 第 1 ラウンド | `GalilScaffoldTopFirstRound.first_round` | **葉なしの定理**（run データを取る） |
| `Rounds … 1` の構成 | `CloseoutWatchRound9.roundOne_of_segRun`, `CloseoutShiftMismatch.roundOne_of_segRun_M` | 入力: `ChainTickable` / `RoundDataC` / `hland` |
| `ShiftAtMismatchM` | `CloseoutMismatchCompare.shiftAtMismatchM_of_round` | **証明済み** |
| `WatchClosedC` | `CloseoutMismatchCompare.watchClosedC_proved` | **証明済み** |
| `RoundDataC` の残差 | `CloseoutWatchRound2:132`（`MatchTickC`）→ `CloseoutMatchTickN.MatchTickN`（証明済み）→ 消費者 `CloseoutTerminalN.roundStepC_of_alignN` | 配線済み |
| `LandingReadyC`（`hland`） | `CloseoutLandingRound`（7 定理） | `canRight` / `ChainReady` / `distance` 非負まで出た |
| `ChainTickable`（`hready`） | `GalilChainTickable`（`chainOk_tick`, `chainTickable_unless_break`, `no_break_during_replay`）／`CloseoutTickFalse.chainOk_tick_false` | 命題が不適切。置換は `WatchOk` インスタンス相対で、インスタンスは未発見・充足可能性**未決** |
| 背景 tick の恒等性 | `CloseoutMismatchCompare.chainTick_false_idle`, `chainStep_watch_of_lagZero` | **証明済み**（lag ゼロなら `WatchOk` 不要） |
| `ShiftRun` の存在 | `CloseoutShiftRun.shiftRun_exists` / `_entry` / `_round` | **証明済み** |

## 2b. `hfour`（`H_fourOther`）— **放電済み**（2026-09-19、`pal_in_peg_final39`）

| 部品 | 在り処 | 状態 |
|---|---|---|
| `H_fourOther` の定義 | `CloseoutPackRun34:342` | 前提として数えられていた |
| **`four_of_other'`** | **`CloseoutPackRun40:368`** | **証明済み。`H_fourOther` の結論そのもの** |
| `Other'`（5h 版） | `CloseoutPackRun40:56` | `other_of_other'` で `Other` へ弱化できる |
| `Coupled'` | `CloseoutPackRun40:77` | `coupled'_of_idle` / `coupled'_tick` で run を運ばれる |
| `ChainPosInv2` が `Coupled'` を含む | `CloseoutPackRun41:213` の docstring が明記 | — |
| 消費者 | `CloseoutPackRun34.watchShiftS_of_chainPosInv` | `ChainPosInv` → `ChainPosInv2` に載せ替える |

**議論**: `5h ≤ R + C`（`Other'`）＋ `C ≤ 1`（shift guard の `singlePositive cycle`）
＋ `distance = R`（`SumRel` ＋ lag ゼロ）＋ `1 ≤ h` ⟹ `4h ≤ distance`。

**放電の実物**（新規モジュール、全体 build 緑）:

| 定理 | 場所 |
|---|---|
| `chainPosInv'_of_idle` / `chainPosInv'_steps` | `PalPeg/ShiftLocalRun.lean` |
| `shiftLocalS_of_chainPosInv'` / `shiftLocalS_of_run'`（`hfour` なし） | 同上 |
| `needIMW'_le_W'`（`needIMW'_le_W` の `hfour` 抜き） | 同上 |
| **`pal_in_peg_final39`（7 前提・反証済みゼロ）** | **`PalPeg/CloseoutFinalFour.lean`** |
| 索引の別名 `pal_in_peg_of_seven_leaves` | `PalPeg/Canonical.lean` |

**注意**: `hfour` を落とした既存 3 版はどれも代わりに偽の前提を取っていた —
`final31` は `hav`（`PalPeg.ConsumeAvailRefute.hav_false`）、`final36`/`final37` は
`hpack`（`CloseoutPackRefute.hpack_false`）。

**共通部分の括り出し**: `RadPack` → `TrailF` → `needL'` の 3 段は S / S3 / S4 で
3 重コピペだったので、`hsh : ∀ i ≤ Tc, ShiftLocalS (st i)` を引数に取る形
（`ShiftLocalRun.needIMW'_le_of_shiftLocal` ほか）に括り出した。`final5MW*` 4 版の
共通 45 行も `CloseoutFinalFour.pal_in_peg_of_needLe` に括り出した（既存 4 版の
載せ替えは未実施）。

## 3. `hpack` の代替（run 搬送パック）

| 部品 | 在り処 | 状態 |
|---|---|---|
| `ChainPack` / `ChainSide` | `CloseoutChainPack` | `hpack` は**偽** |
| `ChainSideR`（`scanBound` 抜き） | `CloseoutChainSideR` | 矛盾は除去、導出不能は残る |
| `ScanBudget` の producer | `CloseoutBudgetFree.scanBudget_of_front_run` | 証明済み（run の出口上界から） |
| **`LPackM3`**（`LPackM2` ＋ `CentreLedger` ＋ `LagCan`） | **`CloseoutPackRun49`** | **boot 成立・tick・steps・`MatchRes2` 抽出、全部標準公理のみ**（2026-09-19 に 3 エラー修正して登録） |
| `MatchRes2` の producer | `CloseoutPackRun49.matchRes2_of_lpackM3`（`ChainPack` 経由でない） | 証明済み |
| `VerRun`（`hpk` の最上位での実体） | `CloseoutVerSide` | `repV` ＋ `lagCan` だけ |
| 中心頭の表現 | `CloseoutPackRun21.CentreRep`（`InvLPC` の場） | — |

## 4. `hme`（marks）

| 部品 | 在り処 |
|---|---|
| `H_marksEntry'` を不要にする | `CloseoutMarksFree.marks_steps_free` / `marksRun_of_window` |
| 残差 | `WindowInOrigin`（モデル欠陥 (e)） |

## 5. `hor`（oracle）

| 部品 | 在り処 |
|---|---|
| 葉 11 本 | `CloseoutOracle8.h_oracle_of_leaves7`（結論は `H_oracle` = `CycleOracleMC`） |
| `hor` への橋 | `CloseoutOracleBridge.hor_of_H_oracle` / `hor_of_H_oracle2` / `hor_of_H_oracle2_invSS` |
| found 経路の入口 | **`CloseoutFoundRoute1`（未登録）** |
| 区間構成 | `CloseoutReadyStage.watchSegE_constructS`, `CloseoutSegCheckpoint.segment_to_checkpoint` |

## 6. 反証の在り処（`REFUTATION_AUDIT.md` が正本）

| 対象 | 反証定理 |
|---|---|
| `hpack` | `CloseoutPackRefute.hpack_false`（**無条件**） |
| `ScanBudget` | `CloseoutPackRefute.scanBudget_false`（無条件） |
| `SearchQuiet` | `GalilLeafQuiet.not_searchQuiet` |
| **`WatchOk`（単体）** | **`WatchOkRefute.watchOk_false`（無条件、2026-09-19）** |
| `WatchOk` ＋無条件 `Good` | `GalilWatchOkInst.no_watchOk_instance`（lag = reset 版） |
| `Trail` | `GalilTrailProof.not_trail_cx`（反例語） |
| `ReplaySpan` | `GalilReplaySpan.cx_*`（`aaaaabaaaab`） |
| `hpos` | `GalilLeafPos.not_hpos_of_report_place` / `not_hpos_of_tight_entry` |
| `MatchTickC` | `CloseoutMatchTickRefute.matchTickC_false_at_terminal`（条件付き） |
| `hpres` | `GalilLeafPres.hpres_false_at` |
| `ShiftAtMismatchC` | `CloseoutShiftMismatch.shiftAtMismatchC_false_at_nonterminal`（条件付き） |
| `WatchShiftG`（`hws`） | `CloseoutWatchShiftAudit.watchShiftG_false_at_backDone`（条件付き） |
| `Extra7` の 2 残差 | **`CloseoutPackRun50`（未登録）** |

## 7. 未登録モジュール 44 本（2026-09-19 時点）

**未登録は「無意味」ではない。** `CloseoutPackRun49` は未登録のまま 5 定理が健全で、
3 エラーを直したら 7 定理全部が通った。以下は在り処の記録であり、内容の評価ではない。

closeout 系（このゴールに関係する可能性が高い）:
`CloseoutFoundRoute1`（`hfound` の入口）/ `CloseoutPackRun50`（`Extra7` 残差の反証）/
`CloseoutRealize1`（`H_realizeLIMG2'` の `LocalStep` は付随的）/
`CloseoutWatchRound52`・`CloseoutWatchRound53`（match clock、`WatchTailC`）/
`CloseoutCoreEnc25` / `StageBirth`（`hinit` の監査）/ `StageIfaceInstance` /
`DecompInstance` / `PrepInstance` / `PrepInstances` / `Probe1`

下層・別系統:
`BorderJobProg` `GSVerifierFused` `GSVerifierProg` `GalilDpCode` `GalilDpCounters`
`GalilDpFrames` `GalilDpSimulation` `GalilFppMarkedCode` `GalilFppMarkedFrames`
`GalilFppPrepareCopy` `GalilFppWide` `MiddleClear` `MiddleProg` `PassSum9` `PassSum10`
`PatternProg` `ProgLangBudget` `ProgLangCalls` `ProgLangChoice` `ProgLangControlSteps`
`ProgLangSum` `ProgLangTransaction` `ProgLangWait` `ProgramBroadcast` `ProgramFrame`
`RTQueueProg` `SlotSchedule` `TextFeedAtomic` `TextFeedCycle` `TextFeedCycleModel`
`TextFeedPipelineDirection` `TextFeedPipelineWaitSource`

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
