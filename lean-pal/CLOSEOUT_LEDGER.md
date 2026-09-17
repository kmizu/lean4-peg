# CLOSEOUT_LEDGER — lean-pal 残差台帳

**目的**: 無条件 `PAL ∈ PEG`（`PegSeparation.RecognizedByTotalPEG PalPeg.PAL`）へ向けて、
主経路に残る**意味的義務**だけを一元管理する。ファイル追加・新しい `finalN`・build 成功は、
それ単独では前進として数えない。

**状態区分**

| 区分 | 意味 |
|---|---|
| `OPEN` | 未証明の意味的義務が残っている |
| `REFUTED` | 現在の命題に反例がある。証明対象でなく修正対象 |
| `REFORMULATED` | 命題を適切に変更したが、成立または利用側との接続が未完 |
| `PROVED` | 新命題自体は証明した。最終経路への供給は未確認 |
| `INTEGRATED` | 成立済みの前提から供給でき、主経路で利用され、対応する旧義務が消えた |

**未解消の前提を `H_x → H_y`、構造体フィールド、instance、別 oracle へ移しただけなら `OPEN` のまま。**

基点: HEAD `b70b395`（PR #61）。検証コマンド: `cd lean-pal && lake build --quiet PalPeg`。
`#print axioms` は推移的公理依存の検査であって、引数として置いた前提の成立を検証しない。
最上位定理の**完全な型**を `#check` で確認し、各前提の供給元まで追うこと。

---

## 0. 最上位

`pal_in_peg_final24` — `PalPeg/CloseoutPackRun46.lean:319`。状態 `OPEN`（下記 11 前提が未供給）。

前提: `hSP`, `hws`, `hee`, `het`, `hme`, `hsl`, `hsc`, `hor`, `hbs`, `hls`, `hC`。

> 注意: `final13 → final24` の番号の増加は、**義務の減少を意味しない**。多くは
> 同じ義務の再定式化であり、実際に主経路から消えた義務は §2 に列挙したものだけ。

---

## 1. OPEN（主経路に残る意味的義務）

| ID | 意味 | 現在の宣言 | 供給元 | 利用側 |
|---|---|---|---|---|
| `hSP` | scan 状態での `ShiftPal`（shift 入口の回文性） | `CloseoutPackRun36:712` の引数 | `ChainRound`（`CloseoutPackRun31:183`）→ 残 `H_shiftDone`(閉)/`H_advance`/`H_birth`/`H_fresh`/`H_matched` | `lTickLeaves2_of_shiftPalG` |
| `hws` | `WatchShiftG`（chain–scan 結合） | 同上 | `ChainPosInv2`（`CloseoutPackRun41:215`）+ `Coupled'`（`PackRun40:77`） → 残 `MatchRes2` の `repVmid`/`replayPay`、新規場 `CentreLedger`、`LagCan` | `rShiftNextMG_of_watchShiftG` |
| `hee` | `Extra7` 入口 | `CloseoutPackRun46:284` | 残差は **1 つ**: `∀ c r, InvLPC w c r → position r.right ≠ 2*w.length` | `bigPack2MG7''_tick` ほか |
| `het` | `Extra7` tick | `CloseoutPackRun46:296` | 残差は **1 つ**: `(mode ≠ scan ∨ clock = 1) → y.mode = scan → ¬y.replaying → canRight y.vm.right` | 同上 |
| `hme` | `H_marksEntry'`（rewind 角） | `CloseoutPackRun16:~185` | `ChooseLayout`（`PackRun17:120`）→ 残 `WindowInOrigin` → `WalkerInOrigin`（`PackRun28:526` で閉）→ 残 `hplace`、`2 ≤ delay`、replay 中の `canRight` | `MarksInv'`/角 2 本 |
| `hsl` | `H_shiftLocalG` | `CloseoutPackRun26:317` | 未着手 | `packRunR_MG2` |
| `hsc` | `H_stageScan` | 最上位引数 | 未着手（readiness を消費しないことを確認済み） | 同上 |
| `hor` | `CycleOracleMC3` | 最上位引数 | §3 の葉一覧 | 同上 |
| `hbs` | `H_bootShift` | 最上位引数 | 未着手 | 同上 |
| `hls` | `H_landShift` | 最上位引数 | 未着手 | 同上 |
| `hC` | `H_realizeLIMG2'`（局所実現） | `CloseoutPackRun36:488` | 局所側（`LocalSysConcrete`/`LocalRealizes*`）、`Fair` 依存 | `pal_in_peg_final5MG2` |

---

## 2. INTEGRATED（主経路から実際に消えた義務）

| ID | 何が起きたか | 根拠 |
|---|---|---|
| `Extra.failed` | **削除**。監査の結果どの消費側も読んでいなかった（`Extra'` の読み手は `scanAvail`/`rewindMargin` のみ；DP の実消費は `MismatchDp` が自前経路で `StageFailed` に到達） | `CloseoutPackRun42` §2 監査、`CloseoutPackRun43` |
| `Extra.cand` | **削除**（同上）。裸の向き変換 `H_candOrient` は反例あり（§4） | `CloseoutPackRun43`、`CloseoutCandOrient` |
| `Extra.ready` | **削除**。どのモードでも読まれていなかった | `CloseoutPackRun45` §0 監査、`CloseoutPackRun46` |
| `rInitPackM` | 無条件で証明（pack は `AuxPack.front.notInit` により `init` に居ない） | `CloseoutPackRun21:88` |
| `WatchPrefixC` | 無条件の定理（`WatchSeg` の構成子族は排他、段は関数的） | `CloseoutWatchRound20:172` |
| `ShiftPeriodC` | 葉ですらなかった（`ShiftRoundDataL` の 2 場から導出）→ 削除 | `CloseoutWatchRound45:81` |
| `WindowEndC` | 仮定ゼロで閉（`LandingData.ScanInvariant` の `Represents` から） | `CloseoutWatchRound50:86` |
| `H_fourOther` | `Coupled'`（sharp `5h`）の下で定理に | `CloseoutPackRun40:306`、`coupled'_tick` は無仮定 |
| `hshift`（readiness） | 放電（`scan_shift` は比較量子を 1 つ消費し clock を 2048 に） | `CloseoutPreload38:51` |
| `hact`（readiness） | 形を slack 0 の節に直して消滅 | `CloseoutPreload39:57` |
| `hrot`（core） | `RTQueue.Inv` から導出、仮定でなくなった | `CloseoutCoreEnc22:180` |
| `near ≠ []`（core） | 消滅 | `CloseoutCoreEnc22` |

---

## 3. `CycleOracleMC3` の葉（`hor` の内訳）

閉: `hex`, `hsearch`, `hends`, `hbudget`, `hrs`, `hended`, `hlastMatch`, `hstr`, `hfb`。

| 葉 | 状態 | 備考 |
|---|---|---|
| `hpres` | `REFORMULATED` | 普遍形は `GalilLeafPres.hpres_false_at` が反証。scan 側は `HpresAt` で放電（`CloseoutOracle5:64`）。replay 側 `hpresRep` は `GalilReplaySpan` に制限形を受ける版を追加する編集が必要（進行中） |
| `hstage` | `OPEN` | `ReplayStageInv`、mid-replay restart の `3·radius ≤ 5·last` |
| `hshape` | `REFORMULATED` | `StartShape` は偽 → `StartShape'`（`GalilReplaySpan.startShape'_of_decodes`） |
| `hlastMismatch` | `OPEN` | 最終文字分岐 + `EntryRefreshed` |
| `hmismatch` | `OPEN` | `hdp` → `MismatchDp`+`StageBudgetAt`、`hpos` → 区間予算 |
| `hfound`/`hfoundBg` | `OPEN` | 着地不変量に `Restarted`/`StageEntry` + found tick からの経路構成。**最大の未着手** |
| `hfoundReplay` | `OPEN` | 未着手 |
| `hreadyB` | `OPEN` | 着地での `RunEntriesAll` |

---

## 4. REFUTED（反例があり、修正対象）

| ID | 反例／理由 | 現在の扱い |
|---|---|---|
| `H_candOrient` | `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`。接頭辞 3/5 は回文、`W.drop 3 = [0,0,1]` は非回文。Lean で確認（`CloseoutCandOrient.unrestricted_transport_false`、標準公理のみ） | 主経路から削除済み。正しい橋は `GalilDpSuffix.candidate_iff`（同一窓＋反転） |
| `Extra.scanMargin` | 1 文字語で反証（`ScanMargin2.margin_false_witness`） | 削除済み |
| `ShiftLocal`（無ガード） | 全 `scan→shift` 着地で偽（`shiftLocal_false_at_landing`、`Internal.idle` が有効） | `ShiftLocalG`（scan ガード付き）へ |
| `ReplayNoBusyC` | replay 中も found 量子で chain は始まる（Scala も同じ） | `ReplayRunW`（3 分岐）へ |
| `LandingFreshC` | `h` が普遍量化で `periodLength w' = 0` と `= 1` を同時要求 | `LandingFreshC'` + `ShiftPeriodC` へ分割 |
| `MismatchLandingLagZeroC` | lag 1 の `take` が guard を通る（`budget_counterexample`） | 着地限定 `MismatchLandingLagZeroL` へ |
| `WatchFreshC` | 全 watch 区間量化、`WatchSegE.stop` は任意 clock で成立 | 着地限定へ。ただし下記の通り着地版は空虚 |
| `WatchFreshAtC`（着地版） | **前提が充足不能 = 空虚**。着地の chain は `copy`（`chainStart` は `ChainVM.copy`、`ChainMatched` は構成子を保つ）であり `watch` ではない（`CloseoutWatchRound52.landing_chain_copy:120`、`landing_not_watch:135`、`watchFreshAtC_vacuous:148`）。**n72 の「文脈だけで閉じた」は誤り**で、`watchFreshAtC_of_ctx` は内容を持たない | 誕生時刻版 `WatchBirthFreshC`（watch 誕生は着地の `2h+3` prep tick 後、そこでの clock は `MatchClock.run 2048 2048 avPrep` で fresh でない）へ。`OPEN` |
| `ChainWatchPhaseC`（`n ≤ 2047`） | chain 周期は非有界なので copy/back 相は 1 クロック窓に収まらない | 相跨ぎ `ChainWatchReachM` へ |
| `LagPos`（`0 < lag`） | `Outer.immediate` は `zero lag` がガード | `LagCan`（`0 ≤ value lag`、自己保存）へ |
| `ScanRealized` | `ScanSupplyInv` と矛盾（`scanRealized_absurd`） | `PostRunPh`/`PostRunF`（到達可能接頭辞）へ |
| `hpres`/`hpresRep`（普遍形） | `hpres_false_at` | `HpresAt`/`HpresRepAt` へ |
| `Extra3.failed`（全 scan 状態） | restart が DP を入口に reset | 削除（§2） |

---

## 5. モデルの欠陥（修正単位）

| ID | 内容 | 状態 |
|---|---|---|
| `M-periodOnly` | Scala `ScaffoldChain.start()` は `periodOnly = false` **かつ** `cycle.reset()` を行うが、Lean の `chainAt`/`chainStart` は `s.periodOnly` を触らず `restartVM`/`replayStartVM` も保持。`shiftGuardVM` は `s.periodOnly` を読むので、restart 後の fresh chain が stale なフラグ・cycle で判定される。`cycleAfter` も `s.periodOnly` を読んで誤って減算し得る | `OPEN`。**次の修正単位**。boolean 一個の代入では不十分（`cycle.reset()` と、chain 誕生と match 処理の順序の照合が要る）。reset の条件は「その遷移で新しい chain が実際に誕生すること」であり、`found = true` ではない |

---

## 6. 運用規則

- 再定式化・改名でも同じ義務 ID を引き継ぐ。
- 「一つの仮定」に問題を詰め直して数を減らさない。
- 進捗率は報告しない。今回何が `INTEGRATED` になったかを報告する。
- 同じ義務が名前を変えて再登場したら、別名へ分解する前に、初期状態・遷移・量化範囲・供給元へ戻って監査する。
