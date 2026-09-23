# PAL の物理実現: 残件 KPI

2026-09-22、コウタ先輩の「残りの証明を KPI にして減らす」に基づく固定台帳。
正本は Lean の定義・定理・公理監査。作成した補題数や行数は KPI にしない。

## 現在の追い方 — proof-strategy.md の39作業項目

先輩の2026-09-22の追加指示により、巨大な公理1本は日々の指標にしない。
[`proof-strategy.md`](../proof-strategy.md) のチェック項目を M0–M5 の作業台帳に展開し、
各項目に証拠と残差を記録する。**39は作業項目数であり、必要な補題本数でも、同じ重さの単位でもない。**
検証中の変更は完了数へ加えない。詳細は [`PHYSICAL_CONNECTIONS.md`](PHYSICAL_CONNECTIONS.md)。

| 段階 | 未完 / 項目数 | 対象 |
|---|---:|---|
| M0 | 0 / 6 | 最終接続の型・ガード・量化・半径 |
| M1 | 0 / 7 | 空白初期化・最初の入力・通常入力・マクロ境界 |
| M2 | 0 / 6 | 非飢餓 scan count の最初の接続例 |
| M3 | 5 / 6 | 段カウンタ・alias・DP・バッファ再利用 |
| M4 | 6 / 6 | matched と残りの全分岐の接続 |
| M5 | 7 / 8 | 停止・出力・最終定理の差し替えと検証 |

**作業項目は完了21・未完18。** M0の6項目、M1の7項目、M2の6項目、M3-02のconsume各ケース、M5の抽象側3契約供給を完了として記録。M2は最初の非飢餓ケースの接続であり、count全体の完成ではない。

最終消費者の8引数 F01–F08 は、その上位の完了条件として残す。
**boot・feed・全starved・idle静止count・watch count全体・正規watch入口・shift入口/進行/終了を共通の `PhysicalShiftDispatch.machine rest` へ接続済み。**
`cases_of_remaining` がこれらを同じ最終TickCasesへ渡す。
hの鏡も共通Cacheに載せ、watch count全体・feed・starvedで保持し、shiftOneでは予備減算と同時に再建する。
shift入口から出口までのCache接続も完了。M3-01の第4小項目（鏡の保持とremainingへの引き渡し）は完了し、内訳は4/5。restart用コピーが残り、上位項目は未完。
残りのactiveケースは `hother`、
未実装命令行は `rest` に明示されており、全体のnone証明は未完。
旧T表は**15出口に局所定理あり、残り8**。今回T06（beginShift）を源条件供給・実dispatcher・最終TickCasesまで接続した。他の既存部品には未供給の側条件があり、15を最終接続済みケース数とは数えない。
最終完成時には `unconditional` の標準3公理のみへの依存を確認する。

2026-09-23のコピー付き接続は `PhysicalSnapshotEntryDispatch.machine rest`（下記LoanDispatchの基礎）。
blank/feed/starved/idle静止count/watch count全体/watch入口/shift進行・終了に加え、shift入口を
追加lastコピー込みで最終TickCasesへ接続した。入口の成功二度消費とコピー交換は32+32、
共通入口64と3カーソルの12段移動を、同じ118本・半径1536の1sweepへ合成する。
他の比較腕・restartは残り、M3-01/T02は未完のため21完了18未完を維持。
検証は `/tmp/physical-snapshot-entry-workbench.log` BUILD=0、
`/tmp/physical-snapshot-entry-axioms.log` AUDIT=0。新規7guardは標準3公理のみ。


2026-09-23追記: `PhysicalRestartCopies.from_copies` が同じEncからlast3コピーを供給し、
lower/work/鏡への有限交換とspan/鏡の同時resetを半径32の実sweepまで証明した。
restartへ融合する中間行で、debt/DP更新・半径鏡再準備・dispatcher接続は残る。
`completed_is_restart`は残る2更新後の実tickFun一致を証明するだけで、物理更新の放電ではない。
**KPI21完了18未完、T02/M3-01未完を維持。** Workbench BUILD=0、最終監査AUDIT=0:
`/tmp/physical-restart-copies-{workbench,axioms}.log`。新3guardは標準3公理のみ。


2026-09-23追記: `PhysicalDebtMirror.restart_from_copies`がlast引き渡しと半径鏡のdebt貸出しを
半径32+32で単一sweepへ融合。`PhysicalDebtRebuild.running/running_double`はdebt増分と
負の場合の鏡再準備を1回/2回実行する。この時点のRebuilding契約は共通Encへ未統合だった（下記追記で接続済み）。比較時の
保持、終了時の不足1補完、DP初期化、restart全行dispatchが残る。**21完了18未完を維持。**
全体BUILD=0/AUDIT=0、新6guardは標準3公理のみ:
`/tmp/physical-debt-rebuild-{workbench,axioms}.log`。


2026-09-23: `PhysicalLoanInvariant.Enc`へRebuildingを統合し、
`PhysicalLoanDispatch.machine rest`が最新の共通機械となった。実feedの12段と補完の可換性を
`PhysicalDebtFeed`で証明し、部分鏡/balanceを入力到着・全starvedで保持する。
blankと既存のcount/watch入口/shift入口・進行・終了も同じ最終TickCasesへ保持した。
探索の非飢餓行・DP reset・restart全行は未完。**21完了18未完、T02/M3-01未完を維持。**
Workbench BUILD=0、最終公理監査AUDIT=0、新規6guardは標準3公理のみ:
`/tmp/physical-loan-dispatch-{workbench,axioms}.log`。


2026-09-23: 正のworkのgrow countを同じ`PhysicalLoanDispatch.machine rest`へ追加。
span+=8/work--/span鏡/背景消去64と、debt返済・部分鏡再建32+32を一つのmacro sweepへ融合し、
clock減算も含め実tickFunと一致することを証明した。源Encからbalanceと有限窓のwork正判定を供給し、
`forward_grow`→`cases_of_remaining`でCountGrowをhotherから除いた。初回feed/全starved/既存ケースも保持。
work=0のprepare・比較・他の探索行は未完なので**21完了18未完、T02/M3-01未完を維持。**
Workbench BUILD=0、最終公理監査AUDIT=0。新4guard・更新cases guardは標準3公理のみ:
`/tmp/physical-grow-count-{workbench,axioms}.log`。


2026-09-23: `PhysicalMatchCounters`が比較時radius++/length+=2/debt--と条件付きcycle/replay減算、
部分鏡保存を証明。GrowStorageの半径を32へ縮小し、GrowCountは96、GrowMatchは96+32=128で融合。
実sweepとcompareFun/matchedPlaceのVM同定が通った。LoanAssemblyは部分鏡を保った12段ヘッド実行と
macro1536への輸送を証明し、idle verifierのnoneもstayで扱う。個別のctl/output・head readiness・
guard供給とgrow比較の最終TickCases接続は未完。prepare/他の探索/DP/restartも残るため、
**21完了18未完、T15あり8未、T02/M3-01未完を維持。**
Workbench BUILD=0、最終公理AUDIT=0、新7guardは標準3公理以内:
`/tmp/physical-grow-match-{workbench,axioms}.log`。共通機械はLoanDispatchのまま。


2026-09-23最新: growの一致比較を`PhysicalLoanDispatch.machine rest`の最終TickCasesへ追加。
GrowMatchTickが制御/output/replayingと左右カーソル、部分鏡を同じ12段・macro1536 sweepで保存。
GrowMatchCaseが実tickFun/guardを証明。到来prefixは既存ArrivedOnRunから、canRightは非飢餓から供給し、
hotherからMatchGrow（scan/clock≤1/chain idle/search grow/work正/比較一致）を除いた。
既存boot/feed/starved/count/watch/shiftも保持。work0 prepare・他探索・不一致/fallback・DP/restartが残り、
matched全体ではないため**21完了18未完、T15あり8未、T02/M3-01/T05未完を維持。**
Workbench BUILD=0、最終公理AUDIT=0、新4guardと更新cases guardは標準3公理以内:
`/tmp/physical-grow-match-final-{workbench,axioms}.log`。


## 最終接続と旧部品台帳の完了条件

* 旧T表の部品: 実際の `tickPhysRule` の12ステップが、その出口の抽象 `tickFun` を符号化する
  **分岐全体の定理**を接続する。目的の `EncControl` / `EncTapes` を仮定するラッパー、
  特定の chain 内部分岐だけの証明、頭だけの対応では減らさない。
* T の既存定理は明示された源状態の側条件付き。側条件を到達状態から供給する仕事は
  C04 に残す。特に `fpp` の `hcomp` / `hfloorRun` / `hin`、rewind の退役テープ消去条件、
  copy の読み取り条件を、証明済みだと扱わない。
* F: `ShadowedLocalFinal.given_physicalMachine_indexed` のその引数を、**同一の具体的な**
  `Q Γ t K L0 Enc q0 repQ outQ` に対して、追加の未解決仮定なしで供給する。
* 単体 Lean、`PalPeg.Workbench`、変更した定理の公理監査を通す。最終公理は
  `PalPeg/Axioms.lean` の guard で確認する。
* 分割・統合・再開が必要なら理由と旧→新の対応を変更履歴に残す。
  項目の削除・束ね直しだけで残数を減らさない。新しい `axiom` は追加しない。

## 最終接続: 8項目

消費者: `PalPeg/ShadowedLocalFinal.lean` の `given_physicalMachine_indexed`（固定証人 0 / 1 / 0）。
以前の AGENTS.md の「7つ」は数え違い。`PhysFrozen` は述語の選択であり、
それに関する証明引数は `hfrozenEnter` / `hfrozenKeep` / `hfrozenQuiet` の3本。

| ID | 未接続の引数 | 完了条件 |
|---|---|---|
| F01 | `hencInit` | 全テープ blank の物理初期配置から指定された抽象初期状態を符号化 |
| F02 | `hforwardTick` | 到達可能な非凍結状態で内部ティックを前向きに模倣。T/C 全体を消費 |
| F03 | `hforwardFeed` | 任意の到来文字を実際の入力付き物理ステップで模倣 |
| F04 | `hfrozenEnter` | 抽象の凍結点で具体的な `PhysFrozen` が成立 |
| F05 | `hfrozenKeep` | 入力なしの物理ステップが `PhysFrozen` を保存 |
| F06 | `hfrozenQuiet` | 凍結中は `repQ = false` |
| F07 | `hencRep` | 到達状態の抽象 report 判定と具体 `repQ` が一致 |
| F08 | `hencOut` | 報告点の抽象 output と具体 `outQ` が一致 |

F01は `enc_initial`、F03は `PhysicalBootFeed.forwardFeed` から供給可能。
通常noneステップ・report/output・凍結を含む最終機械の確定は未完で、8引数の束はまだ構成していない。
最後に `unconditional` の経路を差し替え、追加公理を外す。

## 旧部品台帳: 生の tickFun の23出口

消費者: `PalPeg/TickFunction.lean` の `GalilScaffoldTop.tickFun`。
証拠の定理は `PalPeg/PhysicalEncoding.lean` と下記の接続モジュール内。`あり` は上記 T の基準による
**局所分岐定理あり**を表し、F02 完了を意味しない。

| ID | 出口 | 局所分岐定理 | 証拠 / 残差 |
|---|---|---|---|
| T01 | init | 未 | 初期化ティックの具体行 |
| T02 | scan: restart | 未 | restart の制御・テープ・ヘッド |
| T03 | scan: wait | 未 | `background_still_of_tick` / `scan_consume_of_tick` は部分ケース。DP・chain 全ケースは未 |
| T04 | scan: count | 未 | 静止・順方向plain一致ケースは新接続で完成。背景処理全体は未 |
| T05 | scan: matched | 未 | 共通4カウンタ・鏡と制御は実際の12ステップへ接続済み。chain 全ケース・探索・誕生との合成が未 |
| T06 | scan: beginShift | あり | `PhysicalShiftSource.running_onRun` → `PhysicalShiftDispatch.forward_entry` → `cases_of_remaining`。源条件を実行から供給し、二度消費・入口更新・3カーソル移動・役割交換を一回の実sweepで接続。`entry_of_compare` が全scan-shift腕を覆い、`entryRead_iff` が有限窓の選択を保証 |
| T07 | scan: beginFallback | 未 | 不一致比較後の fallback 入口 |
| T08 | shift: shiftOne | あり | `PhysicalShift.running` → `PhysicalBoundaryCount.forward_shift` → `cases_of_remaining`。共通CoreInv・実sweep・元のremainingPosガードまで接続。残量上限/CopyIdleはOnRun、可用性は合法Tickから供給 |
| T09 | shift: exit | あり | `PhysicalShift.running_exit` / `running_mode` → `PhysicalBoundaryCount.forward_shift` → `cases_of_remaining`。残量ゼロで鏡がhへ戻ることを含め共通CoreInv・実sweepへ接続 |
| T10 | copy: copyOne | あり | `copy_one_of_tick`（読み取り条件の供給は C04） |
| T11 | copy: copyEnd | あり | `copy_end_of_tick` |
| T12 | home: homeStep | あり | `home_of_tick` |
| T13 | home: fppStart | あり | `home_of_tick` |
| T14 | fpp: fppSlice | あり | `fpp_of_tick`（プログラム側条件の供給は C04） |
| T15 | fpp: fppDone | あり | `fpp_of_tick`（同上） |
| T16 | markEnd: markForward | あり | `markEnd_of_tick` |
| T17 | markEnd: markBack | あり | `markEnd_of_tick` |
| T18 | choose: select | 未 | 選択・alias・rewind 入口 |
| T19 | choose: back | あり | `choose_back_of_tick` |
| T20 | rewind: fppReset | あり | `rewind_reset_of_tick`（退役半分の消去条件は C04） |
| T21 | rewind: pair | あり | `rewind_pair_of_tick_branch` |
| T22 | rewind: one | あり | `rewind_one_of_tick_branch` |
| T23 | replayStart | 未 | 再生開始・制御・カウンタ・カーソル |

同じ定理が複数の出口を覆うことがある。定理名の個数を数えない。
`rewind_one_of_tick` 自体は `hctl` / `htapes` を受け取る組み立て器なので、
その名前だけでは T21/T22 の証拠にしない。上表の `_branch` を使う。

## F02 の共有統合作業: 5項目

| ID | 状態 | 完了条件 |
|---|---|---|
| C01 | 未 | active chain の内部ステップ＋match 処理。copy/back/watch/broken、両方向、0/1/2回消費、不一致を実際の行動表へ接続 |
| C02 | 未 | chain の段表現を `counterOf` / 符号化に組み込み、境界イベントの alias を実現 |
| C03 | 未 | idle chain の DP 走者・探索完了・chain 誕生を実際の行動表へ接続 |
| C04 | 未 | 到達状態から全分岐の側条件を供給。入力との対応、鏡、消去、有限制御の範囲、head readiness を含む |
| C05 | 未 | 同一機械で全分岐を dispatch・融合し、`TEqG` / sweep、margin、starved-idle を保ち、F02 の型へ接続 |

語ごとの `Enc w` を受け取る `given_physicalMachine_indexed` を証明した。
機械本体は語の量化の外で固定する。`PhysicalContract.Obligations` はその8引数を保持し、
`forwardTick_of_cases` は OnRun / CanonTrace と既存の合法なTickを失わず接続する。
boot / feedは具体化済み。noneは全starved、CountAtRest、CountWatch（成功/失敗/非消費、全token・両方向・境界）、
back/FIRSTのCountBackReady、shift入口とshiftモード全体を同じPhysicalShiftDispatch.machineとCoreInvを持つEncで供給し、その他が未完。
正規period配置とhの一致はOnRunから供給し、入口後の鏡5の値も実sweepで証明済み。

## 次の対象

M3-02完了。period形状・hのOnRun供給とwatch入口後の鏡5の値まで接続済み。
watch/shift間の鏡と予備は入口から出口まで共通Enc・実dispatcherへ接続済み。M3-01の残りはrestart用lastの複数コピーと再準備。
`PhysicalRoles` で同じ118本・半径1536上の有限役割とboot/feed/既存countを接続。
`PhysicalCountSpare.forward_plain` でslot 10の予備準備を既存VM/clockの実sweepへ合成した。
`PhysicalWatchEntry` が入口の4本reset、period移動、背景消去、clock減算を
有限窓で選ぶ実sweepへ接続。正規period配置からInv/Repを新たに作る。
`PhysicalCacheInvariant` / `PhysicalCacheMachine` でCounterShapesとwatch/brokenのInv/Repを
同じEncへ載せ、実boot・初回を含むfeed・全starved・静止count・plain一致count・正規watch入口で
保持を証明。plain消費の源Inv/RepをEncから供給し、同じ最終TickCases・有限役割へ接続した。
正規period配置・残量上限・shift時CopyIdleのOnRun供給は接続済み。hの鏡を含めた残る分岐の保存は未完。
`PhysicalBoundaryCount` が成功countのplain両方向・FIRST/LASTの役割/符号交換を同じ実sweepと
最終TickCasesへ接続済み。さらに不一致・非消費を接続し、`forward_watch` がwatch count全体を扱う。
PhysicalShiftSource.running_onRunが実行側の既存TrackedAt.usedをArrivedOnRun経由で受け取り、全源条件を供給。PhysicalShiftDispatchが実窓の選択・既存分岐の保持・最終TickCasesを閉じた。T06を完了し、旧T表は14→15あり、9→8未。39項目は21完了・18未完のまま。M4-02にはbeginFallbackが残る。
M2は `PhysicalCountConsume.forward_count_plain` と `cases_of_remaining` まで接続済み。
watch countの不一致・非消費もPhysicalBoundaryCountへ接続済み。他のchain/searchケースは未完。
matched の続きは M4。以下は再利用する既存部品の記録。

* `scan_matched_counters_of_tick`: active chain のとき、radius / length / 条件付き cycle /
  条件付き replay と鏡が、実際の12ステップ後に抽象 `tickFun` の値を符号化する。
* `scan_matched_control_of_tick`: chain の種類によらず、時計・出力・replaying を含む制御と
  onLetter / leftFirst の2判定が実際の12ステップ後に一致する。
  右ヘッドが到来済み入力を表すこと、その長さが入力語以下であることは源状態の条件。
* `scanNext` / `scanActs` を `ruleNext` / `ruleActs` の実際の scan 行へ接続済み。
  内部消費は `scanConsume_tapes` へ切り出し、`scanAfterConsumeWindows_eq` /
  `chainMatchConsumesTest_of_watchConsume` が比較行の拡張に依存しないようにした。
* `scanCommands_watch_double` / `scan_watch_double_head` は二度消費の命令と実行を接続済み。

**T05/C01 は未完のまま。** 境界イベント、chain 内部全ケース、idle の探索・誕生、
全成分の同時符号化をまだ閉じていないので残数を減らさない。

## 変更履歴

| 日付 | 変更 | 計器 |
|---|---|---|
| 2026-09-22 | `tickFun` の23出口と最終引数8本から基準を固定 | T 未接続11/23、F 未接続8/8、C 未完5/5、追加公理1 |
| 2026-09-22 | `physRule_copy_end` を既存の12ステップ組み立て器へ接続し `copy_end_of_tick` を証明 | **T 11→10**。F/C/公理は不変 |
| 2026-09-22 | matched の共通カウンタ・鏡と制御を実際の12ステップ・抽象 `tickFun` へ接続 | T/F/C/公理は不変。T05全体は未完 |

検証: 単体 **EXIT=0**、Workbench **BUILD=0**、最終公理監査 **AUDIT=0**（追加公理1のまま）。
`PhysicalEncoding.lean` の9つの公理guardを通過し、対象定理は標準3公理のみに依存。
今回追加したguardは `scanConsume_tapes` / `scanMatchCounter_tape` /
`scan_matched_counters_of_tick` / `scan_matched_control_of_tick`。
`sorry` / `admit` / `native_decide` / 新規 `axiom` はソースに無い。

ログ: `/tmp/pe-match-core.log`（単体）、`/tmp/pe-match-core-build.log`（Workbench）、
`/tmp/pe-match-core-axioms.log`（最終公理監査）。最終公理のguardは変更していない。

2026-09-22 方針変更後の検証: Workbench **BUILD=0**。
ログ `/tmp/physical-strategy-workbench.log`。境界単体 `/tmp/physical-boundary-check.log` **EXIT=0**。
コピーカーソルの余白条件除去 `/tmp/physical-place-margin-checked.log` **EXIT=0**。

最終監査 `/tmp/physical-strategy-axioms.log`: **AUDIT=0**。最終定理のguardは未変更。

共通cache符号化の検証: `PhysicalCacheInvariant.lean` / `PhysicalCacheMachine.lean` **EXIT=0**、
`/tmp/physical-cache-machine-workbench.log` **BUILD=0**、
`/tmp/physical-cache-machine-axioms.log` **AUDIT=0**。
新モジュール2本をWorkbenchへ登録し、追加した公理guardは標準3公理のみ。
`sorry` / `admit` / `native_decide` / 新規 `axiom` なし。最終定理の追加公理は未変更。

成功count境界の検証: `/tmp/physical-boundary-count.log` **EXIT=0**、
`/tmp/physical-boundary-count-workbench.log` **BUILD=0**、
`/tmp/physical-boundary-count-axioms.log` **AUDIT=0**。
新モジュール3本をWorkbenchへ登録。running_staged / running_rotate / running_match /
forward_match / cases_of_remainingのguardは標準3公理のみ。
新規axiom・sorry・admit・native_decideなし。最終unconditionalのguardは未変更。

2026-09-22: M3-02完了、**20→21完了 / 19→18未完**。
`PhysicalBoundaryCount.forward_watch` / `cases_of_remaining` が成功/失敗/非消費を含む
watch count全体を同じ実機械・CoreInv・最終TickCasesへ接続した。
型はtoken・方向・lag符号・比較結果を追加仮定に持たず、Encと既存の合法Tickから供給する。
比較の二度消費を同じtickへ合成する仕事はM4に残し、count全体の完成とは数えない。

watch count全体の検証: `/tmp/physical-watch-count.log` **EXIT=0**、
`/tmp/physical-watch-count-workbench.log` **BUILD=0**、
`/tmp/physical-watch-count-axioms.log` **AUDIT=0**。
新モジュールPhysicalCountMismatch/PhysicalWatchIdleをWorkbenchへ登録。
forward_count（両モジュール）、forward_consume、forward_watch、cases_of_remainingのguardは
標準3公理のみ。新規axiom/sorry/admit/native_decideなし。git diff --check通過。
最終unconditionalの追加公理は未変更で、無条件PALは未完。

2026-09-22: M3-01を台帳末尾で5小項目に分解し、入口の源条件・hの長さ一致・入口後の鏡を証明。
`CountBackReady` が実ガードだけで最終残差から除外される。鏡の後続保持とshift/restartは未完なので、
**21完了・18未完を維持する。**


2026-09-22: **T08 shiftOneを同じ最終TickCasesへ接続。旧部品台帳は13→14あり / 10→9未。**
M4-04のshiftOne小項目を完了。M3-01もshift中の共通Cache保存が閉じたが、入口・出口・restartが残る。
**39項目は21完了・18未完を維持。** 上位項目をまとめ直して残数を減らしたものではない。
`ShiftMoving` は元のremainingPos（shift/copyのOR）と同値で、CopyIdleと残量上限をOnRunから供給する。
全テープ・退役FPP背景消去・予備・h鏡・制御・境界を一つの実sweepで保存する。

検証: `/tmp/physical-shift.log` **EXIT=0**、
`/tmp/physical-shift-connection.log` **EXIT=0**、
`/tmp/physical-shift-workbench.log` **BUILD=0**、
`/tmp/physical-shift-axioms.log` **AUDIT=0**。
`ideal_shaped` / `running_shaped` / `remainingBound_onRun` / `copyIdle_onRun` / `running` /
`forward_shift` / `cases_of_remaining`の公理guard通過（標準3公理のみ）。
新規axiom・sorry・admit・native_decideなし、git diff --check通過。
39項目と旧23出口の件数も台帳の実行列から確認。最終unconditionalの追加公理は残る。

2026-09-23: beginShift全体を共通dispatcherへ接続。**T06未→あり、旧T表14→15あり・9→8未**。
M3-01第4小項目も完了（4/5）。上位の39項目は21完了・18未完を維持。
検証: `/tmp/physical-shift-dispatch.log` **EXIT=0**、
`/tmp/physical-shift-dispatch-workbench.log` **BUILD=0**、
`/tmp/physical-shift-dispatch-axioms.log` **AUDIT=0**。
forward_entry/cases_of_remainingの公理guardは標準3公理のみ。最終追加公理は未変更。

2026-09-23: restartの旧探索4カウンタの非参照性、有限窓の優先判定、4ビューのstay、
有限制御更新を `PhysicalRestartStorage` で証明。lastの実コピー準備・借りた鏡の再準備・
DPリセット用バッファ・実行行への接続は未完。**21完了18未完、T15あり8未を維持**。


2026-09-23: `PhysicalSearchRecycle` のwatch入口6本resetを検証し、
`PhysicalSearchSnapshots` で同じ既存6本上の2組のboundary/last/spareを実装。
実consumeの最大3増分・2組の役割交換・次回Inv、shift時の6本減算を実sweepで証明し、
源窓によるphase/FIRST/LAST選択まで接続。入口からの供給とlastの2コピーRepも証明。
最終dispatcherのEnc/Stored統合、VM側base/hbaseの供給、restartへの引き渡しと
span/debt/鏡/DPの再準備は未完。**21完了18未完、T15あり8未を維持**。
検証: `/tmp/physical-search-snapshots-workbench.log` **BUILD=0**、
`/tmp/physical-search-snapshots-axioms.log` **AUDIT=0**。entry_saved/watch_consume/shift_running/
saved_last_copiesのguardは標準3公理のみ。最終追加公理は未変更。


2026-09-23: `PhysicalSnapshotCount` でconsumeのbase/hbaseを既存count VM行から放電。
`PhysicalSnapshotInvariant.Enc` と `PhysicalSnapshotMachine.machine rest` にコピーInvを導入し、
全blank/feed/starved・idle静止count・watch count全体・正規watch入口を同じ最終TickCasesへ接続。
旧境界交換と追加2組の交換は同じ実sweep。新Encではshift/比較/restartのコピー保持がまだhotherに残る。
旧shift証明は保持し、snapshot減算・二度消費融合をこれから接続する。
restartのlast引き渡しとspan/debt/鏡/DP再準備も未完。**21完了18未完、T15あり8未を維持**。
検証: `/tmp/physical-snapshot-machine-workbench.log` **BUILD=0**、
`/tmp/physical-snapshot-machine-axioms.log` **AUDIT=0**。新しい最終TickCasesのguardも
標準3公理のみ。39項目の実行列を再集計して21/18を確認。最終追加公理は未変更。


2026-09-23: `PhysicalProgramErase`が同じ118本の退役DP12本を有限制御で消去する。
Denseを源条件として長さの線形上限内のroot復帰とresetへのTEqGを実sweepで証明し、
既存全Encと余白も保持した。旧eraseActが非空白rootで停止する例も形式化済み。
源Dense/消去時間の実traceからの供給・有限制御の共通dispatcher統合・live切替えは未完。
DP/FPP再利用全体の完成ではなく、hotherも減らないので**21完了18未完、T15あり8未を維持**。
全体BUILD=0/AUDIT=0、新5guardは標準3公理以内:
`/tmp/physical-program-erase-{workbench,axioms}.log`。


2026-09-23: `GalilDpDensity.onRun/fpp_onRun`で実初期配置から任意prefixのDP12/FPP9本の
Denseを証明。MARKSのemit位置は既存prepared完成形と実行一意性から供給し、
全373命令の有限表をカーネル検査。`PhysicalDpDensity.bank_reset_onRun`で実Control.Runから
Denseと初期長＋enabled call数のサイズ上限を消去器へ供給した。
再liveまでの消去時間の割当て・共通phase・PAL全体のtrace/ロード途中・prepare/restartは未完。
M3-06は未完、hotherも未変更なので**21完了18未完、T15あり8未を維持**。
Workbench BUILD=0・最終AUDIT=0、新8guardは標準3公理以内:
`/tmp/physical-dp-density-{workbench,axioms}.log`。


2026-09-23: `PhysicalDpCleanup.machine`が有限phaseとDP退役12本の消去を
旧共通dispatcherと同じ半径1536・118本・単一sweepへ載せた。
新Encは実消去のGood/Viewを持ち、doneからresetへのTEqGを供給する。
実bootで両bankの空白を証明し、初回を含む全feed・全starvedを新Encへ接続。
非飢餓の既存行/最終TickCasesの移行、再liveまでの期限、PALのtrace/ロード中、
prepare/restart/FPP消去は未完。旧hotherは未変更、M3-06は未完なので
**21完了18未完、T15あり8未を維持**。Workbench BUILD=0・AUDIT=0、新13guardは標準3公理以内。
ログ: `/tmp/physical-dp-cleanup-{workbench,axioms}.log`。


2026-09-23 15:05: DP消去付き共通機械へ既存7activeケースを最終TickCasesまで移行。
PhysicalDpBankが実dispatcherのDP bank保存を証明し、CleanupDispatchが同じ源ケースを新Encへ渡す。
PhysicalDpPreloadは任意ロード途中Runの12本Denseとサイズ上限、PhysicalDpRetirementは
源Loan Encのlive DP表現を供給して準備/実行中の消去開始へ接続。
再live期限・PAL全体の履歴供給・prepare/reset/restart/FPP旧消去が残るため、M3-06は未完。
**21完了18未完、T15あり8未を維持。** 新10guardは標準3公理以内、
Workbench BUILD=0（9810 jobs）/AUDIT=0: `/tmp/physical-dp-retirement-{workbench,axioms}.log`。
ユーザーのClaude Code引き継ぎ依頼により、最新の具体的引き継ぎをCLAUDE.md冒頭へ記載。
