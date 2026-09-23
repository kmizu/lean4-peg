# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 2026-09-23 深夜（最新・最優先）— 方針転換: Scala の出力経路を TM なしでそのまま写す

コウタ「もとのScalaコードが大したことやってないんよ」「君が問題を難しくしてる」「TMの枠だと色々ずれる」「量はあってもかなり単純になるはず」。
**118本テープ TM（`Physical*`）経由は打ち切り。** 正本の出力経路は window-pal（`GenerateWindowPal` → `ScaffoldWindowPal` → circuit → `SymbolicSca2Peg`）で、Lean の `GalilScaffold*` が写していた `ScaffoldGalil.scala` は出力経路ではない。

**済み（標準3公理）**
- `PalInPegSca.pal_recognizedByTotalPEG_of_sca`: `RecognizedBySCA PAL → RecognizedByTotalPEG PAL`（Kim–Park `SCAToPEG.loffBackward` ＋ `PAL_reverse_mem`）。
- `ScaTyped`: 状態・ラベルを構造型で書いた scaffold 自動機械 `Typed` を Kim–Park の `Fin` 版へ輸送（`pal_in_peg_of_typed`）。

**進捗（2026-09-23 深夜、すべて標準3公理・コミット済み）**
- 写し（定義のみ、サブエージェント）: `ScaWindowPal`（WindowPAL/WindowStage の tick）、`ScaGsProgram`/`ScaGsTables`（GS 命令型、matcher 294 行・flags 492 行の表、quantum 512/1024）、`ScaWindowWorker`（worker の抽象意味）。
- 証明: `ScaHeap`（永続スタック）、`ScaWindowSchedule`（段の運びの閉じた形 `Inv`、`inv_run`、`answering_run`）、`ScaWindowOutput.window_correct`（worker の仕様＋fault なし ⇒ 受理 ↔ PAL）。
- 残り: (W1) コンパイル済み表 ＝ `GsMatchHeads`/`GsDualFlags` のコルーチン（有限の翻訳検証、力技）、(W2) コルーチン ＝ GS 照合／中央フラグの仕様（Lean の `GSScan`/`GSDecomp`/`GSRealTime`/`StageMatcher` へ）、fault なし、SCA への符号化（無限の部分を永続スタックで）。

**計画（`DESIGN_SCA_PAL.md` §6 の3層）**
1. 汎用の永続構造層: Scala `ScaffoldCircuitStructs` を写す。ノードごとに有限個のセル枠、セルは `below`（辺）・枠タグ・`value`（辺）・`data`。スタック = 根の辺＋タグ。push/pop/copy/clear が抽象リストへの表現関係 `Rep` を保つことを1操作1補題で。pop は「根→below」の2歩で半径内。キュー（永続スタック2本）・カウンタも同様。
2. 抽象機械: window-pal の1文字ぶん（二進段・GS head worker）を永続レコード＋有限制御の `absStep` として Scala と同形に書く。
3. 不変量 `Inv w` と正しさ: 段①の既存資産（`Assembly.dyadicAnswer_correct`、`StageMatcher.dyadic_gs_correct` 等）へ精緻化。符号化で `Typed` 自動機械へ → `pal_in_peg_of_typed`。
- 注意: Lean の中央フラグは Manacher、Scala は `GsDualFlags`。どちらに合わせるかは段2で決める。
- 物理経路の7本の義務（`PalInPegPhysical`）は旧経路として残す（新経路が完成したら最上位を付け替える）。

## 2026-09-23 深夜 — 最上位を物理機械の経路へ付け替え（最新。下の節より優先）

**目標定理は `PalPeg.PalInPeg.unconditional`（`PalPeg/PalInPegPhysical.lean`）。** 旧 `obligation_localRealization`（「局所機械が存在し正準トレースの抽象 latch と受理が一致」を 1 本の存在命題に詰めたもの。機械の構成と正しさが全部隠れ、抽象 VM の head 瞬時コピーまで tick ごとに追わせる形）はコウタの判断で撤去。旧経路は `PalInPeg.given_localRealization`（前提付き）。
公理ラチェット（`Axioms.lean`、AUDIT=0、ルート 9842 jobs BUILD=0）は**7本の原子義務**: `obligation_scanRest` / `obligation_fpp` / `obligation_chooseSelect` / `obligation_rewindReset` / `obligation_init` / `obligation_replayStart` / `obligation_freeze`。前6本は `PhysicalResidualParts.TicksWhere physRest P`（`physRest` は未実装モードの view 命令＝stay）。本数が 1→7 に増えたのは旧 1 本が中身を隠していたため。
**fpp（未停止）は処理済み**: `hcomp`（抽象テープ左に K 以上、run 上で偽）を撤去し、窓機械はパディング版の抽象機械（`PhysicalFppPad.padMachine`、左に 6）と比較する（`machineAgree_winMachine` / `winRun_agree`、物理パディングは `decProg` で 6）。`hfloorRun` は `RunOffFloor`（量子の各歩で床に当たらない）に弱め、合法 Tick の関係版 `Run` から出す（`runOffFloor_of_run` / `fppReady_of_tick`）。`obligation_fpp` は「停止済みプログラムの fpp tick」だけ（トレース不変量で消せる見込み: fpp へは `fppStart` でしか入らず停止時は markEnd へ）。
**計算モデルの食い違い**: 正本の PEG（window-pal）は scaffold（永続ポインタ）で head コピーが O(1)。Lean は TM（118本）なので choose-select/init/replayStart は mirror head（A、推奨）か scaffold→PEG 新証明（B）。コウタの判断待ち。choose-select/init/replayStart は head 装置に遅延コピー（mirror＋役割交換 or 駐車ビュー＋オフセット）を 1 回設計。

## 2026-09-23 夜 — Claude Code（Opus 5.5）の進捗と再開点（最新。下の節より優先）

**無条件 PAL ∈ PEG は未完成。`obligation_localRealization` は残る。** ブランチ `feat/lean-pal-report-residuals`（main に未マージ、最新 push 済み）。

### 方針（コウタと合意）
- **上から詰める**: 最終定理から具体機械まで先に接続し、残差を型付きで外に出す。
- **詰まったら事前条件を弱め、事後条件を強める**（Curry–Howard: 引数が多すぎ・事前条件が強すぎを疑う）。
- **デバイス合成**: 仮想デバイス（view=RTQueue+stack、カウンタ、stack、プログラム機械、period/answer）ごとに証明して合成する。`PhysicalDevices.lean`（`encTapes_iff_devices`＋keep 補題、headStep の書き直しで 72→30 行）。
- **正本は Scala 版**: 挙動は `scala/pal` の `ScaffoldGalil` を短い入力で動かして確認できる（報告は `caught` = Scan∧¬replaying∧¬right.canRight∧¬right.gap）。

### いまの最終接続（標準3公理のみ）
`PhysicalReportTest.given_remainingCases_and_frozen rest hcases PhysFrozen hfrozenEnter hfrozenKeep hfrozenQuiet : RecognizedByTotalPEG PAL`。
報告・出力の契約は証明済み（`repW`＝制御の Scan・非replay・onLetterBit ∧ 右 view 窓の `pendingTest` 偽；`encRep`/`encOut`）。
**残差は2つ**: (A) `hcases`＝`TickCases`（実質 `PhysicalDpCleanupDispatch.cases_of_remaining` の `hother`: matched 全体、fallback、restart、prepare/DP reset、init/replayStart/choose-select 等）と `rest` の具体化。(B) 凍結の3欄。

### この日に変えた契約（下の旧記述より優先）
- latch は tick 開始時の状態を読む（報告判定は制御と窓から読める。`LocalLatchRealize.rep_eq` を弱めた）。締め切り `|w|·nLocalL − 1`（Lindley の余裕 τ−2c=80910、`run_on_time_shift_slack`）。
- 受理の契約は答えレベル（`LocalTrackingLatch.tracking_pal_of_oracles`: 健全性＝報告∧output⇒回文、完全性＝回文⇒締め切り前に報告∧output）。`ReportPoint` 一致の旧契約は満たせない形だった。
- 報告判定は `ShadowedLocalFinal.reportCaught`（Scala の caught と同じ）。健全性は trace の `SoundScanNR`（`OutputRel`）、完全性は台帳 `LocalLedgerShift.H_ledger_of_local_oracles_with`（チェックポイントの Scan を運ぶ）。
- `CanonTrace` は `ShapedRun.OracleTick` 版。`PlateauInv.dpDense`、DP 履歴 `PhysicalDpHistory`/`PhysicalDpSource`。
- 余白 margin を広げる案は不可（boot が半径 K ちょうどの余白を作る設計）。

### (A) 静かなモードの接続（2026-09-23 深夜、`PhysicalPhaseLayers` / `PhysicalPhaseStill` / `PhysicalFinalResidual`、Workbench 登録済み・全体 BUILD=0）
- **最終入口は `PhysicalFinalResidual.given_unhandledTicks_and_frozen rest hunhandled PhysFrozen …`**（標準3公理）。`hcases` の代わりに名前付き残差 `PhysicalPhaseLayers.UnhandledTicks rest` だけを取る。
- 処理済み（`cases_of_remaining_quiet`）: 既存7ケース＋ home・markEnd・`ChooseBack`（select でない choose）・`CopyReady`（copy、進む側は walker が読める）・`RewindStep`（rewind の1歩/2歩、atFirst 偽・床に非接触）。
- 仕組み: `QuietPhase`（markEnd/home/fpp/choose/copy/rewind）の tick は全8層を素通し（`forward_quiet_machine`）。Snapshot の保存コピーは `successor_put_quiet` で同じ定理から運ぶ。`¬NeedsLoan` はタダ（静かなモードは scan に戻らない）。
- 鍵は **`coreInv_of_ideal_named`**（事前条件を弱めた版）: chain の counter 10..15・mirror 5・極性10 だけ保存すればよく、VM 名付き counter の形は新しい Enc から取る。これで counter を書き換える copy/rewind が home と同じ形で通った。
- copy と rewind の1歩/2歩の準備条件（walker が読める・床に非接触）は合法 Tick から出る（`copyReady_of_tick` / `rewindStep_of_tick`）。残差は「copy でない」「rewind なら atFirst」だけ。
- **fpp の `hcomp` は run 上で偽**（`GalilScaffoldTape.reset` は `left = []`、fpp 開始時に reset のままのテープがある）。`fpp_of_tick`→`physRule_fpp`→`machineAgree_winMachine` の `MachineAgree.margin'`（抽象テープ左に K 以上）が強すぎる。直し方: `margin'` を外し、左端より先は物理パディングの decode と抽象既定記号 6 が一致すること＋`hfloorRun`（床を越えない）で窓一致を保つ。`margin'` の使用は PhysicalEncoding 内 8 か所。
- 未処理の静かなモード: fpp（上の `hcomp` の修正と `hfloorRun`/`hin` の supplier が要る）、rewind の reset 分岐（退役 FPP bank が reset 済み＝`hidle`、FPP 退役消去の置換待ち）、choose-select、`CopyReady`/`RewindStep` の否定側（run から到達不能を示す）。
- **choose-select / init / replayStart は物理規則に行が無い**（`ruleNext` の choose は `chooseBackNext` のみ、init/replayStart は `_ => q`）。3つとも head の瞬時コピーで、物理層にビュー用 mirror が無い。旧局所層は mirror 入替え/駐車ビュー（`LocalReplaySwap`/`LocalReplayParked`、`H_initLoc` 等が残差）。設計候補は `ASSEMBLY_PLAN.md:985-1033` と `:731-770`（idleHead 強化）。
- 残る大物: scan 側（matched・fallback・restart・DP prepare/reset・探索量子）、`rest` の具体化、凍結3欄。

### Scala 実測（2026-09-23 深夜、全 510 語 長さ≤12 ＋ランダム長さ≤40）
- FPP bank 再利用: 前サイクルの使用長 U ≤ 112、反転間隔 ≥ 272 tick、比 U/間隔 ≤ 0.12（1 マス/tick の消去でも違反 0）。消去期限は余裕。
- choose-select 直前の head 距離 ÷ fallback 開始からの tick: left ≤ 0.2、center ≤ 0.1（違反 0）。replayStart: ≤ 0.4167（違反 0）。1 マス/tick で先回りする mirror で間に合う → 案 A を採用。
- init は 1 語 1 回（boot 直後のみ）。Lean でも init に入る遷移は無い（`initial` のみ）。init 後は scan・chain idle・探索開始なので Loan 層の `Partial` 遷移を伴う。物理規則に init/choose-select/replayStart の行は未実装（`ruleNext` の `_ => q`）。

### freeze の確定設計（2026-09-23 深夜、未実装）
- 凍結後の抽象状態は報告しない（`onLetterTest` が `position+1 ≤ 2|w|` を要求、`frozenAt` は `2|w| ≤ position`）。それでも replayStart が right を center に戻すので物理の沈黙には粘着ビットが要る。
- 包み層 `FreezeWrap M`: 制御に b を足す。`b' = 入力あり ? false : (b ∨ detect ws)`、`detect` = 右 view が gap 上で pending 偽（`pendingTest`）。報告 `repW' = ¬b ∧ ¬detect ∧ repW`。凍結述語 `PhysFrozen := b ∨ detect`（keep・quiet は構成から即）。
- 不変量 `Enc' := Enc ∧ (b → 2·到着数 ≤ front)`。`front = position right + replay`（`GalilRunTrace.front`）は入力なし tick で単調（`GalilFrontMono.front_tick_mono`、要 `FrontPack`・`CentreLive`）。報告時は front = position = 2·到着数 − 1 なので b の間は報告不能。detect なら 2·到着数 ≤ position。
- 6本の TicksWhere は中の機械のまま。包み層が TickCases を持ち上げる。

### (B) 凍結の次の一手（設計済み・未実装）
最後の比較は一致/shift/fallback のどれもありうる（`PlateauInvariant.plateauCompare`）ので「凍結＝飢餓」は偽。代わりに物理側へ粘着ビット b を足す包み層:
b' = (入力あり → false; なし → b ∨ 「tick 開始時に右ヘッドが gap 上で pendingTest 偽」)、報告は `!b && repW`。
凍結後は b が立ったまま（保存は制御だけ）。抽象側との一致は「b 立ち ⇒ caught でない」で、前線（位置＋replay 残り、`front_stepsAll_mono`）の単調性から出す。postPhase の凍結側に「gap・先が空」を運ぶよう強める（`plateauStep` の比較分岐で y.right = right t.right）。

## 2026-09-23 15:05 JST — CodexからClaude Codeへの引き継ぎ

ユーザーの依頼は「証明に向かって邁進。ログに従って続きを」。今回「Claude Codeに引き継ぎしたいので、引き継ぎをCLAUDE.mdに書いて」と指示され、証明の追加作業を区切った。
**次はこの節から再開すること。無条件 PAL ∈ PEG は未完成。** 下の既存本文にある古いPALの仮定・ファイル数・進捗より、この節と更新済み `AGENTS.md` §0を優先する。

### 完成条件と現在の残件

- `lean-pal/PalPeg/PalInPegUnconditional.lean` の `obligation_localRealization` が未放電。
- 最終定理 `PalPeg.PalInPeg.unconditional` は `[propext, Classical.choice, Quot.sound, PalPeg.PalInPeg.obligation_localRealization]` に依存する。
- **完成は4本目を実証明で除き、標準3公理だけになること。** 追加axiom・sorry・admit・native_decideで代替しない。
- 日々の指標は `proof-strategy.md` の39作業項目。**21完了・18未完**。補題数や同じ重さの項目数ではなく、完成率として扱わない。
- 内訳: M0 6/6、M1 7/7、M2 6/6、M3 1/6、M4 0/6、M5 1/8。旧23出口の局所部品は15あり・8未。局所部品ありと最終接続済みは別。
- M3残5: 境界/lastとrestart、init/replayStart/choose-selectの複製、chain誕生、DP12テープ実行、DP/FPP再利用。
- M4残6: matched全体、fallback、探索など残りの分岐を同じdispatcherへ接続。
- M5残7: 完成した同一機械で停止・出力・凍結などを確認し、最終義務を放電。
- 正本の内訳と証拠は `lean-pal/PHYSICAL_KPI.md` と `lean-pal/PHYSICAL_CONNECTIONS.md`。今回の進展もM3-06全体を閉じていないため、21/18を維持する。

### 最新の共通機械と接続面

**`PhysicalDpCleanup.machine rest` / `PhysicalDpCleanup.Enc` が最新の共通機械/符号化。**
旧 `PhysicalLoanDispatch.machine rest` / `PhysicalLoanInvariant.Enc` を包み、DP退役12テープのrewind/clear/home/doneを有限制御に追加した。
同じΓm・118本・micro半径128・macro半径1536・margin1536・ヘッド12段。番号や長さは有限状態に持ち込まない。役割交換は有限なので許可。テープ同値はリテラル等号でなくRep/TEqGを使う。

通常処理の次のlive bit/役割を源窓で読み、その次に退役側となるDPだけを同じ源窓から並行消去する。
各テープは通常処理か消去の一方を採用するので、半径を加算せず1回の実sweepで進む。消去は各テープ最大1536アクション。
`Progress` は密な源からの消去履歴 `Good` と物理表現 `View` を証明側だけに持つ。`ready` は全phase=doneからcanonical resetへのTEqGを返す。
**doneまでに必要な時間が次のlive切替えまでに必ず得られることは未証明。**

接続済み:
- `PhysicalDpCleanup.enc_initial`: 全空白初期状態。
- `PhysicalDpCleanupBoot.forward_feed`: 初回入力を含む全feed。
- `PhysicalDpCleanupBoot.forward_starved`: boot/runningの全starved。
- **`PhysicalDpCleanupDispatch.cases_of_remaining`: 既存7種類のactiveケースを新機械/Encの最終TickCasesへ移行済み。**
  `CountAtRest / CountWatch / CountBackReady / mode=shift / Entry / CountGrow / MatchGrow`。
  watchは全token・両方向・成功失敗を含み、shiftは入口・進行・終了。Grow/MatchGrowは正のworkに限る。
- `hother` は同じ7除外条件を持つ未実装ケース。今回の移行で残差は減らしていない。合法Tick、ArrivedOnRun、canonical traceを保持している。

`PhysicalDpBank.machine` は現在のLoanDispatchの全有限窓分岐について、dpLiveと両DP bankの物理アドレスの保存を証明した。到達性やEncを仮定しない構造的な証明。
**これは現在の機械にはDP reset/flip行が未接続だから成立する。** 新たなreset行を接続するときは、その行を別扱いし、全行がbankを保持すると誤って仮定しないこと。
`PhysicalLoanDispatch.active_of_remaining` に既存ケースの本体を切り出した。局所的な残差継続を受け取るので、新Encへの移行に「全ての旧Enc状態で新Encも成立する」という偽の前提は不要。旧cases APIも保持。

### 今回追加・変更して検証したファイル

すべて `lean-pal/PalPeg/`。新4モジュールはWorkbenchへ登録済み。

| ファイル | 内容・主な出口 |
|---|---|
| `PhysicalDpBank.lean` | 合成/反復/有限役割/dispatcherを通じてDP bankを保存。`machine` |
| `PhysicalDpCleanupDispatch.lean` | `forward_of_previous` / `forward_handled` / `cases_of_remaining`。同じ7ケースを新Encへ接続 |
| `PhysicalDpPreload.lean` | **ロード途中の任意prefix**で12テープすべてDense。`dense_onRun` / `prepare_run_size` |
| `PhysicalDpRetirement.lean` | 共通Loan Encからlive DPのTEqGを取り出す `live`。途中ロード/実行中から消去開始へ `forward_preparing` / `forward_program` |
| `PhysicalLoanDispatch.lean` | `active_of_remaining`を抽出し既存casesを再利用可能にした。ケース被覆は変更なし |
| `Workbench.lean` | 上記4モジュールのimportを追加 |

`PhysicalDpPreload` の不変量は、全テープの非空白接頭辞＋空白接尾辞、lower/copyの書込みhead=最初のblank、copy開始まではtape7=reset。
実 `GalilScaffoldPrepareControl.Tick/Run` のlower→lowerHome→copy→home→runで保存し、disabled tickも扱う。
完成済みpreloadは仮定しない。各テープのleft+right長は `1 + bs.count true` 以下。

`PhysicalDpRetirement.live` はsnapshotによる旧探索カウンタ差し替えと、radiusの部分鏡再建の両方を扱う。
`forward_preparing/program` はこの源のTEqGと実Run由来のDenseを `PhysicalDpCleanup.forward_retired` へ渡す。
**これらはreset行完成の証明ではない。** 現在も通常行の後状態Loan Enc・その実step等式・bank flip/役割保存・準備/プログラムRunを引数に取る。
PAL全体のOnRunから当該Runを供給し、通常reset行を実装してこれらの引数を証明する仕事が残る。後状態Encを新しい義務として仮定して完了扱いしないこと。

### 直前までに完成した基盤（必要時だけ読む）

- `PhysicalProgramErase`: 有限rewind/clear/home/done消去器。Denseから `3*(left.length+right.length)+5` 回以内にresetへTEqG。`bank_real_reset` は実sweep反復まで証明。
- `PhysicalEraseBatch`: n回を半径nの1sweepへ融合。`stored` / `Good` / `good_run` / `done_clean`。
- `PhysicalRetiredDpFrame.loan`: 退役DPだけの変更を旧共通Encへ通す（marginも保存）。
- `PhysicalDpCleanup`: `apply_running` / `forward_kept` / `forward_retired`。源の実表現から消去状態を保存。
- `PhysicalDpCleanupBoot.boot_banks`: 実blank bootが両bankをblankにする証明。後状態を仮定しない。
- `GalilDpDenseMarks` / `GalilDpDensityTable` / `GalilDpDensity` / `PhysicalDpDensity`: 任意Fin3入力・lowerの実preloadから、任意program実行prefixのDP12本/FPP9本がDense。MARKS8/9のheadがfrontierを越えるため単純head上限は使えない。既存prepared完成形と実行一意性からemit位置を供給した。
- `PhysicalDpDensity.bank_reset_onRun`: 実enabled call数でサイズを上から抑え、指定された消去回数でresetへつなぐ。指定回数の利用可能性は別義務。

### 次の着手点・未解決の山

1. **PALの実行からDPの履歴を供給する。** `FrameFunction.searchStepFun` と `GalilScaffoldPrepareControl`、program quantumを結び、任意の退役時に準備途中またはpreload後のprogram Runを得る。初期resetも扱う。
2. **再liveまでの消去期限。** 消去器の完了上限と実際のbank再利用間隔を結ぶ。stage所要時間の「上限」を利用可能時間の「下限」と取り違えない。
   `GalilDpCost` の3186*word.length+1683、`GalilScaffoldTimingCost` のrunBudget/first_stage_ticks/later_stage_ticksは上限。現時点で期限証明には接続していない。
3. **prepare/reset・restartの実行行。** prepareはpc320でDP全reset、tape10へLEFT/right、work=lower、walker=centerを同時実行。後のspan→workも含めaliasを有限役割/既存鏡で実装する。追加抽象tickや瞬間コピーを入れない。
4. 残る探索モード、search出口の部分鏡不足1補完、不一致/fallback、matched全体、chain誕生、init/replayStart/choose-selectなどを同じ機械へ追加。
5. FPP退役側の旧左向き消去も置換が必要。旧eraseActはrootで止まり右側を消さない。live時のDenseを、旧消去が既に穴を作った退役FPPへ適用してはいけない。

先に別レイアウトの部品を作って統合し直す方針へ戻らない。今ある共通機械・Enc・TickCasesの接続を維持する。
サブエージェントは使用していない。ユーザーは進捗を補題数で飾らず、完成/未完を正確に分けることを重視する。

### 最終検証と再開コマンド

2026-09-23、この引き継ぎ直前に実行:

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal
. ~/.elan/env
lake build PalPeg.Workbench
lake env lean PalPeg/Axioms.lean
```

- **Workbench BUILD=0、9810 jobs。** `/tmp/physical-dp-retirement-workbench.log`
- **最終公理監査 AUDIT=0。** `/tmp/physical-dp-retirement-axioms.log`（空ログが正常）。追加公理は依然1本残る。
- 今回の新10個の公理guardは標準3公理以内。対象5ファイルにsorry/admit/native_decide/新axiomなし。
- `git diff --check` 通過。ビルド/Leanの実行ジョブは終了済み。

### 実装時の注意・ワークツリー

- **大量の未追跡Leanファイルと既存の変更がある。すべて作業成果で、git reset/cleanで消さない。** 今回commit/pushはしていない。同じローカルcheckoutから引き継ぐこと。
- `lean/` と `lean-pal/` は別toolchain。ここは後者。`make verify`だけでは今回のモジュールを検証できない。
- 新モジュールは `PalPeg/Workbench.lean` に登録。単体だけ通して全体build済みとは言わない。
- 具体的な12段融合をchange/rfl/simpaで直接比較するとheartbeatが膨張する。規則/idealRun関数全体を関連仮説と目標で同時にgeneralizeし、一般補題を先に使う。
- `PhysicalEraseBatch.step` はirreducible。`PhysicalDpBank` の `feedStep`、CleanupDispatchのLoanDispatch.machineにもlocal irreducibleを用いて巨大展開を避けた。
- `!b = c` はLeanで `!(b = c)` に読まれ得る。Bool反転の等式には `(!b) = c` と括弧を付ける。
- `CLAUDE_RESUME.md` / 台帳末尾は詳細履歴。古い「全active移行未完」「ロード途中未検証」は今回この節で更新済み。

---

## リポジトリの全体像

3 つの独立したサブプロジェクトが同居している。互いに toolchain が違うので混ぜないこと。

| ディレクトリ | 内容 | toolchain |
|---|---|---|
| `lean/` | **Shallot**（PEG フレームワーク + 第一階関数型言語の仕様・実装・証明）と **Lens**（Lean 4 → Scala 3 抽出器） | Lean v4.32.0、外部依存ゼロ（Mathlib 不使用） |
| `scala/` | Lens の抽出結果（`generated/`、コミット済み）、手書きランタイム、CLI、差分ハーネス、`pal/`（Python 版 PAL 生成器の Scala 3 移植） | Scala 3.7.4 / sbt 1.x |
| `lean-pal/` | `PAL ∈ PEG` の Lean 証明（Kim–Park 成果物 `PegSeparation` 経由、**条件付き**） | Lean v4.31.0 + Mathlib v4.31.0（pinned） |

`docs/palindromes-in-peg/` は素の PEG で回文言語を書く構成のアーティファクト（Python が参照実装、Rust runner、検証ログ）。入口は `STATUS.md`。

## よく使うコマンド

`lake` は `~/.elan/env` を source しないと見つからないことがある（Makefile は自動で source する）。

### 全体検証（`lean/` + `scala/`）

```sh
make verify        # audit → lean build → lake test → drift → sbt test → 差分ハーネス群
make verify-fast   # 証明中の反復用: audit + lake build のみ
make audit         # scripts/audit-source.sh: sorry/admit/native_decide/axiom を lean/ から排除
make lean          # cd lean && lake build（= 全証明 + Audit.lean の公理監査）
make lake-test     # Lens の golden テスト（lean/tests/golden/Shallot.scala と diff）
make regen         # Lens で scala/generated を再生成（コミット対象）
make check-drift   # コミット済み generated が fresh extraction と一致するか
make scala         # cd scala && sbt -batch test
make diff / json-suite / macro-peg-diff / counterexample-diff   # 差分ハーネス各種
make corpus-golden # golden 再生成（意図的な操作。git diff でレビューする）
```

Lens golden の更新: `cd lean && LENS_UPDATE_GOLDEN=1 lake test`（その後 git diff を確認）。

### lean/ 単体

```sh
cd lean && lake build              # defaultTargets = Shallot + Lens
cd lean && lake build Shallot.Peg.Soundness   # 単一モジュール
cd lean && lake exe extract --out <dir> --pkg shallot.gen
```

### scala/

```sh
cd scala && sbt -batch test                       # 全サブプロジェクト
cd scala && sbt -batch "pal/test"                 # PAL 移植のみ（直列実行、-Xmx8g）
cd scala && sbt -batch "shallotCli/run run ../examples/fact.shl"
cd scala && sbt -batch "shallotCli/run eval \"1 + 2 * 3\""
cd scala && sbt -batch "pal/testOnly pal.SomeSuite"   # 単一スイート
```

この WSL2 環境では sbt が `/run/user/1000` の AccessDenied で起動しないことがある。回避: `mkdir -p /tmp/xdg-1000; XDG_RUNTIME_DIR=/tmp/xdg-1000 sbt -batch ...`。

### lean-pal/

```sh
make lean-pal                                   # 初回: Mathlib cache 取得 + build
cd lean-pal && lake build --quiet PalPeg        # 通常の反復
cd lean-pal && lake build PalPeg.GSScan         # 単一モジュール
```

`make verify` には**含まれない**（Mathlib cache のダウンロードが必要なため）。全体ビルドは 9,000 job 超で長い。

## アーキテクチャ上の要点

### lean/ — Shallot と Lens

- `Shallot.lean` がルート import。新モジュールはここに追加しないとビルドも監査も通らない。
- 具体構文パーサは「検証済み汎用 PEG インタプリタを文法値に適用したもの」であり、PEG の soundness/completeness/determinism がそのまま Shallot パーサに効く。JSON（`lean/Json/`）と Macro PEG（`lean/MacroPeg/`）も同じ枠組み上に載っている。
- `lean/Audit.lean` の `#guard_msgs in #print axioms` ブロックが公理監査の本体。ビルド成功 = 標準 3 公理（`propext`/`Classical.choice`/`Quot.sound`）以外を使っていない証明。旗艦定理を足したらここにも guard を追加する。
- ポリシー: `sorry`/`admit`/`native_decide`/追加 `axiom` は禁止（`scripts/audit-source.sh` がソースレベルで、`Audit.lean` が意味レベルで弾く）。
- **Lens の抽出可能サブセット**は `docs/extractable-subset.md` に凍結されている。抽出対象コードでは `partial def`/`unsafe`/`opaque`、添字付き inductive、Prop を運ぶコンストラクタ、`do` 記法（明示 `match` で書く）、whitelist 外の typeclass は使えない（fail-loud）。
- `scala/generated` は**コミット済み**の生成物。Lean 側を変えたら `make regen` → 差分をレビュー → コミット。`check-drift` が CI 相当の門番。
- 差分ハーネス（`corpus/`）のケーステーブルは Lean で一度だけ定義され、抽出される。Lean-native 実行と抽出 Scala 実行が `corpus/golden/*.jsonl` と三者一致することで、抽出器・ランタイム・評価器のドリフトを検出する。
- TCB: Lean カーネル、Lens、手書きランタイム `scala/runtime`（`shallot.rt`）、Scala コンパイラ、JVM。

### scala/ の sbt 構成

`runtime`（strict lint）→ `generated`（lint 免除）→ `shallotCli`（strict）。`macroPegRef` は vendored 参照実装（lint 免除、`UPSTREAM.md` 参照）、`macroPegDiff` はその独立差分ドライバ、`pal` は Python 生成器の移植でテストは Python 出力とバイト一致を比較する。手書きコードは `-Werror -Wunused:all`。

Scala 3 は**ブレース構文で書く**（indentation syntax / `then` / `end` は使わない）。サブエージェントに書かせるときも指示に含める。

### lean-pal/ — PAL ∈ PEG

- 唯一の仮定は `PegSeparation.RealTimeTM.RecognizedBy PalPeg.PAL`（厳密実時間多テープ TM が PAL を認識すること）。Galil 機械をこのモデルに書き下す作業が進行中で、無条件の `PAL ∈ PEG` は**未完**。対外的な言い回しは「条件付き」を崩さない。
- `PalPeg.lean` がルート import。`PalPeg/` には未 import・未追跡のモジュールが大量にある（追跡 110 / 実在 500 超）ので、`lake build --quiet PalPeg` が通ったことと「そのファイルがビルドされた」ことは別。新モジュールは必ずルートに追加する。
- 公理監査は `PalPeg/Axioms.lean` の guard。`lean/` の `audit-source.sh` は `lean-pal/` を**見ない**ので、こちらでは `sorry` 排除を自分で確認する。
- 層構成（下から）: 語の組合せ論（`Words`/`Groups*`）→ 仕様（`Chain`/`Stages`/`Assembly`/`OnlineMachine`）→ GS 分解・前処理（`GSScan`/`GSDecomp*`/`GSPreprocess*`）→ 実時間照合（`GSRealTime`/`GSVerifier*`/`StageMatcher`）→ 中央フラグ（`Manacher*`/`MiddleJob`/`BorderJob`）→ スケジューリング（`RTQueue`/`Schedule`）→ テープ化（`TapeLib`/`*Tapes`）→ 有限制御 `ProgLang` 移植（`*Prog*`）。詳細は `lean-pal/README.md` の「ファイル構成」。
- 設計・現状の正本は `lean-pal/ASSEMBLY_PLAN.md`（組み立て方針、新しい順に追記）と `lean-pal/DESIGN_SCA_PAL.md`、`ALGORITHM_SPEC.md`。
- 旧制御層は `lean-pal/archive/single-prog/` に退避済みでビルド対象外。

## lean-pal 無条件 PAL ∈ PEG の進捗（2026-09-19 時点）

**進捗の計器は `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL` の公理リスト。**
目標は閉じた項として存在し、足りない義務は `axiom` で明示されている。
`PalPeg/Axioms.lean` の `#guard_msgs in #print axioms` がラチェットで、
1 個外すと guard が壊れて更新を強制される。**標準 3 公理だけになったら §10.5 達成。**
いまは **1 個**の義務が残っている（2026-09-19, n175 で 4 → 3、n246 で 3 → 2:
`obligation_shiftPalResiduesAlongRun` は `WindowPack.shiftPal_of_windowRunPack` で証明。
2026-09-20, n282 で 2 → 1: `obligation_cycleOracleOnPackedRun` は定理
`PalInPeg.cycleOracleOnPackedRun`＝`OracleReady.cycleOracleOn_of_readyLeaves` になった）:
`obligation_localRealization`。経路は `PalPeg/PalInPegUnconditional.lean` の
docstring に表で記録。

**trace 形は run 形から導けた（n175）。** trace は `st 0 = boot w` から始まるので
`st 1` で `InvLPC` が立ち（`GalilTrailFront.inv_of_boot_tick` ＋
`GalilOracleMC2.invLPC_of_boot`、`BranchSupply.cpack_alongTrace` と同じ recipe）、
`GalilTrailFront.steps_between` で `st j`（`1 ≤ j ≤ Tc`）に届く。
**新しい定理は 1 本も書いていない。既存部品を繋いだだけ。**

**2026-09-19（n112→n113）: 旧 `obligation_shiftPalAtScanStates` は偽の疑いが濃かったので
run 形／trace 形の 2 つに割った（3 → 4）。**
`ShiftPal` の結論は「chain の周期が入力語 `w` の本物の周期である」という履歴の事実だが、
guard の `BigPack2MG7W` の場を一次情報で全部展開したところ、chain の周期テープの中身と
`w` を結びつける場が 1 つも無かった（`w` に触れる場はヘッド、chain に触れる場はカウンタ）。
`hpack` が偽だったのと同じ欠陥で、CLAUDE.md 自身が `ShiftPal` を過剰量化の 5 例の
1 番目に挙げていた。機械検査した反証はまだ無いので `REFUTED` とは書いていない。

**差し替え済み**（n113）: `obligation_shiftPalAlongRun`（`InvLPC` 起点から到達する
scan 状態）と `obligation_shiftPalAlongTrace`（`PreTraceIMW` の trace の scan 点）。
どちらも履歴が run で固定されるのでこの欠陥は無く、放電器も用意してある
（`ShiftPalAlongTrace.shiftPal_alongTrace` / `CloseoutBundleRun.shiftPal_of_run_B`、
残差はどちらも `H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `periodOnly = false` 分岐）。
**偽の疑いが濃い前提 1 個より、真であろう前提 2 個を採った。** 詳細は `CLAUDE_RESUME.md` n112/n113。
`marksEntry` は 2026-09-19 に放電（`CloseoutMarksPack.packRunR_MW_marksFree`、n110）:
唯一の消費者だった `packRunR_MW` の 2 箇所は `MarksInv'` を作るためだけにあり、
`CloseoutPackRun17.marksInv'_of_run'` が `H_marksEntry'` なしで run 全点に
それを与えていた。4 入力（`first ≠ 4` / `hfloor_of_invLP2` /
`windowInOrigin_alongRun` / `cpack_of_entry`）は `InvLPC` の origin で全部無償。
`WindowInOrigin` の障害だった `Fair` は、モデル欠陥 `M-fallbackPlace` を直した
時点（n107）で消えていた。
**「`hme` の producer は `hpack` だけ」という過去の自分の記述を一次情報として
扱っていたせいで 1 日以上見落とした。**

**guard を狭く切ると義務が増える。** 2026-09-19 に `ChainPositionInvariantWithShiftPhase.payload`
の guard が `ScanNR`（`mode = scan ∧ replaying = false`）だったせいで replay 中の
台帳が抜け、その穴埋め用に `MatchRest.replayPay` という義務が立っていた。
guard を `mode = scan` に広げたら**義務ごと消えた**。同型の例が 8 件
（`LagCan` は `.watch` だけ / `CentreRep` は `rewind ∨ replayStart` だけ /
`VerRep` は `.watch` だけ …）。**新しい場を足す前に、既存の guard が必要以上に
狭くないかを見る。**

**run 形（`∀ z, Steps j x z → …`）と trace 形（`∀ i ≤ Tc, … (st i) …`）は別物。**
`Tick` は決定的でないので trace 形から run 形は出ない。run に沿う事実は trace 形で書く
（`obligation_verifierRunAlongRun` が落ちたのはこの切り直しだけが理由）。

**自分が書いた義務も過剰量化しうる。** 2026-09-19 に `obligation_matchRest_alongTrace` の
場 `canRNext`（`canRight (right s.right)` を trace 全域で、mode guard なし）が
**偽**だと機械検査で確定した（`MatchRestRefute.matchRest_alongTrace_false`）。
報告点は `position right = 2|w| − 1` ちょうどなので 2 歩分の余裕は原理的に無い。
**「着地状態の性質」を「源状態の性質」として書くと 1 歩ぶん強くなる。**
義務を書く前に、消費者がその分岐で何を要求しているかを読む。

* 公理は**1 場ずつの原子**に分解する（束ねると「1 個外す」が測れない）
* 義務は**trace 形**で書く。global 形（`∀ c s`）は放電の材料が run に沿ってしか
  存在しないので**原理的に落ちない**（`hpack` / `hav` が偽だったのと同じ病）
* `pal_in_peg` という名前は無条件の最終定理のために予約。部分結果は
  `PalInPeg.given_<残差>`

### 旧記述（前提を数えていた時期のもの。上の計器に置き換わった）

**状態: 全体 build 成功・標準公理のみ・無条件 PAL は未完。正本の最上位は `pal_in_peg_final39`（`CloseoutFinalFour`、**7 前提・反証済みゼロ**: `hSP` `hme` `hor` `hC` `hbgP` `hmatchP` `hsdP`。2026-09-19 に `hfour` を**何も足さずに**放電——`CloseoutPackRun40.ChainPosInv'`＝`Coupled` を `Coupled'` に強めた構造が `four_of_other'` を直接使えるため、`ShiftLocalRun` が run に載せた。索引の別名は `Canonical.pal_in_peg_of_seven_leaves`）。一代前は `pal_in_peg_final30`（`CloseoutFinalW`、8 前提、`hfour` を含む）。`hfour` を落とした既存 3 版はどれも代わりに**偽の前提**を取っていた: `final31` は `hav`（`ConsumeAvailRefute.hav_false`、過剰量化の 8 例目）、`final36`/`final37` は `hpack`（`CloseoutPackRefute.hpack_false`）。`pal_in_peg_final37`（`CloseoutFinalW4`）は 4 前提だが `hpack` が**偽**（`CloseoutPackRefute`、2026-09-19 反証）——`ChainPack` は run 沿いの束を一状態述語として書いており `ChainPosInv2` からは出ない。よって 8 → 4 の削減は偽の前提を通っており、前進として数えない。計画書 §10.5（前提ゼロ）は未達。** 全モジュール sorry なし。新モジュールは `PalPeg.lean` の `import PalPeg.GalilSegmentConstruct` の直後に登録。

### 1. 最上位の定理と残りの仮定

| 定理 | ファイル | 仮定 |
|---|---|---|
| **`pal_in_peg_final37`** | **`CloseoutFinalW4`** | **4 前提**: `hSP`（scan 状態の `ShiftPal`）, `hor`（`CycleOracleMC3`）, `hC`（`H_realizeLIMW'`）, `hpack`（`ChainPosInv2 → ChainPack`）。`final25` の 8 前提のうち `hsc`/`hws`/`hsl`/`hni` は**反証**、`hee`/`het` は `front` ポテンシャルで証明、`hme` は `hpack` の `marks` 場に包含。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
**残差は 3 つの壁に統合（n77）**: (1) `ScanToScan`（run の区間分解、`CloseoutSegment`）— `hSP` のラウンド境界・最初のラウンドと `hor` の found 葉（`ShiftRoundC`）がここに帰着、(2) `hC`（`H_realizeLIMW'`）、(3) `hpack` のモデル欠陥 (e) 部分（`marks`/`hwin`）。`hor` の橋は `CloseoutOracleBridge.hor_of_H_oracle`、`H_oracle` の葉は `CloseoutOracle8.h_oracle_of_leaves7` で 11。
| **`pal_in_peg_final30`** | **`CloseoutFinalW`** | **8 前提・反証済みゼロ**: `hSP`, `hme`, `hor`, `hC`, `hfour`, `hbgP`, `hmatchP`, `hsdP`。`final29` の `hsl`（`ShiftLocalG`）も偽だったため（`beginShiftVM'` は `shiftGuardVM` を含まない）、弱化ではなく**場ごと削除**。wave 8 で trail 橋を `ChainPosInv` に載せ替えた結果 `IPackMG.shift` を読む者が消えたので可能になった。非破壊複製: `CloseoutPackW`（`IPackMW`）/ `CheckW` / `OracleW`（`packRunR_MW` は shift 仮説ゼロ）/ `FinalW`。`hC` は `PreTraceB` を取る `H_realizeLIMW'` へ |
| **`pal_in_peg_final29`** | **`CloseoutWeakFinal`** | **9 前提・偽の前提ゼロ**: `hSP`, `hsl`（`ShiftLocalG`）, `hme`, `hor`, `hC`, `hfour`, `hbgP`, `hmatchP`, `hsdP`。`final27` の 5 前提のうち `hws`（`∀ w y, WatchShiftG`）は **偽**（`CloseoutPackRun32`: `ChainStep.backDone` 生まれの watch は `distance = reset`）。2 つの弱化で除去: trail 橋を `ChainPosInv` に載せ替え（`CloseoutShiftS`/`ShiftFinal`）、pack 側は必要な `ShiftLocalG` を直接取る（`CloseoutShiftWeak`）。後ろ 4 前提は Run34 の guarded 分岐仮説 |
| **`pal_in_peg_final27`** | **`CloseoutExtraFinal`** | **5 前提**: `hSP`, `hws`, `hme`, `hor`, `hC`。`final26` の 7 前提から `hee`/`het` が消えた。理由: 両者は `packRunR_MG27` の `hprefix`（run 各点の `Extra7`＝`canRight`）を作るためだけに存在し、その上界は front ポテンシャル（`front = position + replay value`、`front_stepsAll_mono` で単調、非 replaying では `front = position`）に乗って run の出口から遡る。出口の上界は `CycleOutMC3` の定義と `ReportPointAt.atPlace` が持つ（`CloseoutFrontExtra`/`ExtraFree`/`ExtraOracle`） |
| **`pal_in_peg_final26`** | **`CloseoutStageFinal`** | **7 前提**: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。`final25` の 8 前提から `hsc`（`H_stageScan`、反証済み）が消えた。理由: `CycleOutMC3` は両出口で `InvLPS` を返しており（`GalilInvPlus3:193, :212`）、boot も `Inv` 分岐に着地する（`invLPC_init:94`）。チェックポイント層を `InvLPS` 上で再走させれば `hstage_of_scanBranch` は呼ばれない（`CloseoutStageCheck`/`StageBoot`/`StageOracle`）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| `pal_in_peg_final25` | `CloseoutPackRun51` | 8 前提: `hSP`（scan 状態の `ShiftPal`）, `hws`（`WatchShiftG`）, `hee`（`Extra7` 入口）, `het`（`Extra7` tick）, `hme`（`H_marksEntry'`）, `hsc`（`H_stageScan`、**反証済み**・再切り出し待ち）, `hor`（`CycleOracleMC3`）, `hC`（`H_realizeLIMG2'`）。`final24` の 11 前提のうち `hbs`/`hls`/`hsl` は木の中の定理で供給済み（`InvLPC` の chain は常に idle → `ShiftLocal*` は空虚）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| `pal_in_peg_final24` | `CloseoutPackRun46` | `hSP`（scan 状態の `ShiftPal`）, `WatchShiftG`, `Extra7`（`scanAvail` のみ）入口/tick, `H_extraEntry3/Tick3`, `H_marksEntry'`, `H_shiftLocalG`, `H_realizeLIMG'`, `H_shiftLocalC`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIM'`（最上位。found 葉は `foundExit_compare_final9`、readiness は `PostRunC`、核は `chooseVm_tapeActK`；詳細 `CLAUDE_RESUME.md` n74；残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`；**モデル欠陥: chain 誕生で `periodOnly` 未リセット（修正保留）**；readiness 帰納段 `postRunF_step` 成立；found 葉は `foundExit_compare_final14`（`FoundExitLPS`）、readiness 往復は `galilFrameS` 上で閉、core `shiftVm_tapeActKQ` K=28）；`BigResid6` は `bigResid6_of_lpackM2`（残 `ShiftPal`・`WatchShift`）；readiness は `PostRunF` 往復（Preload31）；readiness は `ScanRealized` 矛盾（n49）で `PostRunPh/F` へ再基底化中；rewind 角は `MarksEntry` 1 点；found 葉は `foundExit_compare_final19`；`ShiftLocal` は反証→`ShiftLocalG`（final16、`IPackMG` 再配線中）；`rewindMargin` は `CentreMargin` 1 葉に集約、`.double` 出口義務は Scala に合わせ再定式化要） |
| `pal_in_peg_final4` | `GalilFinalAssembly4` | `H_oracle2`（boot 側 oracle、`CycleOracleMC2C`）, `H_needLB'`, `H_realizeLB'` |
| `pal_in_peg_final2'_trailF` | `GalilTrailProof` | `H_oracle`, `H_trailF`, `H_base`, `H_realizeL'` |
| `pal_in_peg_of_local_core` | `LocalLatchRealize` | 局所 oracle（`LocalSysConcrete.localSys_oracles` の残差）+ `H_ledger`（`LocalLedgerShift` で放電済み、`habs`/飢餓同値が残り） |

- `H_oracle2` ← `GalilFinalAssembly4.h_oracle2_of_leaves` ← `GalilOracleMC3.h_oracle_of_leaves''`（`hquiet`/`houtReplay` 除去、`hfoundReplay` 追加）。葉の現状は §3。
- **重要（2026-09-19 訂正）**: `h_oracle_of_leaves*` は**全部** `GalilFinalAssembly.H_oracle`（= `CycleOracleMC`、origin/着地とも `InvL`）を結論とする。最上位の `hor` は `CycleOracleMC3`（origin/着地とも `InvLPS`）で**別物**。橋は `CloseoutOracleBridge.hor_of_H_oracle`（`H_oracle` ＋ `InvLPS` 着地 lift）。差は 2 つ（不変量と、中心進行 vs `mu` 進行）。**型名の一致で producer を判断せず、定義を展開して origin と結論の不変量を照合すること。**
- **重要（2026-09-19 追加、同じ欠陥の 5 例目）**: 名前付き葉が偽になる典型は「唯一の消費者が到達しない状態まで量化している」こと。`ShiftPal` / `H_advanceT` / `MatchTickC` / `hpos` / `ShiftAtMismatchC` が全部これ。**新しい葉を測るときは、まず消費者のその分岐で何が scope に入っているかを読み、それを文に入れる。** `ShiftAtMismatchC` の場合は `SegEndS` の出口が「cycle 終端 ∨ 不一致」の選言で、不一致側では cycle 終端が未知なのに葉が主張していた（Scala `ScaffoldGalil.scala:254` の `canShift` は `periodOnly` のとき `singlePositive cycle` を要求し、周期中の不一致では `beginFallback()`）。反証は `CloseoutShiftMismatch.shiftAtMismatchC_false_at_nonterminal`、再定式化は `ShiftAtMismatchN` / `roundOne_of_segRun_N`。
- `H_needLB'` ← `H_trailF`（`GalilTrailProof`）← scan 側 `GalilTrailScan/Budget/Front/Sane/Order` + verifier 側 `GalilTrailChain/Assembly`。残りは scan 不変量 pack `RadPack`（`GalilTrailRad`、進行中）1 つに集約。
- `H_realizeLB'`: 局所実現。`LocalSysConcrete`（tick/到着/stutter/出力 oracle は無仮定）、`LocalRealizesScan`（rewind/choose 閉）、`LocalRealizesPhase`（shift/copy/home/markEnd 閉、fpp は局所 1 量子のみ残）。**scan/init/replayStart は抽象 tick の非決定性で閉じない**（§2）。

### 2. 設計上の重要事実（2026-09-17 深夜〜朝に判明）

- **訂正（2026-09-19）**: 下の「`radiusAfter`（search 活性∧chain idle なら不変）」は
  **古い**。一次情報 `PalPeg/GalilScaffoldTopSearch.lean:37` は
  `def radiusAfter (s : GalilVM) : Counter := GalilScaffoldCounter.inc s.radius` で
  **無条件の `inc`**。`backgroundS` は右ヘッドも radius も変えないので
  `position center + value radius = position right` は background で保存され、
  matched compare では両方 +1。**過去の自分の記述を一次情報として使わない。**
- **`Fair` 完成（`GalilTickFair`）: `Tick ∧ Fair` は全状態で一意、残差なし。** 抽象 `Tick` 単体は一意でない（`GalilTickDet`）: (a) broken chain で `restart` と `scan_wait` stutter が競合（Scala は restart 優先）、(b) 探索量子は `ReadFun GalilDpCode.code` + `PrepareControl.Tick` 決定性を仮定すれば関数的、(c) chain は関数的、(e) `beginFallbackVM'`（着地場所）が非関数的。
  **訂正（2026-09-19, n171）: `initVM`/`replayStartVM` は `periodOnly`/`walker` を自由に
  していない。** 定義（`GalilScaffoldTopReplay:20,33`）の 15 連言の最後 2 つが
  `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` で、既に固定されている。
  よって `Fair.keepsSearchCursor` は `Tick` からタダ（`tick_init_cases` /
  `tick_replayStart_cases` で `initVM`/`replayStartVM` を取り出すだけ）。
  `Fair` の実質は 2 場: `restartFirst`（broken chain のときの restart 優先。
  `restartGuardVM` が `chain = .broken w` を要求するので broken chain のない区間では空虚）と
  `fallbackPlace`（`beginFallbackVM'` が place `p` を長さ上界だけで縛っているのが原因。
  実機は search の walker から一意に計算するので、これは**形式化のミス**——
  `beginFallbackVM'` に `t.fpp.walker = t.walker` を足せば消える）。`tickFun`（`GalilTickFun`）は choice で 1 つ選ぶだけ。**方針**: モデルは編集せず（使用箇所 300 超）、Scala の優先順位と固定値を表す `Fair` を定義して `Tick ∧ Fair` の一意性を証明（`GalilTickFair`、進行中）。構成側の witness と局所 step が `Fair` を満たすことを別途確認。
- **偽だった葉（同じ型: 任意状態への量化）**: `hquiet`（`SearchQuiet` は「found に到達しない」と同値、`GalilLeafQuiet`）、`houtReplay`（`InvScan` に出力なし → `InvScanO := InvScan ∧ OutputRel`、`GalilLeafOutReplay`）、`hpres`（`SearchReady` は負債 1 単位分保存されない → `SearchReadyB := ReadyRem ∧ RunEntriesAll`、`GalilLeafPres`；`watchSegE_construct` は再証明要、`GalilSegmentConstructB` 進行中）、`hpos`（区間終端の右ヘッド位置、`GalilLeafPos`: 区間予算 `position r.right + count true ≤ 2m−2` から出す）。
- **過剰量化の 8 例目（2026-09-19）**: `pal_in_peg_final31` の
  `(hav : ∀ w (st : ℕ → State GalilVM) (i : ℕ), ConsumeAvail (st i).vm.chain)`。
  `st` が無制約関数なので `∀ z : ChainVM, ConsumeAvail z` と同値で、
  `gap = false` かつ右も incoming も空な verifier を持つ watch で破れる
  （`ConsumeAvailRefute.hav_false`）。正しい形は run 形の `CloseoutVerSide.VerRun`。
  **run に沿う事実を `∀ st` で書くと、常に状態全体への全称に潰れる。**
- **過剰量化の 7 例目（2026-09-19、自分で撒いた）**: `M-watchBreak` 修正の下流で
  `(hnobg : ∀ w' v, ¬ BreakStepPos w' v)` と書いたが、`BreakStepPos` は「正 lag ＋ 不一致」
  なのでそういう `w'` は存在し、**この前提は偽**。義務は必ず**状態局所**に書く
  （`NoBgBreak x := ∀ w v, x = .watch w → ¬ BreakStepPos w v` を run の各点や不変量の場として
  持たせる）。`∀ w' v, ¬ BreakStepPos w' v` と書いてはならない。
- **モデル欠陥 `M-watchBreak`（2026-09-19、機械検査済み）**: Scala 正本
  `ScaffoldChain.step()` は `Mode.Watch` かつ `lag.sign > 0` で `consume()` を呼び、
  不一致なら `Mode.Broken` に落とす（`ScaffoldChain.scala:136,178`）。Lean の `ChainStep`
  には `.watch → .broken` の構成子が無く、break は `ChainMatched.breaks` にしか無い上に
  その `BreakStep` は `zero w.lag = true` を要求するので **lag ゼロ経路のみ**。結果、
  正 lag ＋ 不一致の watch に**後続状態が存在しない**（`PalPeg.ChainStepGap.
  no_chainStep_at_positive_lag_mismatch`）。**これが `WatchOk` が偽である根本原因。**
  直すには `ChainStep` に正 lag 版 break を足す（影響 202 箇所、`M-periodOnly` と同規模）。
- **`WatchOk` は 2026-09-19 に無条件で反証された（機械検査済み）**: `PalPeg.WatchOkRefute.watchOk_false`
  （引数は `WatchOk Ok` のみ、公理は `propext`/`Quot.sound`、`sorryAx` なし）。`born` が
  **任意の lag/margin** で `Ok` を与え、`good` がその正 lag で `Good`（period テープの焦点記号と
  入力右ヘッドの記号の一致）を強制するが、`born` の仮説（`canRight ver` と `OnBlock v`）は
  両者を関係づけない。証人は `bornVer`/`bornBlock`（`symbol (moveRight bornBlock).focus = some 0`
  と `read (right bornVer) = some 2` をカーネルで計算）と `lag = ⟨[0],[]⟩`。
  `born` の過剰量化は `ChainOk` の設計が強制している（`| .back v _ _ _ ver => OnBlock v ∧ canRight ver`
  が lag/margin を無視し、`ChainStep.backDone` はそれを watch へ継承する）。
  **帰結**: `hready : ChainTickable` を `ChainOk`＋`WatchOk` 上に載せ替える道は閉じた。
  消すには `ChainOk` を `.copy`/`.back` で lag/margin を縛り、誕生義務を `.back` の場として
  持たせる再設計が必要。これは `hSP` の唯一の残り障害。
- **偽だった仮定（前夜まで）**: `periodLength` +1、`hbg`、`hfast`、`lookChain` 常時 2 手、`ReplaySpan`（反例 `aaaaabaaaab`）、`Trail`（fallback 後は右スタック非空 → `TrailF`）、`ReplayStageInv`/`FoundStage` の普遍形（到達可能 found に限定 → `ReplayBudgetR`）。
- found 時の半径 k ≤ 2n（`found_radius_le_two_period`）が replay 予算の鍵。`OffCompareFoundStage` は `GalilFoundStageInv` で閉じた。

### 3. `H_oracle2` の葉（`GalilOracleMC3.h_oracle_of_leaves''` 基準）

閉: `hex`, `hsearch`, `hsegmentM`（`segment_of_invLPC`+`hends_C`）, `hends`, **`hbudget`（`replayBudgetR_of_decodes'` を `decodesC` で — `CloseoutOracle8.hbudget_C`）**, **`hrs`（`restartShape_sharedC` — `CloseoutOracle8.hrs_C`）**, `hstr`（`Final4` で不要）。
**訂正（2026-09-19）**: `hended`/`hlastMatch` は**閉じていない**。producer（`GalilLeafReport.hended_C`/`hlastMatch_C`、`GalilOracleMC4.hlastMatch_C'`）は側入力 `hpres`（bare `SearchReady` が search quantum で保存される）を取るが、それは**偽**。`GalilLeafPres.searchReady_run_true_iff` が `SearchReady v' ↔ 1 ≤ value v.search.debt` を証明済みで、debt 0 で破れる（機械検査: `CloseoutPresRefute.hpres_fails_at_zero_debt`）。閉じるには `GalilLeafPres` が指定する `SearchReadyB := ReadyRem ∧ RunEntriesAll` への再切り出しが必要。
**`Decodes` はタダ**: `GalilFinalAssembly2.decodesC` が証明済み（`Decodes` は `P.centre`/`P.place` だけを縛り、`centreC`/`placeC` は `s.center` の具体関数）。`Closeout*` 全域の `hP : Decodes (PofC …)` 素通し仮説は全部不要。
**訂正（2026-09-19, n114）: 探索（DP）側は無条件で証明済み。**
`GalilDpCorrect.initial_correct`（fresh プリロードから `Result`）、
`GalilScaffoldSearchRun.dp_quanta_safe` / `calibrated_quanta_safe`
（run 相の探索状態から `SafeQuanta` ＋ `Result`）、
`GalilTickFair.readFun_code`（`decide` で証明、`safeQuanta_unique` の前提）、
`GalilMinimalPeriod.result_least`（`Result` → `Candidate` ＋ 最小性）は
すべて標準 3 公理のみで、既に `GalilScaffoldStagePrepare` / `GalilBranchInvariants2` /
`GalilScaffoldChainFallback` で消費されている。
`CloseoutPrepInputs3.PrepInputsG3` が `Result` を仮説として束ねているのは
**ステージ層とそこの間が繋がっていないだけ**で、found 経路の残りは新しい数学ではなく層の配線。

**訂正（2026-09-19, n181/n182）: `hpres` の後継 `ReadyFuel` は反証済み**
（`PalPeg/ReadyFuelRefute.not_readyFuel_v0`）。`.run` 入口の債務（= 2）が
`K = headRank`（入力長に比例）回のマッチを払えと要求していた。
**正しい乗り物は `GalilReplaySpan.ReadyClosure`**（`ready`/`seg`/`restart` の 3 場）で、
`CloseoutPreload11.readyClosure_S2` が `PostRun` ＋ `RestartS2` から出す。
消費者（`CloseoutReportCase`）が `ReadyFuel` から取り出しているのは `SearchReady` だけなので
置換は 1:1。`CloseoutContracts.StageEntryC` も `fuel` 場が偽なので切り直しが要る。

残: `hpres`→`ReadyClosure` 版への切り直し（上）; `hstage`（`ReplayStage` を `GalilReplaySpan` 内で持ち回り、進行中、mid-replay restart の `3·radius ≤ 5·last` が新義務）; `hshape`（`StartShape`）; `hlastMismatch` の最終文字分岐（`LastMismatchReport`）と `EntryRefreshed`; `hmismatch` ← `GalilLeafMismatch` の残差 `hdp`（DP pack、進行中）/`hfb`（fallback tick 数、進行中）/`hpos`（区間予算前提を pieces に追加、進行中）; `hfound`/`hfoundBg` ← 着地不変量に `Restarted`/`StageEntry` を追加（`GalilInvPlus3`、進行中）+ found tick からの経路構成（未着手、最大の残り）; `hfoundReplay`（replay 中 found の経路、未着手）。

### 3c. 2026-09-19 の追加（`M-periodOnly` とモデルの忠実性）

- **モデル欠陥 `M-periodOnly` を実装**: Scala `ScaffoldChain.start()` の `periodOnly = false` と `cycle.reset()` が Lean に無かった。`chainBorn (found) (x : ChainVM) := x.isIdle && found`（誕生条件は「その遷移で新しい chain が実際に始まること」）と `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）を入れ、`compareFound`/`backgroundS`/`background_found_step` の遷移先を包んだ。全体 build 緑。回帰テスト `CloseoutPeriodOnlyRegression.birth_resets`。
- 伝播を止めた補題: `not_shiftGuard_afterMismatchB`（誕生時の chain は `chainStart`＝`.copy`、`shiftGuardVM` は `.watch` を要求 → guard は立たない）と `refresh_afterBirth_iff`（`P.onLetter = onLetterVM raw`・`P.leftFirst = leftFirstVM` の下で `refresh` は `afterBirth` 不変）。
- 局所側: `LocalTick1` に `birthL`/`abs_birthL`/`inv_birthL`/`stepLocal_birthL`/`matchCtl_congr` と射影群、`bgState` に誕生元 chain を追加、`c₁` を 66 → 67。`tickL1_abs` は側条件 `hbirth` を取り、具体 `PofC` では定理（`CloseoutBirthFrame.hbirth_PofC`）。
- **`hsc`（`H_stageScan`）は反証**: `InvScan` の 11 場は `s.radius` に触れないのに `ReplayStage` は `Canonical radius` を要求。再切り出し `InvScanS := InvScan ∧ ReplayStage`、産出側の第 1 段は `CloseoutStageScan1`。
- **`hme` への合成**: `walkerInOrigin_of_run` の義務 `hcan` は `CPack.front : FrontPack` の `replayPos` + `frontier` と `consume_not_replaying_false` から出る（`CloseoutReplayCanRight`）。新規入力なし。
- `hee`/`het` の残差（scan 状態で `canRight`）は**偽の疑いが強い**。`Inv.input` は右ヘッドの内容を縛るが位置を縛らない。

### 3b. 2026-09-17 朝の追加
- `StartShape` は偽 → `StartShape'`（`GalilReplaySpan.startShape'_of_decodes`）。`hpres` は `ReadyFuel`（`GalilSegmentConstructB`/`GalilReadyFuelUses`）と `RunEntriesAtBegin`（replay、`''_fuel`）に置換。`hfb` 閉（`GalilLeafFb`）。`hdp` → `MismatchDp`+`StageBudgetAt`（`GalilLeafDp`）。`hpos` → 区間予算（`GalilOracleMC4`）。`TrailF` は `RadPack` の tick 保存 1 つ（`GalilTrailRad`）。局所 7/10 モード閉（`LocalWF`）。
- 次: `RadPack` tick 保存、`Fair` を使った scan/init/replayStart の `Realizes`、found 経路 3 葉、各版の集約（MC2/MC3/MC4/InvPlus3/ReadyFuel）。

### 4. 残りの課題（優先順）
1. `Fair` 一意性（`GalilTickFair`）→ 構成 witness/局所 step の `Fair` 監査 → `Realizes` の scan/init/replayStart。
2. found 経路の葉（`hfound`/`hfoundBg`/`hfoundReplay`）: `InvLPS` 上で `prep_segment_construct_of_found` → rounds/break 分岐 → `foundRouteMC_shift`/`foundRouteMC_noshift_dC`。
3. §3 の進行中項目の登録と `h_oracle_of_leaves'''` への集約。
4. `RadPack` で `H_trailF` を閉じる。局所側: `LocalWF`（fpp 量子、側条件）。
5. 局所台帳の `habs`/飢餓同値（`LocalSysConcrete.H_ready`, `H_feed_track`）。

### 5. 再開手順
```sh
cd lean-pal && . ~/.elan/env && lake build --quiet PalPeg > /tmp/b.log 2>&1; echo $?   # 全体（20 分）
cd lean-pal && lake env lean PalPeg/X.lean                                          # 単一ファイル
sed -i "/^import PalPeg.CloseoutFinalBranch$/a import PalPeg.X" PalPeg/Workbench.lean  # 未配線の新モジュール
# 正本の鎖に入るなら PalPeg/Canonical.lean に別名を置く。ルート PalPeg.lean は 4 本だけ
# （PalInPeg / Canonical / Workbench / Axioms）で、直接は足さない。
```
- サブエージェント規約: 定理 1 つ・ファイル:行番号・使う補題名を指定、新規ファイル 1 本、既存編集禁止（例外は明示）、sorry 禁止、`lake build` 禁止、`#print axioms`。中心部の設計は自分で書く。
- 詳細は `CLAUDE_RESUME.md` / `lean-pal/ASSEMBLY_PLAN.md` 先頭。

## 証明はコードである — lean-pal 編集の規律

2026-09-19 に `lean-pal/` は **1143 モジュール・331,884 行・定理 12,593 本**に達し、
「名前を思い出して grep する」運用が破綻した。同じ日に既存部品を 3 回取り落とし
（`CloseoutTerminalN.roundStepC_of_alignN` を「配線が必要」、`CloseoutMarksFree.marks_steps_free`
を「無い」、`CloseoutPackRun49`（`LPackM3`）を「中心台帳は `ChainPack` にしか無い」と書いた）、
そのうえ未検証の断定を重ねた。**証明が進まない直接の原因は難易度ではなく、
「どのモジュールにどの証明があるか」の地図が無いことだった。**

証明はコードである。プログラムを関数・モジュールに整理するのと全く同じ規律を適用する。

### 1. 断定の前に地図を作る

- **コードベース全体を俯瞰していない状態で「○○は無い」「○○が壁だ」と書かない。**
  部品の不在は grep 1 回では示せない。俯瞰は機械で取る（import グラフ、宣言の逆引き、
  主定理からの推移閉包）。
- 「前提が N 本」のような数は、**その定理の型を実際に見てから**書く。
  `#print axioms` は公理の推移依存だけを見るもので、前提の本数は見ない。
- Prop 引数の本数＝前提の本数ではない。`∀ w, H_x w` は 1 本に見えて族であり、
  instance や decidability は自動放電される。**数えるべきは「producer が無い前提」**。

### 2. 1 モジュール 1 責務・名前が中身を表す

- **定理名・ファイル名に番号を入れない。**「いつ書いたか」ではなく「何であるか」を書く。
  `final37` / `PackRun49` / `Oracle8` / `Preload41` のような名前は、番号を覚えていない限り
  意味から引けない。意味のある別名は `PalPeg/Canonical.lean` に置く（**カーネルが検査する
  索引**：名前が動けば build が壊れる。markdown の索引は黙って腐る）。
- 反証済みのものは `refuted_` を前置して、使ってはいけないことを名前で示す。
- **仮定名・変数名は「何を言っているか」を表す。位置で付けない。**
  コウタの指摘（2026-09-19）:「変数名とか仮定につける名前も大事。あとでみたときに
  直感的になんか変なことしてるなってわかるから」。**名前は臭い検出器である。**
  実例: 偽だった前提が `hav` / `hpack` という名前だったので過剰量化が見えなかった。
  `hconsumeAvailEverywhere` / `hchainPackAtAnyState` なら一目で分かった。
  - ✗ `hP` `hR` `hL` `h1` `hz` `hE` `hi` `key` `hm2`（位置・登場順で付けた名前）
  - ✓ `hpre`（`PreTrace`）`hradLedger` `hlagCan` `hipos`（`1 ≤ i`）`hradZero`
    `hentryCounters` `hile`（`i ≤ Tc`）`hpackM2` `hverRun` `hfront` `hshiftLocal`
  - 同じ名前を別の意味で使い回さない（`hpre` を `PreTrace` と `PreloadL'` の両方に
    使うと衝突する。`hpreTrace` / `hpreload` に分ける）。
  - **過剰量化した仮定には、その過剰量化が名前に出る名前を付ける**
    （`…Everywhere` / `…AtAnyState`）。そうすれば書いた瞬間に気づける。
  - **略すのは `h`（hypothesis）だけ。** 人間には長い識別子のコストがあるが AI には
    ほぼ無いので、多少長くても意味が分かる名前を選ぶ。略す場合は規則性を持たせる
    （コウタ 2026-09-19）。
  - **記号だけの接尾辞を新しく作らない。** 既存の `IPackM` / `IPackMG` / `IPackMG2` /
    `IPackMW` 系がその失敗例で、docstring から辿れるのは 2 つだけ:
    | 記号 | 意味 | 出典 |
    |---|---|---|
    | `G` | **G**uarded（shift 半分を mode guard で守った） | `CloseoutPackRun30:81` |
    | `2` | `LPackM2` を併せて運ぶ世代 | `CloseoutPackRun36:73` |
    | `W` | `shift` 場を**落とした**系統（偽の `WatchShiftG` を運んでいた場） | `CloseoutPackW:63` |
    | `I` / `M` | **出典なし**（誰も書いていない） | — |

    `PreTraceIMW` の実体は「各点で `LPackM` と `LPackM2` を持つ pre-trace」。
    `IMW` は「いつ書いたか」の痕跡であって「何であるか」を表していない。
    **新しく書くものは `LandingObligationsAlongTrace` のように、読んで分かる名前にする。**

### 3. コピペ証明を残さない

- 同じ証明を書き足して `_A` `_B` `_2` `_'` の変種を増やすのをやめる。
  変種が必要なら、共通部分を補題に切り出してから分岐させる。
- 既に 88 個の suffix 変種と 233 個の `*_tick` があり、47 本の `pal_in_peg_final*` がある。
  **これ以上増やす前に、既にあるものを探す。**

### 4. デッドコードの判定は主定理との関係でのみ行う

- **「誰も import していない」「名前が参照されていない」はデッドの証明にならない。**
  未登録・未参照のまま健全で有用な部品が実在した（`CloseoutPackRun49` は未登録のまま
  5 定理が健全、修理して 7 定理全部が通った）。
- 判定基準は **主定理 `RecognizedByTotalPEG PAL` との関係**。その義務・前提・残差に
  触れているなら、参照ゼロでも残す。関係が無いものだけを削除する。
- 削除は不可逆なので、削除前に「何がそこにあったか」を索引に記録する。

### 5. 反証を書くのは、証明を試して反証の形の障害に当たったときだけ

- まず証明を書こうとする。`REFUTED` と書けるのは **`False` を導く機械検査済みの定理が
  あるとき**だけ。定理が前提を取るなら `REFUTED（条件付き）` と書き、未構成の証人を名指す。
- 散文の論証・他ファイルのヘッダ・類推・**過去の自分の記述**は一次情報として扱わない。
- **ファイル自身の docstring も一次情報ではない**（2026-09-19, n116）。
  `CloseoutRealize1.lean` は冒頭で §1〜§6 を完了したかのように列挙していたが、
  実際の宣言は 2 つだけで §3〜§6 は存在しなかった（§6 は「latch を迂回する直接経路」と
  読める記述で、信じると `hC` の壁を回避できると誤解する）。
  **宣言の存在は `grep "^theorem"` で確認する。docstring の節番号を数えない。**

## 進捗ノートの扱い

- `CLAUDE_RESUME.md`（ルート）が Claude Code 向けの再開情報の最新。`PROGRESS.md` は古い記録を含む。どちらも新しいエントリが上に来る追記形式で、各エントリは「何を証明したか / build 結果 / 公理 / 未完の部分」を 1 段落で書く。
- lean-pal の節目を記録するときは `ASSEMBLY_PLAN.md` と `CLAUDE_RESUME.md` の両方の先頭に追記する。「全体 build 成功・標準公理のみ・無条件 PAL は未完」の 3 点を必ず明記する。
- `docs/palindromes-in-peg/HANDOFF.md` は Codex の構成ログ（新しい順）。

## その他

- ディスクが逼迫しがち（`make disksize` で確認）。`lean/.lake`、`lean-pal/.lake`、`scala/*/target` が大きい。
- `.claude/worktrees/` はサブエージェント用の worktree 置き場で git ignore 済み。
