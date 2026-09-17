# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

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

**状態: 全体 build 成功・標準公理のみ・無条件 PAL は未完。最上位は 7 前提（`pal_in_peg_final26`, `CloseoutStageFinal`）。** 全モジュール sorry なし。新モジュールは `PalPeg.lean` の `import PalPeg.GalilSegmentConstruct` の直後に登録。

### 1. 最上位の定理と残りの仮定

| 定理 | ファイル | 仮定 |
|---|---|---|
| **`pal_in_peg_final26`** | **`CloseoutStageFinal`** | **7 前提**: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。`final25` の 8 前提から `hsc`（`H_stageScan`、反証済み）が消えた。理由: `CycleOutMC3` は両出口で `InvLPS` を返しており（`GalilInvPlus3:193, :212`）、boot も `Inv` 分岐に着地する（`invLPC_init:94`）。チェックポイント層を `InvLPS` 上で再走させれば `hstage_of_scanBranch` は呼ばれない（`CloseoutStageCheck`/`StageBoot`/`StageOracle`）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| **`pal_in_peg_final25`** | **`CloseoutPackRun51`** | **8 前提**: `hSP`（scan 状態の `ShiftPal`）, `hws`（`WatchShiftG`）, `hee`（`Extra7` 入口）, `het`（`Extra7` tick）, `hme`（`H_marksEntry'`）, `hsc`（`H_stageScan`、**反証済み**・再切り出し待ち）, `hor`（`CycleOracleMC3`）, `hC`（`H_realizeLIMG2'`）。`final24` の 11 前提のうち `hbs`/`hls`/`hsl` は木の中の定理で供給済み（`InvLPC` の chain は常に idle → `ShiftLocal*` は空虚）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| `pal_in_peg_final24` | `CloseoutPackRun46` | `hSP`（scan 状態の `ShiftPal`）, `WatchShiftG`, `Extra7`（`scanAvail` のみ）入口/tick, `H_extraEntry3/Tick3`, `H_marksEntry'`, `H_shiftLocalG`, `H_realizeLIMG'`, `H_shiftLocalC`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIM'`（最上位。found 葉は `foundExit_compare_final9`、readiness は `PostRunC`、核は `chooseVm_tapeActK`；詳細 `CLAUDE_RESUME.md` n74；残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`；**モデル欠陥: chain 誕生で `periodOnly` 未リセット（修正保留）**；readiness 帰納段 `postRunF_step` 成立；found 葉は `foundExit_compare_final14`（`FoundExitLPS`）、readiness 往復は `galilFrameS` 上で閉、core `shiftVm_tapeActKQ` K=28）；`BigResid6` は `bigResid6_of_lpackM2`（残 `ShiftPal`・`WatchShift`）；readiness は `PostRunF` 往復（Preload31）；readiness は `ScanRealized` 矛盾（n49）で `PostRunPh/F` へ再基底化中；rewind 角は `MarksEntry` 1 点；found 葉は `foundExit_compare_final19`；`ShiftLocal` は反証→`ShiftLocalG`（final16、`IPackMG` 再配線中）；`rewindMargin` は `CentreMargin` 1 葉に集約、`.double` 出口義務は Scala に合わせ再定式化要） |
| `pal_in_peg_final4` | `GalilFinalAssembly4` | `H_oracle2`（boot 側 oracle、`CycleOracleMC2C`）, `H_needLB'`, `H_realizeLB'` |
| `pal_in_peg_final2'_trailF` | `GalilTrailProof` | `H_oracle`, `H_trailF`, `H_base`, `H_realizeL'` |
| `pal_in_peg_of_local_core` | `LocalLatchRealize` | 局所 oracle（`LocalSysConcrete.localSys_oracles` の残差）+ `H_ledger`（`LocalLedgerShift` で放電済み、`habs`/飢餓同値が残り） |

- `H_oracle2` ← `GalilFinalAssembly4.h_oracle2_of_leaves` ← `GalilOracleMC3.h_oracle_of_leaves''`（`hquiet`/`houtReplay` 除去、`hfoundReplay` 追加）。葉の現状は §3。
- `H_needLB'` ← `H_trailF`（`GalilTrailProof`）← scan 側 `GalilTrailScan/Budget/Front/Sane/Order` + verifier 側 `GalilTrailChain/Assembly`。残りは scan 不変量 pack `RadPack`（`GalilTrailRad`、進行中）1 つに集約。
- `H_realizeLB'`: 局所実現。`LocalSysConcrete`（tick/到着/stutter/出力 oracle は無仮定）、`LocalRealizesScan`（rewind/choose 閉）、`LocalRealizesPhase`（shift/copy/home/markEnd 閉、fpp は局所 1 量子のみ残）。**scan/init/replayStart は抽象 tick の非決定性で閉じない**（§2）。

### 2. 設計上の重要事実（2026-09-17 深夜〜朝に判明）

- **`Fair` 完成（`GalilTickFair`）: `Tick ∧ Fair` は全状態で一意、残差なし。** 抽象 `Tick` 単体は一意でない（`GalilTickDet`）: (a) broken chain で `restart` と `scan_wait` stutter が競合（Scala は restart 優先）、(b) 探索量子は `ReadFun GalilDpCode.code` + `PrepareControl.Tick` 決定性を仮定すれば関数的、(c) chain は関数的、(e) `beginFallbackVM'`（着地場所）、`initVM`/`replayStartVM`（`periodOnly`, `walker` 自由）が非関数的。`tickFun`（`GalilTickFun`）は choice で 1 つ選ぶだけ。**方針**: モデルは編集せず（使用箇所 300 超）、Scala の優先順位と固定値を表す `Fair` を定義して `Tick ∧ Fair` の一意性を証明（`GalilTickFair`、進行中）。構成側の witness と局所 step が `Fair` を満たすことを別途確認。
- **偽だった葉（同じ型: 任意状態への量化）**: `hquiet`（`SearchQuiet` は「found に到達しない」と同値、`GalilLeafQuiet`）、`houtReplay`（`InvScan` に出力なし → `InvScanO := InvScan ∧ OutputRel`、`GalilLeafOutReplay`）、`hpres`（`SearchReady` は負債 1 単位分保存されない → `SearchReadyB := ReadyRem ∧ RunEntriesAll`、`GalilLeafPres`；`watchSegE_construct` は再証明要、`GalilSegmentConstructB` 進行中）、`hpos`（区間終端の右ヘッド位置、`GalilLeafPos`: 区間予算 `position r.right + count true ≤ 2m−2` から出す）。
- **偽だった仮定（前夜まで）**: `periodLength` +1、`hbg`、`hfast`、`WatchOk`、`lookChain` 常時 2 手、`ReplaySpan`（反例 `aaaaabaaaab`）、`Trail`（fallback 後は右スタック非空 → `TrailF`）、`ReplayStageInv`/`FoundStage` の普遍形（到達可能 found に限定 → `ReplayBudgetR`）。
- found 時の半径 k ≤ 2n（`found_radius_le_two_period`）が replay 予算の鍵。`OffCompareFoundStage` は `GalilFoundStageInv` で閉じた。

### 3. `H_oracle2` の葉（`GalilOracleMC3.h_oracle_of_leaves''` 基準）

閉: `hex`, `hsearch`, `hsegmentM`（`segment_of_invLPC`+`hends_C`）, `hends`, `hbudget`（`replayBudgetR_of_decodes'`）, `hrs`（`restartShape_sharedC`）, `hended`, `hlastMatch`（`hquiet` 依存を除去中）, `hstr`（`Final4` で不要）。
残: `hpres`→`SearchReadyB` 版区間構成（進行中）; `hstage`（`ReplayStage` を `GalilReplaySpan` 内で持ち回り、進行中、mid-replay restart の `3·radius ≤ 5·last` が新義務）; `hshape`（`StartShape`）; `hlastMismatch` の最終文字分岐（`LastMismatchReport`）と `EntryRefreshed`; `hmismatch` ← `GalilLeafMismatch` の残差 `hdp`（DP pack、進行中）/`hfb`（fallback tick 数、進行中）/`hpos`（区間予算前提を pieces に追加、進行中）; `hfound`/`hfoundBg` ← 着地不変量に `Restarted`/`StageEntry` を追加（`GalilInvPlus3`、進行中）+ found tick からの経路構成（未着手、最大の残り）; `hfoundReplay`（replay 中 found の経路、未着手）。

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
sed -i "/^import PalPeg.GalilSegmentConstruct$/a import PalPeg.X" PalPeg.lean        # 登録（build 中は登録しない）
```
- サブエージェント規約: 定理 1 つ・ファイル:行番号・使う補題名を指定、新規ファイル 1 本、既存編集禁止（例外は明示）、sorry 禁止、`lake build` 禁止、`#print axioms`。中心部の設計は自分で書く。
- 詳細は `CLAUDE_RESUME.md` / `lean-pal/ASSEMBLY_PLAN.md` 先頭。

## 進捗ノートの扱い

- `CLAUDE_RESUME.md`（ルート）が Claude Code 向けの再開情報の最新。`PROGRESS.md` は古い記録を含む。どちらも新しいエントリが上に来る追記形式で、各エントリは「何を証明したか / build 結果 / 公理 / 未完の部分」を 1 段落で書く。
- lean-pal の節目を記録するときは `ASSEMBLY_PLAN.md` と `CLAUDE_RESUME.md` の両方の先頭に追記する。「全体 build 成功・標準公理のみ・無条件 PAL は未完」の 3 点を必ず明記する。
- `docs/palindromes-in-peg/HANDOFF.md` は Codex の構成ログ（新しい順）。

## その他

- ディスクが逼迫しがち（`make disksize` で確認）。`lean/.lake`、`lean-pal/.lake`、`scala/*/target` が大きい。
- `.claude/worktrees/` はサブエージェント用の worktree 置き場で git ignore 済み。
