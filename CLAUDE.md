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

## lean-pal 無条件 PAL ∈ PEG の進捗（2026-09-17 時点・作業停止中）

**状態: 全体 build 成功・標準公理のみ・無条件 PAL は未完。** 全モジュール sorry なし。新モジュールは `PalPeg.lean` の `import PalPeg.GalilSegmentConstruct` の直後に登録済み。

### 1. 最上位の定理と残りの仮定

| 定理 | ファイル | 仮定 |
|---|---|---|
| `pal_in_peg_final3` | `GalilFinalAssembly3` | `H_oracle`, `H_needLB'`, `H_realizeLB'`（`H_base` は `PreTraceB` で除去済み） |
| `pal_in_peg_final2'_trail` | `GalilLookRefined` | `H_oracle`, `H_trail`, `H_base`, `H_realizeL'`（lookahead を遅れ量依存に修正した版） |
| `pal_in_peg_of_local_latch` | `LocalTrackingLatch` | 局所機械の oracle 4 系統 + `H_ledger` |

チェーン: `pal_in_peg_final*` ← `pal_in_peg_of_latch'`（ラッチ意味論）← 抑制走行 τ=2^18 ← 台帳 `ledger_throttledL_2p18` ← `checkpoints_cost` ← `cycleOracleMC_of_pieces` の葉。

### 2. 層ごとの到達点（証明済み）

- **台帳（実時間）**: Lindley 再帰、`Cw`（最左 live 中心）、定数 2·c2 ≤ 2^18。`GalilLindley`/`GalilLedger*`/`GalilThrottledRun*`。
- **停止性の測度**: 中心不変のサイクルは辞書式測度 `mu`（中心, 右ヘッド）で処理（`GalilLexMeasure.checkpoints_cost'`）。
- **入力消費**: `GalilLookRefined` で `lookChain'`（watch 正 lag=2 手、lag 0=1 手、back=1、copy=0）。`needL'` 上界は `Trail` 不変量に還元（`needL'_le_of_trail`）。旧定義は偽（`GalilNeedBound.not_needLB_of_caughtUp`）。
- **長さ下限 hfloor**: `GalilChainCoupling` で `hbudget` を無仮定で証明（`hbudget_of_invLP`）。`hcopy` は boot からの走行で出る（`copyPack_*`, `hfloor_of_reach`）。
- **shift 無し break**: `GalilNoShiftStage.foundRouteMC_noshift'` で `hstage/hcanon/hlast/hlag` を除去。place 4h の角は回文性で排除。
- **replay**: `GalilReplaySpan.replay_after_fallback_general''`（静穏／chain 生存／break→restart の 3 分岐）。`ReplaySpan` は `ReplayBudget` + `RestartShape`（具体機械で証明済み）に置換。
- **局所実現**: `LocalTrackingLatch`（`started` ビットで空語を分離、`run_on_time_shift`, `reported_of_shift`）。TickL1–3, LocalChain, LocalAlloc, LocalSchedule, LocalStepRealize。
- **完全性**: MInv、最左 live 中心の保存（match/fallback/shift/replay）、半径上界 `found_radius_le_all_stages`。

### 3. モデル上の発見（偽だった仮定と対処）

- `periodLength` の +1 → 除去（Scala 準拠）。
- `hbg`（背景 tick で chain 起動しない）偽 / found during replay あり / prep で mismatch → fallback 出口を追加。
- `WatchOk`+`hgood` 矛盾（`GalilReplayGeneral` は空虚）→ `SpanCore` 系に作り直し。
- `hfast` 偽（fallback/shift 中は scan 停止）→ ラッチ意味論へ。τ=2^17 不足 → 2^18。
- `lookChain` 常に 2 手は偽 → 遅れ量依存に。
- `ReplaySpan` 偽（反例 `aaaaabaaaab`、`cx_span` を decide で証明、Python 参照機でも確認）。
- `periodOnly` は VM 上で false に戻らない。`2h ≤ radius` は偽で `2h ≤ radius + cycle (+ remaining)` が正。
- Lean の `Internal` watch には break 構成子がない（正 lag で不一致だと後続なし）。Scala は break して restart で AssertionError。`ReplayBudget` 条項 3 で回避中。

### 4. 残りの課題（優先順）

1. **`ReplayBudget` の条項 2・3**（`R+2 ≤ j`, `2n+3+k ≤ (j−R−2)(delay−1)`、実質 `k ≤ 4n−1`）。現状の半径上界 `4090h−2052` では弱い。条項 1 は found→`Candidate` の接続のみ残る。Opus。
2. **`H_trail`**: トレース帰納で R の単調性・右スタック空、L/C の frontier 形、verifier の追従（`pos v + lag = pos R`）。verifier 右スタック空の前提が最弱点。Opus。
3. **`hcopy` の接続**: `InvLP`/`CycleOutL` に `CopyPack` を足すか boot 走行を持ち回る。Sonnet 可。
4. **`hcenR` の InvScan 分岐**: `InvScan` に中心ヘッド表現を足す。Sonnet 可。
5. **`foundRouteMC_noshift'` の新仮定**（`hwatch2/hes0` は `prep_segment_construct`、`hpal1/hpal2` は `candidate_palAt`）と右ヘッド ≤ 2m−1。Sonnet 可。
6. **`H_oracle`**: `cycleOracleMC_of_pieces` の残りの葉を上記で放電。Opus。
7. **局所実現の oracle 4 系統**（tick 模倣＋ラッチ、stutter、到着符号化、1τ ずらした台帳を `stAbs` について）。旧 `O_step_throttledG` は非シフト・`stTG` 用で流用不可。Opus。

### 5. 再開手順

```sh
cd lean-pal && . ~/.elan/env && lake build --quiet PalPeg        # 全体（長い）
cd lean-pal && lake env lean PalPeg/X.lean                        # 単一ファイル確認（サブエージェントはこれのみ）
sed -i "/^import PalPeg.GalilSegmentConstruct$/a import PalPeg.X" PalPeg.lean   # 登録
```

- サブエージェント規約: 新規ファイル 1 本、既存ファイル編集禁止、sorry 禁止、`lake build` 禁止、末尾に `#print axioms`。登録と全体 build は親が行う。簡単な作業は Sonnet、設計は Opus。
- 詳細な経緯は `CLAUDE_RESUME.md` と `lean-pal/ASSEMBLY_PLAN.md` の先頭エントリ。

## 進捗ノートの扱い

- `CLAUDE_RESUME.md`（ルート）が Claude Code 向けの再開情報の最新。`PROGRESS.md` は古い記録を含む。どちらも新しいエントリが上に来る追記形式で、各エントリは「何を証明したか / build 結果 / 公理 / 未完の部分」を 1 段落で書く。
- lean-pal の節目を記録するときは `ASSEMBLY_PLAN.md` と `CLAUDE_RESUME.md` の両方の先頭に追記する。「全体 build 成功・標準公理のみ・無条件 PAL は未完」の 3 点を必ず明記する。
- `docs/palindromes-in-peg/HANDOFF.md` は Codex の構成ログ（新しい順）。

## その他

- ディスクが逼迫しがち（`make disksize` で確認）。`lean/.lake`、`lean-pal/.lake`、`scala/*/target` が大きい。
- `.claude/worktrees/` はサブエージェント用の worktree 置き場で git ignore 済み。
