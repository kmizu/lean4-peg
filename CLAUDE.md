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

**進捗の計器は `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL` の公理リスト。**
目標は閉じた項として存在し、足りない義務は `axiom` で明示されている。
`PalPeg/Axioms.lean` の `#guard_msgs in #print axioms` がラチェットで、
1 個外すと guard が壊れて更新を強制される。**標準 3 公理だけになったら §10.5 達成。**
いまは 10 個の原子的義務が残っている（経路は `PalPeg/PalInPegUnconditional.lean` の
docstring に表で記録）。

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
- **`Fair` 完成（`GalilTickFair`）: `Tick ∧ Fair` は全状態で一意、残差なし。** 抽象 `Tick` 単体は一意でない（`GalilTickDet`）: (a) broken chain で `restart` と `scan_wait` stutter が競合（Scala は restart 優先）、(b) 探索量子は `ReadFun GalilDpCode.code` + `PrepareControl.Tick` 決定性を仮定すれば関数的、(c) chain は関数的、(e) `beginFallbackVM'`（着地場所）、`initVM`/`replayStartVM`（`periodOnly`, `walker` 自由）が非関数的。`tickFun`（`GalilTickFun`）は choice で 1 つ選ぶだけ。**方針**: モデルは編集せず（使用箇所 300 超）、Scala の優先順位と固定値を表す `Fair` を定義して `Tick ∧ Fair` の一意性を証明（`GalilTickFair`、進行中）。構成側の witness と局所 step が `Fair` を満たすことを別途確認。
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

## 進捗ノートの扱い

- `CLAUDE_RESUME.md`（ルート）が Claude Code 向けの再開情報の最新。`PROGRESS.md` は古い記録を含む。どちらも新しいエントリが上に来る追記形式で、各エントリは「何を証明したか / build 結果 / 公理 / 未完の部分」を 1 段落で書く。
- lean-pal の節目を記録するときは `ASSEMBLY_PLAN.md` と `CLAUDE_RESUME.md` の両方の先頭に追記する。「全体 build 成功・標準公理のみ・無条件 PAL は未完」の 3 点を必ず明記する。
- `docs/palindromes-in-peg/HANDOFF.md` は Codex の構成ログ（新しい順）。

## その他

- ディスクが逼迫しがち（`make disksize` で確認）。`lean/.lake`、`lean-pal/.lake`、`scala/*/target` が大きい。
- `.claude/worktrees/` はサブエージェント用の worktree 置き場で git ignore 済み。
