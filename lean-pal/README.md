# lean-pal — `PAL ∈ PEG` の条件付き Lean 4 証明（Kim–Park 成果物経由）

回文言語 `PAL = { w ∈ {0,1}* | wᴿ = w }` が PEG 言語であることを、
**「`PAL` を認識する厳密実時間多テープ TM が存在する」という仮定のもとで** Lean 4 で証明する。
併せて Loff–Moreira–Reis (2020) Conjecture 7（偶数長回文 `{ w wᴿ }` は PEG を持たない）を
同じ仮定のもとで反駁する。

背景と鎖の全体は [`../docs/palindromes-in-peg/FORMALIZATION_SURVEY.md`](../docs/palindromes-in-peg/FORMALIZATION_SURVEY.md)
（特に §1, §3, §4）を参照。

## 何を証明し、何を仮定しているか

### 仮定（Lean では証明していない）

ただ一つ、`PalPeg.pal_recognizedByTotalPEG` などの前提に現れる

```lean
PegSeparation.RealTimeTM.RecognizedBy PalPeg.PAL
```

すなわち **Kim–Park 成果物の `RealTimeTM.Machine` の意味で `PAL` を認識する機械が存在すること**。
この機械は決定的・停止なし・**1 記号につきちょうど 1 遷移**・各遷移で**各テープがちょうど 1 回書き
1 回動く**（`Common/Compiler/RealTimeTM/Model.lean`）。受理は入力を全部読んだ直後の状態だけで決まる。

紙の上でこの仮定を与えるのは Slisenko (1973) / Galil (1978) の実時間回文判定機械だが、

1. Galil の機械を `RealTimeTM.Machine (Fin 2) t s k` として書き下し `∀ w, M.Accepts w ↔ w ∈ PAL` を証明すること、
2. 文献の「定数遅延の実時間」から成果物の「厳密実時間（1 記号 1 遷移、1 テープ 1 書き込み 1 移動）」への正規化
   （Hartmanis–Stearns 流の tape compression）

の**どちらもこのパッケージには含まれていない**（見積もりは調査 §6：8–15k 行）。
したがってここで示したのは「Galil の機械が成果物の厳密実時間モデルで書ける、と認めるなら `PAL ∈ PEG`」であり、
無条件の `PAL ∈ PEG` ではない。

### ファイル構成（`PalPeg/*.lean`、層ごと）

基礎（`Basic`／`Existence`／`EvenLength`／`Axioms`）は上の 2 節に既出のとおり。残りは以下の層に分かれる。

**語の組合せ論**
- `Words` — 回文と周期の組合せ論（拡張則・境界・Fine–Wilf・group 補題）
- `Groups` — group 圧縮した鎖（2 回の記号参照/群）が `chain` を展開する
- `GroupsLog` — group 併合・正準性・境界縮小 `3ℓ' < 2ℓ`
- `GroupsLogBound` — 群数 ≤ 2·log₂|v|+4 を無条件化

**仕様（鎖・dyadic stage・組み立て）**
- `Chain` — 接尾辞回文鎖のオンライン参照算法と `w ∈ PAL ↔ |w| ∈ chain w`
- `Structure` — レプリカ・境界・予測補題・禁止帯（`lsp_shift_bound`）と反例
- `Stages` — dyadic stage 分解 `Pal(n) ⇔ match_W ∧ middle_W`、段の被覆と同時稼働 ≤ 2
- `Assembly` — 段の組み立て：照合/中央オラクル ⇒ `answer_correct`、`answer_length_iff_mem_PAL`
- `OnlineMachine` — 全体機械の添字モデル（2 段）、`output_correctH`、ラウンド費用 ≤ 3(3(k+1)+Cm+Cp)
- `MiddleBorder` — 境界列挙版の `MiddleImpl`、`MiddleImplSpecH` を Cm=27901 で満たす
- `PrepDecompose` — `decompose` を (S/2,S] に均す `PrepImpl`、`PrepImplSpecH`

**GS 分解と前処理**
- `Matching` — KMP 一歩・境界鎖・Galil の予測補題（仕事 ≤ 保証ゼロ出力数）
- `GSScan` — Galil–Seiferas 走査：安全シフト、健全性/完全性、ポテンシャル `Φ=(k+1)pos+q`
- `GSDecomp` — GS 分解 `GSCore/GSDecomp`、k 反復周期の補題、走査側帰結と `KSimple` への橋
- `GSPreprocess` — 計算可能な GS 分解 `decompose`（Python と一致）、`decompose_spec : GSCore`
- `GSDecompose2` — 失敗位置へジャンプする strip 規則の `decompose2`：`decompose2_gsDecomp`（L1 無条件）
- `GSDecompL1` — 真の L1 境界 `gsDecomp_exists`（パスは p₂ 手前で停止）
- `GSDecompose2Work` — `decompose2` の大域仕事量：定数 `C=(4k+2)C₁+17k+50`, `D=2k+5` の無条件線形上界

**実時間照合**
- `GSRealTime` — GS 走査の実時間実行：レート k+1 で `online_answer_correct`、有界遅れ不変量
- `GSVerifier` — u 検証器を quota 2 で交互実行（オラクルなし `vAnswer_correct`）
- `GSVerifierFused` — 検証器のずらし枝で U/Txt2 の巻き戻しを融合（`uxWalk`、コスト 14p₁+9q+12+2·checked）
- `StageMatcher` — GS 照合器が `MatchOracle` を満たす（`dyadic_gs_mem_PAL`、オンライン性）

**中央フラグ**
- `Manacher` — Manacher の radius 走査の正しさ、接頭辞回文フラグ、仕事量 ≤ n
- `ManacherHeads` — Manacher をテープ上で走らせたときのヘッド総移動 ≤ 7|x|（telescoping）
- `MiddleJob` — 中央回文フラグ：区切り埋め込みで偶奇統一、4 分割ジョブの費用 ≤ 128h
- `BorderJob` — 中央フラグの GS 系境界列挙（縮小段、`palPrefixFlagsGS_spec`、仕事 ≤ 258|x|）

**スケジューリング・キュー**
- `RTQueue` — Hood–Melville 実時間キューと FIFO 仕様
- `Schedule` — 順序処理の締切（`finishTime_le`）と Galil の FIFO サービス不等式（Lindley）

**テープ化**
- `TapeLib` — 成果物のテープ上の zipper / stack / seq / counter ビューと 1 アクション補題
- `TextFeed` — 到着記号を FIFO で走査テープに供給、`feed_online` で `onlineRun` を再現
- `TextFeedProg` — `TextFeed` のラウンド `feedRound'` を検証（`fill'`/`startT'` 帰納、60 ステップ）
- `TextFeedProg2` — オンライン相の `Prog` 化（`fillIf'`/`Enabled` が読みだけで判定できる版、`feed_online_prog`）
- `VerifierFeed` — 検証器の Txt2 も FIFO で供給（`.X .right` ごとの fill 版、二重 FIFO）
- `VerifierFeedX` — `vprogramX`（ずらし枝を `GSVerifierFused` で融合した版）の供給つき一歩 `vscanOneX`
- `GSScanTapes` — GS 走査 1 歩を 3 テープ（P/Txt/Cnt）の動作列で実現、コスト ≤ (2k+2)ΔΦ+8
- `GSVerifierTapes` — u 検証器の 5 テープ化、走行費用 ≤ (2k+3)ΔΦ+18n（L1 不要で償却）
- `BorderJobTapes` — 境界列挙の 6 テープ化、テープ仕事 ≤ 4000|x|、`flags_on_tape`
- `MiddleTapes` — 中央ジョブのバッチをテープ上で実行（`batch_read_flag`、ラウンド組み立ては続行中）
- `MiddleClear` — 段の終わりに `P`/`U`/`Cnt` テープを新品（空スタック）へ戻す消去動作列と `Near` 不変量
- `PatternTapes` — 段のセットアップ（入力コピーからパターン/U/カウンタ群を構築、≤ 21h 動作）
- `PatternTapesPair` — 凍結入力ペアからの段セットアップ（13 テープ版）
- `Prologue` — 段開始前の準備動作のテープ化
- `RTQueueTapes` — Hood–Melville キューを 9 本のスタックテープで実現（snoc ≤ 20、tail ≤ 27 動作）
- `GSPreprocessTapes` — 前処理のテープ化（firstPeriod/extendReach/secondOuter；strip2 続行中）
- `StageMatcherTapes` — 段の照合フェーズ：固定 `roundBudget = 85 + U·B` 動作/ラウンド
- `StageMatcherTapesX` — `XStep` インタフェース版の照合フェーズ（`fedStep`、償却コスト `fcostX`）
- `StageTapes` — 段の全ライフサイクルをテープ上で組み立て（`stage_tapes_spec`）
- `StageTapesX` — `StageTapes`/`StageMatcherTapes` の `X` 版（`vprogramX` 経路）への配線
- `InputCopy` — 入力コピー（フロンティア書き込み 1 動作/ラウンド、左読み）
- `InputCopySentinel` — 番兵初期化された入力コピー（`PrepPreL` 形の `SeqView`、左端で歩きが止まる）
- `ClearAny` — 任意のテープを `≤ 3·width+3` 動作で消去する汎用ガジェット
- `FullMachineTapes` — 全体機械のスロット回転（`Restart` スケジュール）、`full_answer_mem_PAL`

**有限制御 ProgLang 移植**
- `ProgLang` — 有限制御プログラム言語 `Prog`（動作/条件を有限添字で表現）と `StructuredMachine` への橋
- `ProgLangLib` — `Prog` の共通補題（`ite`/`skip`/`seq` の純制御展開を吸収する動作列一致補題）
- `ProgLangPersist` — 永続制御機械（到達スタックの有限性、`grind` 補題）
- `ProgLangSum` — 解釈の移送・合成（テープ添字の単射に沿った射影で `exec_lift` を系として再導出）
- `GSScanProg` — GS 走査を `ProgLang` に移植（動作列が `program'` と逐語一致）
- `GSPreprocessProg` — 前処理カウンタ層の 9 テープ有限制御（`DLOOP` ガジェット、21 ループの合成）
- `GSPreprocessProg2` — 前処理の有限制御・第 2 部（番兵駆動 `bottomProg`、一般化駆動ループ `dLoopS_exec`、カウンタ比較ガジェット `CMPLT`）
- `GSVerifierProg` — 検証器の比較枝を `ProgLang` へ（8→10 テープ持ち上げ、ずらし枝は融合待ち）
- `GSVerifierProgX` — 検証器 1 ラウンド全体の有限制御 `vprogX`（`vprogramX` と逐語一致）
- `BorderJobProg` — 境界列挙を完全有限制御化（`periodActs`/`resetShift`/`shiftProg`、`ovStepProg_exec_full`）
- `MiddleProg` — 中央ジョブのバッチをテープ駆動の掃引で `Prog` 化（`leftN_clamp_eq`、`ovRunProg` = `whileProg`）
- `PatternProg` — 段セットアップの入力非依存コピーを `Prog` 化（`setupProgL_spec`）
- `PatternPairProg` — 13 テープ版セットアップの有限制御化（`settleProgG`/`kLoopProg`）
- `RTQueueProg` — Hood–Melville キューの `ProgLang` 版（snoc/tail 逐語一致、≤26/≤31 動作）
- `StageMatcherProg` — 段の照合フェーズの有限制御化（`matchProg`、`stageX_answer_stageMatchH`）

**インタフェース具体化**
- `DecompInstance` — 分解器を作業テープ `S1..S9` に埋め込む（`decompInstanceB`、`decompOnTapes_isEmpty` で旧インタフェースの不備を指摘）
- `DecompUniform` — 一様版の中央ジョブ分解器の部品（`prologueU`/`splitLoop`/`copyPLoop`/`ctrMoveLoop`）
- `PrepInstance` — `decProg` から具体的な `PrepOnTapes` を構成（`Cp=72522·C₁+397192`, `Dp=45252`）
- `PrepInstances` — `stage_tapes_spec'` が要求する `res`/`GSCore` パッケージ（`prep_res_eq5` 等、無条件）
- `StageBirth` — 段が生まれる時点のテープと `hinit` の護り方（`initOf_hinit`、旧インタフェースの穴の指摘）
- `StageIfaceInstance` — `StageIface` を `stage_tapes_spec'` + `prepInstance` から構成（`full_answer_mem_PAL_of`）

**機械**
- `Speedup` — 1 記号あたり B マイクロステップの機械 → 厳密実時間 `Machine`（線形加速）
- `ProgramMachine` — 構造化機械 `StructuredMachine` → `MultiStepMachine` → `RecognizedBy`
- `Metered` — 固定 B 動作/ラウンドの de-amortization（`metered_phi`、境界で `metered_answer_correct`）
- `Main` — `pal_in_peg_of_structured`：PAL を SAccepts する構造化機械があれば `RecognizedByTotalPEG PAL`
- `EndToEnd` — 添字レベルの端到端：`endToEnd_mem_PAL`（仮定は `decompose` の L1 のみ）
- `EndToEnd2` — `decompose2` 版の端到端：仮定は `PassPeriodSum 8 C₁`（1 パスの周期和 ≤ C₁T）のみ

**数学的仮定 `PassSum*`（`Consumption` の証明を目指す一連のファイル）**
- `PassSum` — 1 パスあたりのステップ二分律（`pⱼ₊₁ < pⱼ` か否か）、周期和上界はまだ開いている
- `PassSum2` — `(j,j+2)` の降下補題（真の孫か親を大きく飛び越す UP かの二択）
- `PassSum3` — 同一周期の共終性・兄弟成長補題（`same_period_nested`、`crossing_siblings_overlap_lt`）
- `PassSum4` — 子の成長比 `(k-2)/(k-1)` の下界
- `PassSum5` — `PassPeriodSum` を UP ジャンプ周期の上界へ還元（DOWN 側は決着済み）
- `PassSum6` — UP 本数の還元（`PrepInstances` の `res`/`GSCore` パッケージも同時に整備）
- `PassSum7` — スケール不変な形 `Σp ≤ 2·max p` への還元と、二分律だけでは不十分であることの反例
- `PassSum8` — 兄弟成長比 `γ≥14/5` から木の漸化式を閉じ `PassPeriodSum 8 2` を得る
- `PassSum9` — 走査終端不変量 (E)、`C(c)<p_c` の DOWN 側証明と UP 側の部分結果（`region_prefix_period` 等）
- `PassSum10` — `lastChildBound`/`RootGrowth` の無条件証明と最終組み立て `passPeriodSum_eight_of_consumption`
- `PassSumRelabel` — `stripLoop2Periods` の単射リラベリング不変性、2 記号版 `PassPeriodSum` への一般化

証明の鎖（`pal_in_peg_of_realTime`）：

```
G.Recognizes w
  ↔ (RealTimeTM.toSCA M).Accepts wᴿ     -- SCAToPEG.loffBackward（LMR Thm 16 十分方向）+ wᴿᴿ = w
  ↔ M.Accepts wᴿ                        -- RealTimeTM.toSCA_accepts_iff（厳密実時間 TM → SCA）
  ↔ wᴿ ∈ PAL                            -- 仮定 hM
  ↔ w ∈ PAL                             -- PAL_reverse_mem
```

Conjecture 7 側は成果物の閉包性 `Closure.recognizedByTotalPEG_inter`（共通部分）と
`Closure.recognizedByTotalPEG_of_isRegular`（正則 ⊆ PEG）に、`EvenLength` の正則性を渡すだけ。

### 公理 guard

`PalPeg/Axioms.lean` が主定理ごとに `#print axioms` を `#guard_msgs` で固定している。
現れる公理は Lean / Mathlib の標準 3 公理 `propext`, `Classical.choice`, `Quot.sound` だけ
（`PAL_reverse_mem` は `propext` のみ）。どこかに `sorry` が入れば `sorryAx` が現れて
`lake build` が失敗する。

```
'PalPeg.PAL_reverse_mem' depends on axioms: [propext]
'PalPeg.pal_in_peg_of_realTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.pal_recognizedByTotalPEG' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenPal_ww_reverse_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 依存

- Lean `leanprover/lean4:v4.31.0`（`lean-toolchain`）。この repo の `../lean`（v4.32.0、Mathlib 非依存）とは
  別パッケージ。成果物の証明は pin された Mathlib で検査されたものなので動かさない。
- Mathlib `v4.31.0`（`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）。
- Kim–Park, *Separating Parsing Expression Grammars using Cell-Probe Lower Bounds: Lean Artifact* v0.1.0
  — GitHub `kimjg1119/peg-separation-artifact` commit `c364edb`（Zenodo doi:10.5281/zenodo.22099762）。
  `lakefile.toml` の `[[require]] name = "PegSeparation"` で git から取得する。
  使う定理は `RealTimeTM.toSCA_accepts_iff`（`Common/Compiler/RealTimeTM/Correctness.lean`）、
  `SCAToPEG.loffBackward`（`Common/Compiler/SCAToPEG/Final.lean`）、
  `Closure.recognizedByTotalPEG_inter`（`Closure/BooleanClosure.lean`）、
  `Closure.recognizedByTotalPEG_of_isRegular`（`Closure/RegularToPEG.lean`）。
  いずれも成果物側で標準 3 公理のみ（`axioms/closure.txt`）。

## ビルド

```sh
cd lean-pal
lake exe cache get      # Mathlib の olean を取得（初回は数分〜十数分）
lake build
```

または repo ルートで `make lean-pal`。Mathlib のダウンロードが要るので `make verify` には含めていない。
`elan` が入っていれば `v4.31.0` は自動で取得される。

参考：Mathlib キャッシュ取得済みの状態で、成果物側の必要モジュール 25 個（`Common/*`、`SCAToPEG/*`、
`Closure/{BooleanClosure,RegularToPEG}`、`External/PartialTotalization/TotalityHelpers`）と
`PalPeg` 5 モジュールの `lake build` は WSL2 上で約 2 分 30 秒。
成果物側の linter 警告（`unusedFintypeInType` 等 93 行）は出るがエラーはない。

エージェントがファイルを編集している最中は `lake build` が一時的に失敗することがある
（依存モジュールの整合が取れていない中間状態）。編集が落ち着いてから再度ビルドし直すこと。

## 現在の到達点

`PalPeg/*.lean` に列挙した全モジュールは `sorry` なし・標準 3 公理のみ（`Axioms.lean` の guard 参照）。

**唯一証明されていない数学的主張は `Consumption`**（`stripLoop2` 再帰における `C(c) < p_c`、
`PassSum10.passPeriodSum_eight_of_consumption` の前提）である。これを仮定すれば
`PassPeriodSum 8 2` が無条件に得られ、添字レベルの端到端定理 `EndToEnd2.endToEnd2_mem_PAL` まで
`decompose2` 版の鎖が閉じる。`PassSum9` の要約にある通り、`Consumption` の下位ケースのうち

- DOWN 側（走査終端不変量 (E) からの帰結）
- UP 側の一部（`region_prefix_period` 等の周期伝播の帰結）

はすでに証明済みで、残る場合分けが未決着のまま開いている。この仮定を除けば、上の層構造
（語の組合せ論から機械まで）はすべて証明済みである。

有限制御（`ProgLang`）への移植は、走査器・キュー・検証器・境界列挙・段のセットアップ・
テキスト供給・永続制御機械について完了している
（`GSScanProg` / `RTQueueProg` / `GSVerifierProg` / `GSVerifierProgX` / `BorderJobProg` /
`PatternProg` / `PatternPairProg` / `TextFeedProg` / `TextFeedProg2` / `ProgLangPersist`）。
残っているエンジニアリング作業：

- 前処理の分岐層の有限制御化（`GSPreprocessProg2` で継続中）
- 中央ジョブのバッチとテープの縫い目（`MiddleProg` / `MiddleTapes` / `MiddleClear` の統合、継続中）
- 段のライフサイクル全体の組み立て（`StageTapes` / `StageTapesX` / `StageBirth` / `StageIfaceInstance`、継続中）
- 全体機械のラウンド組み立て（`FullMachineTapes` のスロット回転を `StructuredMachine` 化まで通す）
- 上記に加え `Consumption` を証明した上での最終定理 `RealTimeTM.RecognizedBy PAL` の取得
  （`Main.pal_in_peg_of_structured` が構造化機械から総 PEG への糊）
