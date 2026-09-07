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

**照合器（GS）**
- `Matching` — KMP 一歩・境界鎖・Galil の予測補題（仕事 ≤ 保証ゼロ出力数）
- `GSScan` — Galil–Seiferas 走査：安全シフト、健全性/完全性、ポテンシャル `Φ=(k+1)pos+q`
- `GSDecomp` — GS 分解 `GSCore/GSDecomp`、k 反復周期の補題、走査側帰結と `KSimple` への橋
- `GSRealTime` — GS 走査の実時間実行：レート k+1 で `online_answer_correct`、有界遅れ不変量
- `GSVerifier` — u 検証器を quota 2 で交互実行（オラクルなし `vAnswer_correct`）
- `StageMatcher` — GS 照合器が `MatchOracle` を満たす（`dyadic_gs_mem_PAL`、オンライン性）
- `GSDecompose2Work` — `decompose2` の仕事量：Σp_j ≤ C₁T を仮定すれば線形（仮定の真偽を検証中）

**中央フラグ**
- `Manacher` — Manacher の radius 走査の正しさ、接頭辞回文フラグ、仕事量 ≤ n
- `ManacherHeads` — Manacher をテープ上で走らせたときのヘッド総移動 ≤ 7|x|（telescoping）
- `MiddleJob` — 中央回文フラグ：区切り埋め込みで偶奇統一、4 分割ジョブの費用 ≤ 128h
- `BorderJob` — 中央フラグの GS 系境界列挙（縮小段、`palPrefixFlagsGS_spec`、仕事 ≤ 258|x|）

**スケジューリング・キュー**
- `RTQueue` — Hood–Melville 実時間キューと FIFO 仕様
- `Schedule` — 順序処理の締切（`finishTime_le`）と Galil の FIFO サービス不等式（Lindley）

**前処理（decompose, decompose2, L1）**
- `GSPreprocess` — 計算可能な GS 分解 `decompose`（Python と一致）、`decompose_spec : GSCore`
- `GSDecompose2` — 失敗位置へジャンプする strip 規則の `decompose2`：`decompose2_gsDecomp`（L1 無条件）
- `GSDecompL1` — 真の L1 境界 `gsDecomp_exists`（パスは p₂ 手前で停止）

**テープ化**
- `TapeLib` — 成果物のテープ上の zipper / stack / seq / counter ビューと 1 アクション補題
- `TextFeed` — 到着記号を FIFO で走査テープに供給、`feed_online` で `onlineRun` を再現
- `VerifierFeed` — 検証器の Txt2 も FIFO で供給（`.X .right` ごとの fill 版を続行中）
- `GSScanTapes` — GS 走査 1 歩を 3 テープ（P/Txt/Cnt）の動作列で実現、コスト ≤ (2k+2)ΔΦ+8
- `GSVerifierTapes` — u 検証器の 5 テープ化、走行費用 ≤ (2k+3)ΔΦ+18n（L1 不要で償却）
- `BorderJobTapes` — 境界列挙の 6 テープ化、テープ仕事 ≤ 4000|x|、`flags_on_tape`
- `MiddleTapes` — 中央ジョブのバッチをテープ上で実行（`batch_read_flag`、ラウンド組み立ては続行中）
- `PatternTapes` — 段のセットアップ（入力コピーからパターン/U/カウンタ群を構築、≤ 21h 動作）
- `Prologue` — 段開始前の準備動作のテープ化
- `RTQueueTapes` — Hood–Melville キューを 9 本のスタックテープで実現（snoc ≤ 20、tail ≤ 27 動作）
- `GSPreprocessTapes` — 前処理のテープ化（firstPeriod/extendReach/secondOuter；strip2 続行中）
- `StageMatcherTapes` — 段の照合フェーズ：固定 `roundBudget = 85 + U·B` 動作/ラウンド
- `InputCopy` — 入力コピー（フロンティア書き込み 1 動作/ラウンド、左読み）

**機械**
- `Speedup` — 1 記号あたり B マイクロステップの機械 → 厳密実時間 `Machine`（線形加速）
- `ProgramMachine` — 構造化機械 `StructuredMachine` → `MultiStepMachine` → `RecognizedBy`
- `Metered` — 固定 B 動作/ラウンドの de-amortization（`metered_phi`、境界で `metered_answer_correct`）
- `Main` — `pal_in_peg_of_structured`：PAL を SAccepts する構造化機械があれば `RecognizedByTotalPEG PAL`
- `EndToEnd` — 添字レベルの端到端：`endToEnd_mem_PAL`（仮定は `decompose` の L1 のみ）
- `EndToEnd2` — `decompose2` 版の端到端：仮定は `PassPeriodSum 8 C₁`（1 パスの周期和 ≤ C₁T）のみ

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
そのうえで、添字レベルの端到端定理 `EndToEnd2.endToEnd2_mem_PAL` は

```lean
PassPeriodSum 8 C₁
```

というただ一つの数学的仮定の下で成立している（`decompose2` 版の `endToEnd_mem_PAL` 系列で唯一未証明のもの）。
`PassPeriodSum b C₁` は「境界 `b` の 1 回の `stripLoop2` パスにおける各 run 開始点での最小 k 反復周期の総和が
`C₁·b` 以下である」という主張で、実験的には係数 `≤ 0.39·b` 程度に収まることが分かっている
（部分的な結果は `PassSum.lean` / `PassSum2.lean` にある）。この仮定を除けば、上の層構造（語の組合せ論から
機械まで）はすべて証明済みであり、テープ実現も各コンポーネント単位では完了している。

残っているエンジニアリング作業：

- `decompose2` の strip2 テープ化（進行中、`GSPreprocessTapes` / `VerifierFeed` / `MiddleTapes` 参照）
- 段のライフサイクル（生成・退役・切替のテープ上の組み立て、進行中）
- 全体機械の `StructuredMachine` 化と最終定理 `RealTimeTM.RecognizedBy PAL` の取得
  （`Main.pal_in_peg_of_structured` が構造化機械から総 PEG への糊）
