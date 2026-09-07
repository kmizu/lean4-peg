# Fable 5 引継ぎ — PAL 判定機・SCA・PEG の Lean 4 形式化

更新: 2026-09-07 17:50 JST。これは今回の引継ぎメモ。
過去の構成ログ `docs/palindromes-in-peg/PROGRESS.md` は別ファイルとして保持している。

## 1. 最新の依頼と停止位置

ユーザーの目標:

> 次に判定機やSCA, PEGの変換をLean4で書き下して正しさを証明してほしい。なるべくトークン使わずに

その後「いったんfable 5に引き継ぐからこれまでの経緯をPROGRESS.mdとして書き出して」と指示されたため、実装を止めてこのファイルを作成した。
**新しい具体的判定機のLean実装にはまだ着手していない。** モデル・既存証明・キャッシュの所在を確認したところである。今回の新目標について開始したビルドやバックグラウンド処理はない。

目標は既存の条件付き定理の前提を実際の機械と証明で埋め、判定機→SCA→PEGの正しさまで接続すること。単なるリスト反転比較の正しさや有限長テストで、この目標を達成したことにしない。

## 2. 現在のリポジトリ

- 作業場所: `/home/mizushima/repo/lean4-peg`
- ブランチ: `feat/pal-plain-peg-artifact`
- このメモ追加前のHEAD: `4995ae3` (`docs(pal): record final Scala test counts`)
- メモ追加前の作業ツリーはclean。今回、既存コードは変更していない。
- 前のScala移植作業の担当エージェントはすべて終了済み。
- コミットはローカルにある。pushは今回実施していない。

## 3. 完了したScala移植

Claude Codeの利用上限で止まった作業を引き継ぎ、`docs/palindromes-in-peg/` のPython **94実装モジュール・66テストファイル**に対応するScala実装を `scala/pal/` に揃えた。Python側は比較基準として変更していない。

最終統合コードで、2026-09-07 14:42に以下を実行済み:

```sh
cd /home/mizushima/repo/lean4-peg/scala
XDG_RUNTIME_DIR=/tmp/xdg-1000 sbt -batch pal/compile pal/Test/compile pal/test
```

結果: **471 passed、0 failed、0 errors、ignoredなし**。テスト部分707秒。
`git diff --check` も成功。これは `pal` サブプロジェクトの全テストであり、リポジトリ全体の `make verify` を今回再実行したという意味ではない。

主な追加・修正:

- SCAVM制御、回路、GS、window worker、最終 `GenerateWindowPal` まで移植・統合。
- `PortCoverageSuite` がPythonファイルを走査してScala対応ファイルの欠落を検査。
- `PhasePeg` のphase-return計算を単調な依存worklistへ変更。元の最小不動点と出力順を維持し、Pythonとの差分・再帰・star・長い参照鎖を検証。
- `PyDiff` のstdout/stderr逐次読み取りによる停止を修正。stderrを並行して読み、256KiBの正常／異常出力を回帰テスト。
- compactorの分割メモリマップ境界、生成器のキャッシュ無効化・中断報告も検証。

重要コミット: `e9023db` (phase worklist)、`eb55bb6` (PyDiff)、`4d89691` (旧生成器の検証分割)、`4995ae3` (最終結果)。

### 検証の境界

- **既定WindowPALの巨大文法をScalaで全生成して既存SHAと比較する検証は未実施。** 小さなcheckpointテストを、その代わりの証拠にしていない。
- 旧実験用 `GenerateGalilPeg` は現在のWindowPALとは別。`--quantum 1 --match-delay 2 --budget 2 --raw-instructions --omit-invariant-monitors --expanded-only` で1,420,678規則・50,121,014 bytesがPythonと全バイト一致。
- その逆変換後の698,145,389 bytesはScalaで生成できたが、Pythonの再帰AST登録が再帰上限100,000でも失敗し、全体比較は未検証。実際の `emitInverse` を小規模Scaffold fixtureで比較するテストは成功。
- `CompactScaffoldPeg` の2GiB超対応は分割マップ設計と小さい窓での境界テストによる。別クラス `FileGrammar` は約2GiB超を明示的に拒否する。

詳細: `docs/palindromes-in-peg/STATUS.md`、`PLAIN_PAL_ARTIFACT.md`、`docs/superpowers/plans/2026-09-07-pal-python-to-scala.md`。

## 4. Leanで証明済みのこと／未証明のこと

`lean-pal/` は既存のShallot用 `lean/` と別パッケージ。
`lean-pal/PalPeg/Existence.lean` の主定理は次の形:

```lean
theorem pal_recognizedByTotalPEG (h : RealTimeTM.RecognizedBy PAL) :
    RecognizedByTotalPEG PAL
```

具体的な機械を受け取る版:

```lean
theorem pal_in_peg_of_realTime {t s k : ℕ}
    (M : RealTimeTM.Machine (Fin 2) t s k)
    (hM : ∀ w, M.Accepts w ↔ w ∈ PAL) :
    ∃ (n : ℕ) (G : PegGrammar (Fin 2) n),
      G.IsLoffTotal ∧ ∀ w, G.Recognizes w ↔ w ∈ PAL
```

証明の接続:

1. `RealTimeTM.toSCA_accepts_iff`: 厳密実時間TM→SCAの言語保存（依存成果物）。
2. `SCAToPEG.loffBackward`: SCA→total PEG、認識言語は反転（依存成果物）。
3. `PAL_reverse_mem`: 回文の反転不変性（このパッケージ）。

`Basic.lean`、`Existence.lean`、`EvenLength.lean`、`Axioms.lean` があり、偶数長回文への制限も条件付きで証明済み。`lake build` と公理guardの成功を前作業で確認した。標準公理以外の新規公理や `sorry` は使っていない。

**未証明なのは前提 `RealTimeTM.RecognizedBy PAL`。** 有限制御・有限個のテープを持つ具体的 `M` と、全入力に対する `hM` がまだない。文献の実時間性とこのモデルとの接続・必要な正規化も証明していない。
`sorry`なしなのは「含意」の証明が完成したという意味であり、前提を証明済みにするものではない。

また、この存在定理は生成済み巨大PEGファイルを直接検証する定理ではない。依存するSCA→PEGの存在構成にはnoncomputableな番号付けがある。具体的生成器の出力まで対応付けるには別の接続証明が必要。

### 引継ぎ時にモデルの実コードで確認した注意点

`PegSeparation/Common/Compiler/RealTimeTM/Model.lean`:

- `transition` は有限状態・今回の入力記号・各テープの注目記号から次の命令を決める。
- `run` は入力リストを `foldl step` する。1入力記号につき1遷移で、入力終了後の追加計算はない。
- `Accepts` は最終状態の受理集合への所属。
- `TapeAction` は書く記号と移動を指定するが、**移動には `.stay` もある**。「必ず左右へ1セル動くモデル」と誤読しない。
- 初期テープはblank。左端からの左移動は端に留まる実装。

旧調査の「1書込/1移動」はこのアクション形式のこと。調査中のtape compression案や必要行数の見積もりは証明ではなく、設計の正しさは再確認が必要。

## 5. Lean環境と再利用できるキャッシュ

- `lean-pal/lean-toolchain`: `leanprover/lean4:v4.31.0`
- Mathlib: `v4.31.0`
- `PegSeparation`: `https://github.com/kimjg1119/peg-separation-artifact`
- pin: `c364edbc1003292097e5fbac3a5607c021226a15`（引継ぎ時も実際のcheckoutで確認）
- `lean/` 側は別バージョン・Mathlib非依存なので混ぜない。

通常のビルド:

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal
lake exe cache get
lake build
```

ルートの `make lean-pal` も利用可能。通常の `make verify` には含まれない。

**メインの `lean-pal/.lake` はまだない。** 前作業でビルドした依存・成果物は次に残っている:

```text
/home/mizushima/repo/lean4-peg/.claude/worktrees/agent-ae9087ce84c0c538c/lean-pal/.lake/
```

このworktreeは引継ぎ時cleanだった。別checkoutなので、メインに追加したファイルが自動で反映されるわけではない。キャッシュ再利用の方法を決めてから検証し、別の古いソースのビルド成功を新実装の成功として報告しない。

## 6. 再開時の入口

必要なところから読む（全履歴の再読は不要）:

1. `lean-pal/README.md` と `PalPeg/Existence.lean`: 実際の到達点。
2. 依存成果物の `RealTimeTM/Model.lean`、`Correctness.lean` と `SCAToPEG/Final.lean`: 接続先の型・制約・既存の証明。
3. `docs/palindromes-in-peg/FORMALIZATION_SURVEY.md`: 関連経路の調査。未確認の引用・正規化案を事実として引き継がない。
4. `GALIL_CLOCK.md` と `delayed_pal.py`／`scaffold_window_*.py`、読みやすい対応Scala実装: 具体的な制御・時間保証の候補。

次に必要なのは機械状態と不変量の設計、各遷移の保存、全接頭辞での判定正しさ、実時間モデルの制約、既存コンパイラへの接続。変換の既存証明を無意味に作り直す必要はないが、抽象モデルを弱めたり入力反復・長さ上限・判定オラクルを入れて元の要求を置き換えない。

ユーザーは少ないトークンでの継続を希望している。検索・ログは絞り、長いビルドにはToken Sieveを使える。過去の見積もりだけで実装を諦めず、同時に部品や有限テストを全体証明として報告しない。

## 7. 2026-09-07 夕方の更新（Fable 5.1）

- `lean-pal/.lake` を本体に複製し `lake build` 成功（依存の再取得なし）。
- 方針変更：RTTM ではなく成果物の SCA を直接構成する（`RecognizedBySCA PAL` →
  `SCAToPEG.loffBackward` → PEG）。SCA は永続ポインタ機械なので Galil の「p ステップ前の状態」
  はスナップショット辺で表せる。設計と未解決点は `lean-pal/DESIGN_SCA_PAL.md`。
- 追加した証明（sorry なし、公理 guard 済み）：
  - `PalPeg/Words.lean`：拡張則、境界＝回文接頭辞／接尾辞、周期⟺境界、Fine–Wilf（正確な
    `p+q-gcd` 境界、Mathlib `List.HasPeriod.gcd` へ橋渡し）、周期の伝播、group 補題
    `hasPeriod_minimal_of_suffix`。
  - `PalPeg/Chain.lean`：オンライン鎖算法 `chain` と `mem_PAL_iff_length_mem_chain`
    （`w ∈ PAL ↔ w.length ∈ chain w`）。これは SCA の仕様層で、実時間ではない（O(n)/step）。
- **未達**：`RecognizedBySCA PAL` そのもの。SCA 実装・実時間性（young run の cursor 実体化、
  break 後の下位構造再構築、実時間キュー）は設計に留まり、`DESIGN_SCA_PAL.md` §4 が証明義務。
- 追記：`PalPeg/Structure.lean`（レプリカ補題、最小周期回文の境界、予測補題、禁止帯
  `lsp_shift_bound`）。設計メモの (M)「成熟なら `LSP(n-p)=ℓ-p`」は **偽**（反例 `001000` を
  Lean で機械化）。昇格時の cursor を「p ステップ前のスナップショット」から取る案は break 直後には
  使えず、設計の見直しが要る（`DESIGN_SCA_PAL.md` §2 (M)、§4）。
- 追記（部品層）：`PalPeg/Groups.lean`（group 圧縮鎖、`expandAll_groupChainRev`；群数の対数上界は
  未証明）、`PalPeg/Matching.lean`（KMP 一歩、Galil 予測補題 `predictability_step`/`work_le`、
  `border_snapshot`）、`PalPeg/RTQueue.lean`（Hood–Melville 実時間キューの FIFO 仕様）。
  すべて sorry なし・公理 guard 済み。`DESIGN_SCA_PAL.md` §7 に dyadic stage 構成の要件と
  残る証明義務（オンライン Manacher、実時間 KMP の π 取得、SCA 符号化）を記載。

## 8. 上位方針（2026-09-07 夜、Fable 5.1）

目標 `RealTimeTM.RecognizedBy PAL` へは repo の dyadic stage 設計（`ALGORITHM_SPEC.md`）を
層ごとに Lean 化する。RTTM（テープ双方向）を採用し、SCA 直接構成は取り下げ。

- L0 部品（済・sorry なし）：Words, Chain, Structure, Groups, GroupsLog, Matching, RTQueue,
  Manacher, Stages（`pal_prefix_iff_stage`, `live_stages`）, Schedule（`finishTime_le`,
  `fifo_meets_deadlines`）。
- L2 進行中：GSScan（GS 走査の安全シフト・正しさ・ポテンシャル）、GSDecomp（分解の存在と L1 境界）、
  ManacherHeads（テープ上のヘッド移動の telescoping 上界）。
- L4 進行中：Speedup（1 記号 B 操作の機械 → 厳密実時間 `Machine`、線形加速）、TapeLib
  （zipper/stack/seq/counter ビュー）。
- 未着手：u 検証器の締切補題、段の組み立て（抽象 dyadic 機械の全接頭辞正しさ）、
  抽象機械の `MultiStepMachine` への符号化。
- 進捗（深夜、コミット 4cca565 まで）：L2 済＝GSScan（走査）、GSRealTime（レート k+1 で実時間、
  有界遅れ不変量 `Φ ≥ (k+1)n − k|v|`、u 検証器の締切）、GSDecomp（分解述語・k 反復補題・`KSimple`
  への橋。**L1 の厳密境界 `(k−1)s<|x|` は未証明**、弱い定数版を続行中）、MiddleJob（Manacher 版の
  中央フラグ締切。ただし TM 化は rad のランダムアクセスで不可なので repo の境界列挙版 BorderJob に
  切替中）。L4 済＝Speedup（`multiStep_recognizedBy`）、TapeLib。
  稼働中：RTQueueTapes、Assembly（段の組み立て）、BorderJob、GSScanTapes、GSVerifier、GSPreprocess。
- 進捗（コミット db53dea まで）：Assembly（段の組み立て `dyadicAnswer_correct`）、GSVerifier（u 検証器、
  オラクルなし）、StageMatcher（GS 照合器が `MatchOracle` を満たす、`dyadic_gs_mem_PAL`：各段の分解
  witness に `cut < W` があれば全体正しい）。稼働中：RTQueueTapes、BorderJob、GSScanTapes、
  GSDecomp 弱定数版、GSPreprocess、OnlineMachine（全体機械の添字モデル、中央/前処理はインターフェース）、
  ProgramMachine（構造化 `StructuredMachine` → `MultiStepMachine` → `RecognizedBy`）。
- 残：BorderJob/GSPreprocess/走査/キューのテープ化を `StructuredMachine` で組み、OnlineMachine の
  インターフェースを満たすことを示して最終定理 `RealTimeTM.RecognizedBy PAL`。
- 進捗（コミット e9bfb1e まで）：ProgramMachine（構造化機械→`RecognizedBy`）、GSScanTapes（走査の
  3 テープ化、判定 bit はオラクル→カウンタ化を続行中）、BorderJob（中央フラグの GS 境界列挙、仕事 ≤ 258|x|、
  段ごとに L1 を仮定）、RTQueueTapes（キューの 9 テープ化、`lenr≤lenf` 判定は仮定→差分カウンタ化を続行中）。
  **critical path：GSDecomp の真の L1 境界（`(k−1)s<|x|`, `(k−2)s<(k−1)p₁`）**。GSVerifier と BorderJob が
  これを仮定してるので、GS の内側削除ループの補題を形式化中。
  稼働中：GSPreprocess、OnlineMachine、GSVerifierTapes、BorderJobTapes、TextFeed（到着記号を FIFO 経由で
  走査テープへ供給）。
- 進捗（コミット c9f36a2 まで）：GSPreprocess（計算可能分解）、OnlineMachine（全体機械の添字モデル、
  `output_correct`）、GSVerifierTapes（u 検証器の 5 テープ化）。
  設計修正：段 S の分割点を S/2 に変更（パターン `rev(w.take(S/2))` は S/2 で確定、前処理 (S/2,S]、
  テキスト `w.drop S` を S から実時間走査）。これで「2W 時点での追いつき」の隙間が消える。Assembly /
  StageMatcher / OnlineMachine を改修中。
  L1 境界：欠けていた補題は「1 パス内の削除は位置 p₂ より手前で止まる」（run 0 は T 未満で終わり、
  位置 T の最小周期は p₀ に戻るので単調性と矛盾）。新エージェントで証明中（GSDecompL1）。
  稼働中：GSScanTapes カウンタ化、RTQueueTapes 差分カウンタ、TextFeed、BorderJobTapes、GSPreprocess 全体
  線形上界、GSPreprocessTapes、GSVerifierTapes の償却。
- 進捗（コミット直近）：GSPreprocess 全体線形上界 `decomposeWork ≤ (16k+38)|x|+2k+5`、RTQueueTapes の
  数値比較を差分テープに置換、GSVerifierTapes の償却（L1 不要）、GSScanTapes のオラクル bit 除去（8 テープ）、
  TextFeed（`feed_online`）。稼働中：BorderJobTapes、GSPreprocessTapes、GSDecompL1、OnlineMachine 半分割、
  MiddleBorder（BorderJob 版 MiddleImpl）。
- 22:00 の API 上限リセット後：半分割再スケジュール完了（`output_correctH`、`round_cost_leH` 条件なし、
  常駐段 ≤ 3）をコミット（413fee4）。落ちた 7 本（L1 最終補題、BorderJobTapes、GSPreprocessTapes、
  検証器/TextFeed の 8 テープ版移植、MiddleBorder、PatternTapes）を再開。加えて Main.lean（構造化機械 →
  `RecognizedByTotalPEG PAL` の糊）と InputCopy.lean（入力コピーのフロンティア書き込み）を Sonnet に依頼。
- **L1 境界の真の存在定理が取れた**（`GSDecompL1.gsDecomp_exists`、`stageOK_exists`、`gsDecomp_verifier_data`；
  鍵は「パスは第 2 周期 T の手前で停止」を最大周期の帰納で示す `pass_stops_before_second`）。コミット 4696181。
  続き：計算可能 `decompose` の出力に対する L1（`decompose_gsDecomp`）、`PrepImpl` 実装（PrepDecompose）、
  検証器の Txt2 供給（VerifierFeed）。Main.lean に糊 `pal_in_peg_of_structured` あり。
- 進捗（コミット 9907aac まで）：BorderJobTapes（6 テープ、仕事 ≤ 4000|x|）、InputCopy、MiddleBorder
  （`MiddleImplSpecH (borderMiddle) 27901`、各段 L1 を仮定）、PrepDecompose（`PrepImplSpecH`、`decompose` の
  L1 を仮定）。添字レベルの全体機械は両インターフェース実装が揃い、残る仮定は `decompose_gsDecomp` 1 本。
  稼働中：decompose_gsDecomp、GSPreprocessTapes、PatternTapes、VerifierFeed、EndToEnd（添字の端到端定理）、
  MiddleTapes（中央ジョブのテープ化＋二重バッファ出力）。残る大物：段のテープ組み立てと全体機械の
  `StructuredMachine` 化。
- 進捗（コミット c62d193 まで）：`decompose2`（失敗位置へジャンプする strip）で L1 が無条件に成立
  （`decompose2_gsDecomp`）。仕事量は窓の入れ子木で償却：子 `(k−1)q < p`（A）と兄弟の重なり `< p+q`（B）を
  証明済み、残るは木の帰納 Σp ≤ C₁T（新エージェント）。PatternTapes（段セットアップ ≤ 21h）、VerifierFeed
  （Txt2 も FIFO 供給；`.X .right` ごとの fill 版を続行中）、MiddleTapes（バッチ実行はテープ化済み、ラウンド
  組み立て続行中）、GSPreprocessTapes（firstPeriod/extendReach/secondInner 済、残り続行中）。
