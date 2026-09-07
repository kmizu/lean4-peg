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
- 進捗（コミット 4389b84 まで）：VerifierFeed の逐次 fill 版（`vfeed_online''`、仮定なし）、GSPreprocessTapes
  が secondOuter まで（1 反復 ≤ (2k+65)·work）、GSDecompose2Work（線形は Σp_j ≤ C₁T を仮定；子 (A)・兄弟 (B)
  補題は証明済み。ウチの見立てでは Σp_j は最悪 T log T になりうるので、Python で全探索して事実確認中）。
  新規：Metered（1 ラウンド固定 B 動作の de-amortization 補題）。残り：MiddleTapes のラウンド組み立て、
  前処理テープ化の strip2、段の照合フェーズ組み立て、全体 `StructuredMachine` 化、最終定理。
  **前処理の線形性が未解決の場合の代替案**：分割点を S/2 に置いたまま前処理に S/2 ラウンドしか使えないので、
  線形でなければ設計変更（別の照合器 or 別の分解法）が要る。
- 進捗（コミット ff37ac6 まで）：MiddleTapes のラウンド組み立て完了（`middle_flag_read`）、Metered（固定 B
  動作/ラウンド、`metered_phi`；`rem=0` 仮定の除去を続行中）。稼働中：PassSum（Σp_j ≤ C₁T の証明/反例）、
  EndToEnd2（`decompose2` へ切替、残る仮定は `PassPeriodSum` のみ）、前処理テープ化の strip2、
  StageMatcherTapes（段の照合フェーズ：setup → 固定 B 動作のラウンド）。
  設計メモ：テープ集合は 4 組を回して使う（常駐 ≤ 3、退役後 4S ラウンドで O(S) のクリアを分散）。
- 進捗（コミット 7fc4811 まで）：Metered（`rem=0` 仮定なし）、EndToEnd2（添字レベルの端到端、仮定は
  `PassPeriodSum 8 C₁` のみ）、PassSum（二分律・領域端の増減）、StageMatcherTapes（段の照合フェーズを固定予算
  で実行、`stage_answer_stageMatchH`）。稼働中：前処理 strip2 のテープ化、Prologue（テープ初期化/クリア）、
  PassSum2（`Σp_j ≤ C₁T` の再挑戦：着地補題）、StageTapes（段の全ライフサイクル）。
  **現状の唯一の数学的仮定**：`PassPeriodSum`（`decompose2` の 1 パス内 run start 周期和 ≤ C₁·p₂）。
  実測（k=4、T≤60 全探索＋山登り）では最大 0.39T で線形が濃厚。
- 進捗（コミット f4d0e1c まで）：Prologue、README 更新、PassSum2/3（(j,j+2) 補題、同周期領域の右端一致、
  兄弟の成長条項）。`PassPeriodSum` は依然未証明（3 回の試行が「pass 固有の着地補題が要る」で一致）。
  稼働中：前処理 strip2 のテープ化、StageTapes（段ライフサイクル）。残り：全体機械、最終定理。
- 進捗（コミット 479e7c7 まで）：StageTapes（段の全ライフサイクル、`stage_tapes_spec`）。稼働中：
  strip2 テープ化、`hgm0`（起動フェーズ分散）の解消、FullMachineTapes（全体機械：常駐 ≤3 段、
  入力コピーは「前段の凍結コピー＋新鮮なフロンティア」のペア方式）、PatternTapesPair（ペア源からのセットアップ）。
  残り：`StructuredMachine` 化（有限制御・テープ数固定）と最終定理。
- 進捗（コミット d0236f1 まで）：StageTapes の `hgm0`/`hsetup` 解消、前処理テープ化が strip2 まで
  （`stripProg2_spec ≤ (16k+32)·work + (k+4)·fuel`）。稼働中：外側ループ `decompose2_on_tapes`、
  照合器初期テープの導出（設置ではなく `setup_spec` から）、FullMachineTapes、PatternTapesPair、PassSum4。
- 進捗（コミット 38b85df まで）：StageTapes の照合器初期テープをセットアップ出力から導出（設置を撤去）。
  PassSum4（連続する子は `(k−2)/(k−1)` 倍まで；幾何成長せず、`PassPeriodSum` は仮定のまま）。
  稼働中：`decompose2_on_tapes`（外側ループ）、FullMachineTapes、PatternTapesPair。
  残り：`PrepOnTapes`/`DecompOnTapes` の具体化（有効周期の正規化込み）、`StructuredMachine` 化、最終定理。
- 進捗（コミット 34f81d1 まで）：FullMachineTapes（4 スロット回転、`full_answer_mem_PAL` は `StageIface` 前提）、
  PatternTapesPair（凍結入力対からのセットアップ、`setup_spec_pair`）。**ビルド注意**：lakefile は
  `autoImplicit = false` だが `lake env lean` はそれを読まないので、単体検査は
  `lake env lean -DautoImplicit=false <file>` で行うこと（MiddleTapes の「`lake build` だけ失敗」の原因）。
  稼働中：`decompose2_on_tapes`（外側ループ）、ProgLang（有限制御プログラム言語 → `StructuredMachine`：
  今のテープ実装は「動作リスト」意味論なので、これが最終定理への最大の残工事）、PassSum5（全探索の再確認と
  証明再挑戦）、ClearAny（任意形状のテープの消去 ≤ 3·幅+3）。
- 進捗（コミット 377c425 まで）：
  * `PassPeriodSum`：全探索＋状態空間探索で反例なし。Lean で DOWN 側を閉じた（PassSum5
    `passSumLinear_of_upSum`：UP ジャンプの周期和 ≤ C·b ⟹ `PassPeriodSum`）。PassSum6 は UP 回数 n₀ で
    `PassPeriodSum 8 (7(n₀+1))`（無条件）。**注意**：「1 パス ≤ 3 反復」は偽（[1,9,1,64,1]、b=65、Σ=76 の
    5 反復例をシミュレータで確認）。正しい構造は「脱出周期 P > (k−1)p_c − 1 − 消費量 t_c」（Fine–Wilf）で、
    根の周期は幾何的に成長する。証明は PassSum7 で継続中。
  * ProgLang（有限制御プログラム言語 → `StructuredMachine`、`progMachine_recognizedBy`）完成。既存の
    動作リスト実装の移植を GSScanProg から開始。
  * 前処理テープ化 `decompose2_on_tapes` 完成、オラクル完全除去。ただし費用上界に fuel 由来の二次項があり
    線形化中。
  * PrepInstances：`stage_tapes_spec'` 用の `res`/`GSCore`/`hs` パッケージ済。インタフェース側の不備を
    4 点発見（`PrepOnTapes.post` の前提条件欠如、二次費用、`p₁=0` で `hkp` 矛盾、`OvTapes` のテープ不足と
    `decompose`/`decompose2` の不一致）→ StageTapes / MiddleTapes / GSPreprocessTapes を修正中。
  * ClearAny（任意テープの消去 ≤ 3·幅+3）。
- 進捗（コミット b36837a まで、2026-09-08 深夜）：
  * **`PassPeriodSum` の現在地**：PassSum7 で「Σp ≤ 2·(パス内最大周期)」に帰着（スケール不変、実測最大 1.304、
    自己相似族の極限 ≈1.31）。PassSum8 で木の再帰を閉じた：**残る唯一の命題は「同じ親の連続する子（兄弟）の
    周期比 ≥ 14/5」**（`PassHasTree`；実測の最小比は 7.1、根同士は 7.4）。これが取れれば
    `passPeriodSum_eight_of_hasTree : PassPeriodSum 8 2`。PassSum4 の `children_growth` は比 6/7 しか出せず、
    差は「子の部分木の消費量 C(c) を |R_c| でなく再帰的に抑える」こと。`dichotomy_insufficient`（PassSum7）で
    二分律だけでは不可能なことも形式的に示した。
  * **有限制御化（ProgLang 移植）**：完了＝GS 走査器（GSScanProg）、実時間キュー（RTQueueProg）、
    検証器の比較分岐（GSVerifierProg、8→10 テープ持ち上げ `exec_lift`）、境界列挙の一部（BorderJobProg）。
    発見した「動作リストのままでは有限制御で実現不能」な箇所：(a) 検証器のシフト分岐（Txt2 の残差移動を走査の
    シフトループに融合する必要）、(b) BorderJob の `periodActs`（カウンタ消去後の復元；第 2 カウンタが要る）、
    `uBack`/`resetWalk`（probe-tail 形へ書き換え）、(c) TextFeed（テープ添字の直和で解釈を合成する組合せ子が
    未作成）。段セットアップの移植 PatternProg は途中（1081 行、sorry なし、12 テープ実体化の手前）。
  * **インタフェース修正**：`PrepPre` 前提条件、`rateS=160`、`DecompOnTapes.dec/decOK` フィールド化、
    `OvTapes` に S1–S9、前処理費用の線形化、オラクル完全除去。`prepInstance`（decProg → `PrepOnTapes`）は
    9 テープ→12 テープ埋め込み＋prologue/epilogue の構築が未着手（レート制限で中断）。
  * **残作業（順）**：prepInstance と decompInstance の具体化 → `StageIface` の具体化（`stage_tapes_spec'`＋
    `PrepInstances.prep_res_eq5`）→ 上記 (a)(b)(c) の書き換えと残りの移植（前処理・中央ジョブ・段・全体機械）→
    全体機械を ProgLang の 1 ラウンド Prog として組み、`progMachine_recognizedBy` → `Main.pal_in_peg_of_structured`
    で最終定理（`PassPeriodSum` が未証明なら「兄弟比 ≥ 14/5」を仮定した条件付き定理として明記）。
- **次の一手（数学、2026-09-08 深夜に判明）**：木解析の実測（入れ子べき乗語 1500 本、ノード 1500 個）で
  「領域 R_c 内での子孫の消費量 C(c) < p_c」（最大 0.915·p_c）、1 ノードの子は最大 3。**補題 C(c) < p_c**
  （c の子孫はすべて R_c の最初の 1 周期以内に始まる）が取れれば、S1（脱出周期 P > (k−1)p_c − 1 − C(c)）から
  兄弟比 > (k−2)p − 1 ≥ (14/5)p が即座に従い、PassSum8 の `PassHasTree` → `PassPeriodSum 8 2` が閉じる。
  証明の筋：領域は p_c 周期的なので、オフセット ≥ p_c に最初に到達する子孫 j の p_c だけ左の「翻訳像」は
  同じ最小周期・同じ走行長を持つ仮想ノードで、直前に訪れたノード i の走行 [a_i, E_i) の内部（尾部 R_i より前）に
  落ちる。UP/DOWN で場合分けして Fine–Wilf で矛盾を導く（未完；agent はレート制限で 3 時まで停止）。
- 進捗（このセッション、PassSum9.lean 追加、コミットせず）：`C(c) < p_c` を **8873 語・35117
  ノード**（seed 1–25、深さ2–6、長さ〜6万まで）で再確認、最大比 **0.9255**（反例なし）。
  ヒルクライム（ビット反転）は周期構造を壊すだけで有効な反例探索にならなかった。
  Lean 側の追加ファイルは既存定理の再掲だけだったので破棄した（`#print axioms` は `[propext, Quot.sound]`
  のみ）を追加したが、`consumption_lt_period`（翻訳像 → Fine–Wilf 矛盾の場合分け）は
  本セッションでは組み上がらず、**新しい証明済み定理は追加できなかった**。唯一残る課題は
  依然として `PassSum8.PassHasTree`。
- 進捗（2026-09-09 早朝、コミット 461ca0c 以降）：
  * **`PassPeriodSum` の現在地（PassSum9）**：走行終端不変量 (E)「c の子孫 j は E_j < a_{c+1} + p_c + p_j」で
    C(c) < p_c と子孫開始位置の上界が出る（証明済）。(E) の DOWN 側は証明済（`runEnd_down_step`）、UP 側は
    「P + q ≤ r_j」の場合のみ証明済（`runEnd_up_step_le`、Fine–Wilf の周期伝播エンジン
    `period_factor_propagate`）。**残る唯一の命題**：UP 側で r_j < P + q（実測 96% のケース）のとき、
    最鋭の形は t + P ≤ p_c（t = 子孫の開始オフセット；実測 t ≤ 0.23(p_c − P)、(E) の実測スラックは 2–3 セル）。
    「span_i ≤ q_{i+1}」（前回の帰着）は偽（u = 0^m 1 (0^7 1)^8 w で反例、実測比 2.88）。
  * **有限制御化**：`setupProgL`（入力非依存の段セットアップ、カウンタ駆動＋左番兵、`VEncodes'` 到達）完成。
    検証器は融合巻き戻し `uxWalk` まで完成（Prog 実現 `shiftProg`/`vprogX` は作業中）。BorderJob は uBack 済、
    periodActs/resetWalk 作業中。**`DecompOnTapes` は充足不能と判明**（`Act` に P/U 書き込みがない；
    `decompOnTapes_isEmpty`）→ `Pset`/`Uset` 構成子を追加中。`PrepOnTapes` に禁止記号パラメータと
    `len_le` の前提条件を追加（費用はテープ内容依存のため）。TextFeed は `fill'`（横断書き込み）が作業中。
- 進捗（2026-09-09 午前、コミット 25f9b3d/5ab98d7 まで）：
  * **`PassPeriodSum`**：PassSum10 で組み立てが完全に閉じた——`passPeriodSum_eight_of_treeFacts`
    （`RootGrowth ∧ LastChildBound ⟹ PassPeriodSum 8 2`、再帰 `stripLoop2` 上に直接）。`LastChildBound` は
    `child_period_bound` から従う（貼り付け中）、`RootGrowth` は `sibling_growth_eight` と
    `consumption_lt_period_of_dichotomy`（(G)∨(H) ⟹ C(c) < p_c）から従う。**残る唯一の未証明命題は (H)**：
    「t_j ≥ (k−1)p_j な子孫は周期境界を跨がへん（E_j < a_{c+1}+p_c）」。自己相似族の正しいコーパス（閉じた
    ノードに ≥2 子孫、332 例）で違反 0。(E) は反例あり（比 1.027）で不要になった。
  * **有限制御化**：完成＝GS 走査器、実時間キュー、検証器（`vprogX`、`vprogramX_amortized` A=9k+14/B=16、
    `matchProg`）、境界列挙 1 ステップ（`ovStepProg_exec_full`、`Act` に `Pset/Uset`）、段セットアップ
    （12 テープ `setupProgL`、13 テープ対版 `setupProgPairL`、カウンタ駆動＋左番兵）、TextFeed（`fill'`、
    phase 1）、ProgLang 直和組合せ子、**持続制御機械 `progMachineP`（`progMachineP_grind`）**。
    作業中：前処理 `decProg` の Prog 移植、中央ジョブ Prog の番兵駆動化、TextFeed phase 2、StageTapes の
    X 版（Ψ 込み Metered）。
  * **テープ意味論側**：`prepInstance`（`PrepOnTapes` の具体化、`forb`・`len_le` 前提付き）、
    `StageIfaceInstance.stageIface`（`full_answer_mem_PAL_of`）完成。`DecompOnTapes` は `EntryBlank` 前提が
    要ると Lean で証明（`decompOnTapes_isEmpty`）→ MiddleTapes を修正中、`decompInstanceB` は修正後の
    インタフェースの witness。生の `DecOK` 仮定を `gsDec2` 版に置換中。入力コピーの左番兵化
    （`InputCopySentinel`、FullMachineTapes `stage_birth_pair_prepView`）完了。段誕生時の初期テープ
    （`hinit`）構築中。
  * **残り**：段ライフサイクルを 1 本の持続 Prog に（idle→前処理 grind→セットアップ→照合＋中央ジョブ）、
    全体機械の 1 ラウンド Prog（4 スロット＋入力コピー＋消去）、Prog 機械の挙動とテープ意味論
    （`full_answer_mem_PAL_of`）の対応、`progMachineP_recognizedBy` + `pal_in_peg_of_structured` で最終定理。
- 進捗（2026-09-09 昼、コミット 6eea622 まで）：
  * **`PassPeriodSum`**：`PassSum10.passPeriodSum_eight_of_consumption` により残る仮定は `Consumption`
    （再帰上の C(c) < p_c）ただ 1 つ。証明済みの部分ケース（PassSum9 冒頭の要約参照）：DOWN 伝播、
    最初の子、早期 UP（`up_violation_early`、UP の ~95%）、深い横断の q₁ = P 重なり（glue）、q₁ < P（dvd、
    両側）。残る角 2 つ（r₁ = L の循環構成、q₁ < P で Fine–Wilf 窓が入らん場合）は実測 0 例
    （2286 子孫、横断 69 はすべて浅く・すべて直接の子）。循環構成の直接構成を試行中（見つかれば設計に影響）。
  * **有限制御化**：TextFeed 完了（phase 2 `feed_online_prog`）、一様分解器の部品完了、前処理 Prog の
    カウンタ層完了（分岐比較層を作業中）、中央ジョブ Prog は数値展開を除去済み（MiddleTapes 側の
    フラグ番兵・S3/S4 複写・`keepS` 緩和・`clearF` 掃引の 4 点修正待ち）、StageTapes X 版
    （`stage_tapes_specX`；feed 付き `vprogramX` ステップと Ψ 込み Metered を作業中）。
  * **テープ意味論側**：`stageIface`＋`initOf_hinit`（`hinit` は `S/2 ≤ |w|` ガード付きで充足）、
    `PrepPre.inb` は番兵つき `w.take L` の形に直す必要あり（未来の入力を要求してしまう；証明付き）。
    `DecompOnTapes` の `EntryBlank` 前提と `gsDec2` 参照モデルへの置換を作業中。
- 進捗（2026-09-09 午後、コミット f4f40ca まで）：`lean-pal/ASSEMBLY_PLAN.md`（最終組み立て設計：T=260 テープ、
  直列化＋テープ再開マーカー、`roundBody_exec` を核とする対応証明、残り約 6,300 行）。設計で見つかった
  ギャップ 3 点を並行修正中：`progMachineP` の到着動作を複数テープ書き込みに一般化、入力アルファベットの
  埋め込み ι : Fin 2 ↪ Fin sc（`full_answer_mem_PAL_of` は Fin 2 では空虚）、`MState.cp1/cp2` の有限化。
  MeteredX（Ψ 込み Metered）は `TightLagBoundary` を残して完成（選言不変量で攻略中）。前処理 Prog は
  第 2 フェーズ再設計（`orcR` 閾値カウントダウン、Cd 解放）中。中央ジョブは目印ツールキット完成、
  MiddleTapes 核の書き換え（フラグ/継ぎ目/消去＋gw カウンタ）待ち。数学：PassSum11 で循環角を
  `t + q₁ ≤ r₁` の下で閉じ、残りは `RemainingGap`（実測 8,820 子孫で 0 例）。
- 進捗（2026-09-09 夕、コミット 8873899 まで）：`PrepPre`/`SetupPre` を番兵形に修正し全体ビルド成功。
  `InputEmbed`（入力 Fin 2 ↪ Fin 9 の埋め込み、`full_answer_mem_PAL_embed`）、`ProgLangPersist2`
  （複数テープ到着、`progMachinePM_rounds_effect`＝組み立て用ラウンド帰納）、`DecompUniform` 配線完了
  （窓仮説つき `DecompOnTapesW`、Cd=40290C₁+220680）。**設計判断 2 つ**：(a) MeteredX の TightLag 経路は
  `debtSlack_false` で不成立と証明→検証器の U テープを 2 本にして巻き戻し費用を消す（Ψ 不要、元の Metered が
  そのまま使える）方針に変更、作業中。(b) 前処理 `orcR` は 9 テープでは O(1)/step 不可（符号付きカウンタに
  4 本必要）→ 11 テープ化、作業中（段側の埋め込みは誕生時に空の `sT`/`sX2` を一時利用）。MiddleTapes 核の
  書き換え（窓仮説・継ぎ目・消去・cp1/cp2 有限化・S10/S11）も作業中。
- 進捗（2026-09-09 夜、コミット 610446b まで）：`PassSumGen`（一般アルファベット `Consumption` ⟹ `PassPeriodSum`）
  と `full_answer_mem_PAL_of_embed'`（唯一の数学仮定 `hcons`、sc=9 版あり）。前処理を 11 テープ化（`OvTapes` は
  15 のまま：Ca↦Cnt、Cb↦U）。検証器：`rewind_not_pointwise` で巻き戻し設計の点ごと費用不可を証明→
  **ジグザグ u 検証器**（`GSVerifierZ`、巻き戻しなし、1 前進あたり 4 移動で `prefix_verifier_deadline` から
  締切成立）に切替、テープ/feed/Prog/段の 4 層を作業中。段ライフサイクル骨格 `StageLifecycleProg`
  （`Resumable`＝PC テープでチャンク再開、`stageRoundProg_effect`）完成、全体機械ラウンド本体
  `FullMachineProg`（4 スロット直列化、到着、消去、受理フラグ、`progMachinePM_rounds_effect` 接続）作業中。
  MiddleTapes 核書き換えと `decProgP` は継続中。
- 進捗（2026-09-10 未明、コミット dc09d00 まで）：`FullMachineProg`（T=260、直列化ラウンド本体、ラウンド帰納、
  `pal_SAccepts_iff_of`／`pal_recognizedBy_of`；空語 ε の受理は初期フラグの引数化で修正中）。前処理は 12 テープ
  （符号付きカウンタの核 `orcAB` 完成、第 2 フェーズ仕様の再証明と組み立てを新 agent で継続）。段バンドルを
  13 スロットに拡張して `PrepInstance` を再埋め込み中。MiddleTapes (1)（窓仮説つき `DecompOnTapes`）着地、
  (2)–(5) 継続中。ジグザグ検証器のテープ/feed/Prog/段の 4 層と、スロット予定表（`stageInSlot`/`Restart`）の
  単進カウンタ実現を作業中。最終定理の残り：具体 Prog の差し込み（`hstepF/G/I`）と `hPAL` の接続。
- 進捗（2026-09-10 早朝、コミット 2ffdf1b まで）：**ジグザグ u 検証器が全 5 層で完成**（`stage_tapes_specZ`：
  `Metered` 無改造、A=9k+14/B=16、レート 918、Ψ なし）。段バンドル拡張＋`PrepInstance` 再埋め込み完了、
  `progMachinePMb`（初期フラグ）で ε 受理を修正、`fullAnswer_zero`。MiddleTapes は S10/S11 と cp1/cp2 の
  有限化（Fin 14 世代 = 28 テープ、4 本化には再利用スケジュールの再設計が要る）まで。
  Opus のレート制限（8 時リセット）で中断：前処理 `decProgP` の第 2 フェーズ再証明、MiddleTapes の継ぎ目/
  消去/具体 `batchProg`、スロット予定表 `SlotSchedule`（書きかけ）。残り：これらの再開、具体 Prog の
  `FullMachineProg` への差し込み（`hround`/`hstepF/G/I`）、`pal_SAccepts_iff_embed`、最終定理。
  数学は `Consumption`（残角 `ShortRunGap` 1 条件）を仮定として保持。
