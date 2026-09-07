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
