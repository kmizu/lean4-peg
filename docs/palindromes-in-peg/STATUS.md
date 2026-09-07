# 回文言語の素の PEG — 経過と現状（2026-09-07、lean4-peg 移行時点）

> Python 94モジュールと66テストのScala対応ファイルは揃っている。
> `pal.PortCoverageSuite` で対応先の存在を確認済みだが、全体テストの再実行やFullWindowPALのSHA再現とは別である。
> 対応表と作業単位は [移植計画](../superpowers/plans/2026-09-07-pal-python-to-scala.md) にまとめる。

この repo で作業を続けるための入口。まずこれを読み、次に `PLAIN_PAL_ARTIFACT.md`
（証人と検証）、`HANDOFF.md`（Codex の構成過程の生ログ、時系列は新しい順）、
`TRANSLATION_STRATEGY.md`（変換方針）を読む。

## 1. 主張と、その確からしさ

**主張**：`PAL = { w ∈ {a,b}* | w = wᴿ }` を認識する、マクロなしの素の PEG が
実在する。13,248,052 規則 / 672,208,000 bytes、SHA-256
`ab891da29e1959360f247e5b9b3f5d3dfec336da1f13376aa3e6b935bf3e211f`。

**確からしさ**：有限テスト＋構造的証拠であり、**全長さに対する証明ではない**。
ブログや対外的な言い方は「書けた**かもしれない**」で統一する。

| 種類 | 内容 | 場所 |
|---|---|---|
| 挙動（Codex） | 未加工入力 79 例：長さ ≤5 の全 63 語、長さ ≤33 の選択 12 語、非二進 4 語。全一致 | `generated/window-pal-verification.{json,log}` |
| 挙動（独立） | 長さ 6–7 の 5 語、64–65 の 4 語、512 の 2 語、2,048 の 2 語。全一致。1 文字あたり ≈13.3M ステップで一定 | `generated/window-pal-{independent,long,512,2048}-check.log` |
| 閉包 | 定義 13,248,052 / 参照 13,248,051（S 以外全部）/ 未定義 0 / 死に規則 0 | `analysis/grammar_closure.py`, `generated/window-pal-structure.log` |
| 再帰 | 全規則が S から到達可能。最大 SCC 4,002,097 規則。消費辺 73,261 本のうち 72,638（99%）が SCC 内 ⇒ 有限展開（DAG）ではない | `analysis/grammar_scc.py`, 同 log |
| 生成器 | 入力長パラメータなし。`compact_scaffold_peg.py` の `depth >= 16` は inline 打ち切りで、残した参照先は定義に残る | コードで確認可 |

**静的に示せていないこと**：全閉路が消費を通ること（非消費再帰の不在）。guard 判定は
過大評価（`X?` の後ろは非保証扱い）で、SCC 内に非消費辺が約 6,100 万本ある。実行時は
Rust 実行器の非消費再帰チェックが全テストで未発火。これは検証済みチェッカーの仕事。

## 2. 何をどう作ったか（要約）

1. **算法**：Galil 流のオンライン回文接頭辞判定を、二つの重なる段階（stage）だけを持つ
   コントローラで組み直す（`delayed_pal.py`）。border 計算は Galil–Seiferas 型の
   定数空間照合（`gs_heads.py`, `gs_match_heads.py`, `gs_flag_heads.py`）。
2. **実時間化**：遅延付き実時間キュー（`scaffold_window_*.py`）と predictability による
   会計（`galil_clock.py`, `GALIL_CLOCK.md`）。1 文字あたりの仕事を有界に。
3. **有限回路**：機械の 1 遷移を Boolean 欄 41,298 / pointer 欄 4,291 の回路として固定展開
   （`scaffold_window_pal.py`）。入力長はどこにも現れない。
4. **SCA → PEG**：欄 → 規則、参照 → `. X`（1 文字消費して次位置の規則）
   （`symbolic_sca2peg.py`）。ゲート 1 個 = 規則 1 個。
5. **圧縮**：単一参照の private 規則を inline（`compact_scaffold_peg.py`、Rust 版
   `rust-peg/src/bin/compact-scaffold-peg.rs`）。59,169,304 → 13,248,052 規則。

**サイズの正体**：規則の 99.66%（13,203,493）が配線ゲート、欄は 41,268 + 3,290。しかも
回路の定数畳み込みは 22 GiB で OOM して **スキップ**されている（`--skip-optimize`）。
つまり未最適化回路の直射出。大きさは翻訳の粗さであって、正しさとも言語の本質とも無関係。
`midpoint.peg`（中点を取るだけで 9,949 規則、うち 9,741 が配線）が縮図。

## 3. なぜ手で書けないか／潰した道

SCA（= 素の PEG）では、ポインタの同一性比較・長さの転送・既存ノードへの書き込みが
できない。これで eertree・Manacher・KMP（`fail[]` へのランダムアクセス）が全部詰まる。
潰した道の一覧と理由は `HANDOFF.md` §3a と `fpp.py` 冒頭。同じ穴に落ちないこと。

## 4. 再現

```sh
cd docs/palindromes-in-peg
python3 -u generate_window_pal.py /tmp/pal-window-original.peg --checkpoint /tmp/pal-window-original.sca --skip-optimize
cargo build --offline --release --manifest-path rust-peg/Cargo.toml
./rust-peg/target/release/compact-scaffold-peg /tmp/pal-window-original.peg /tmp/pal-window-fast.peg   # 約 200 秒
sha256sum /tmp/pal-window-fast.peg    # ab891da2...
python3 verify_window_pal.py /tmp/pal-window-fast.peg --runner rust-peg/target/release/plain-peg-runner --log /tmp/verify.log
./rust-peg/target/release/plain-peg-runner /tmp/pal-window-fast.peg aabbaa aababa   # 任意入力
python3 analysis/grammar_closure.py /tmp/pal-window-fast.peg   # 数分
python3 analysis/grammar_scc.py /tmp/pal-window-fast.peg       # 約 22 分、メモリ数 GB
```

### Scala 3 の再現入口

Scala側のCLIは `pal.GenerateWindowPal`、`pal.CompactScaffoldPeg`、
`pal.VerifyWindowPal` として、リポジトリのルートから次の形で実行する。

Scala全体生成のヒープ必要量は未計測なので、sbtの既定ヒープに頼らず、十分なメモリを持つホストで適切なJVM heapを設定して実行する。

`GenerateOnlinePeg` の互換性もテストで確認済み：cache signatureはScalaソースをハッシュし、`.sca`形式は相互運用できるが自動cache再利用は言語ごとに分かれる。`--memory-mib` はJVMの`-Xmx`で制約し、Pythonの`RLIMIT_AS`とは異なる。SIGTERM時は`interrupted`・`emitted=false`を報告して既存出力を保持し、終了コードはJVMが143、Pythonが130になる。現在はVolta分の実装検証を残す。

```sh
cd /path/to/lean4-peg
cd scala
sbt -batch 'pal/runMain pal.GenerateWindowPal /tmp/pal-window-original.peg --checkpoint /tmp/pal-window-original.sca --skip-optimize'
sbt -batch 'pal/runMain pal.CompactScaffoldPeg /tmp/pal-window-original.peg /tmp/pal-window-fast.peg'
sbt -batch 'pal/runMain pal.VerifyWindowPal /tmp/pal-window-fast.peg --runner ../docs/palindromes-in-peg/rust-peg/target/release/plain-peg-runner --log /tmp/verify.log'
```

Scala版の既定の全体文法を生成して上記SHAと一致させる検証は未実施。移植の差分証拠は、
各 `PyDiff` テストが明示するソース／fixture範囲に限る。

ファイル対応の棚卸しは `pal.PortCoverageSuite` がPythonディレクトリを再帰走査して行い、MAINで94モジュール・66テスト、
不足0件を確認した。件数はSuiteに固定せず、追加されたPythonファイルにも対応Scalaパスを要求する。

`CompactScaffoldPeg` は1GiBの窓を連結して2GiB超のsourceを読む設計だが、1行には別の上限がある。
一方、トップレベルの `pal.FileGrammar` はファイルサイズが `Int.MaxValue`（約2GiB）を超えると明示的に拒否する。
通常の再現手順は圧縮後の文法をRust runnerへ渡すため、後者の読み込み制限はこの手順の障害にならない。

### Lean側の条件付き定理

`lean-pal/` の `lake build` は、Kim–Park成果物の厳密実時間TMモデルを使った条件付き定理を
ビルド・公理監査する。`RealTimeTM.RecognizedBy PAL`（そのモデルでPALを認識する機械の存在）が
仮定であり、Galilの機械の書き下しと、文献の実時間性を厳密な1記号1遷移・各テープ1書込/1移動へ
正規化することは未証明。従って無条件の `PAL ∈ PEG` の証明ではない。

生成には 22 GiB 級のメモリと時間がかかる（詳細は `PLAIN_PAL_ARTIFACT.md`）。文法本体は
repo に入れない（672 MB）。SHA で固定する。

## 5. 次にやること（優先順）

### A. 証明トラック（この repo の本来の仕事）

信頼の鎖を層に分けると：

| 層 | 主張 | 状態 |
|---|---|---|
| ① 算法 | コントローラ＋GS 照合が全入力で PAL を判定し、1 文字あたりの仕事が有界 | 未証明。数学の本体（Galil 1978 相当） |
| ② 回路 | `scaffold_window_pal.py` の回路が ① の 1 遷移を実装 | 未証明 |
| ③ SCA → PEG | `symbolic_sca2peg.py` の射出が意味を保つ | 生成器を証明せず、**translation validation**（回路 C と文法 G を受けて「G は C の符号化」を検査する Lean の検証済みチェッカー）が現実的 |
| ④ inline | 非終端置換が PEG 意味論を保つ | M-PEG-6（展開の意味保存）とほぼ同型の補題 |
| ⑤ PEG 意味論 | 目標の定義 | この repo にある |

順番の提案：⑤の上に **SCA の定義**を置く → ③④のチェッカー（非消費再帰の不在も静的に
出る）→ ①②。①②は Lean で `step : Config → Char → Config`、
`∀ w, accepts (run w) ↔ w ∈ PAL`、`work (step c a) ≤ K` を書く仕事で、規模は週〜月。

### B. 工学トラック（正しさとは独立）

- 回路最適化を復活させて圧縮（定数畳み込み・共通部分式・死に欄除去をストリーミングで）。
  100 倍以上縮む見込み。**同値変形として**進め、SHA を新しい証人として固定し直す。
- Python → Scala/Lean の生成器書き直しは**別件**（コウタ判断）。書き直すと SHA 再現の鎖が
  切れて再検証（数時間）が要るので、③のチェッカーができてからの方が安全。

### C. 対外

- Zenn ドラフト：`~/repo/zenn-blog/articles/2026-09-plain-peg-palindromes.md`
  （`published: false`、nextbeat）。リンクはこの repo の `main` を指す（#6 マージ後に有効）。
  結びで論法・変換器への反例・指摘を募っている。
- macro_peg 側：#211 で木を撤去し、`examples.PalindromePegs`（Macro PEG 2 規則、
  inner/outer/bounded 族）と小さい生成文法の fixture だけ残す。**#6 の後にマージ**。

## 6. 落とし穴（実際に踏んだ）

- **sbt 2 の `test` は増分**で、居残りサーバーやキャッシュに当たると「Total 0」で exit 0
  になる。全件は `testFull`（macro_peg）か `sbt --server --batch "testOnly *"`。
- `pkill -f '<script>'` は**自分のシェル**にマッチして自爆する。PID で kill する。
- 13M 規則の解析は Python で可能だが、不動点はラウンド反復だと 1 ラウンド 8,500 個ずつしか
  剥がれず数時間かかる。`grammar_scc.py` はワークリスト版（約 20 分）。メモリは数 GB、
  Rust 実行器（文法ロードで 1–2 GB）と同時に走らせると 30 GB 機で逼迫する。
- Rust 実行器は文法ロードに 30–170 秒。長い入力は 1 文字 ≈13.3M ステップ
  （2,048 文字で約 36 分）。
- `Galil.pdf`（macro_peg 直下にあった）は著作権物。この repo には持ち込まない。

## 7. 人物と分担（記録）

- 構成：Codex（2026-09-05〜07）。方向修正はコウタ（「GB 級はおかしい、翻訳設計を疑え」
  「magic number のパッチワークをやめて変換戦略を立て直せ」）。
- 独立検証・構造解析・引き継ぎ文書・記事ドラフト：Claude Code（ここね）。
  前史（FPP の壁の分析、TM→PEG コンパイラ `tm2peg.py`、Crochemore–Perrin の周期計算）も同じ。
