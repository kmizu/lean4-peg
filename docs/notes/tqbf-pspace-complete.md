# TQBF の PSPACE 完全性の形式化

`lean/Complexity/` に、計算モデルから `PSPACEComplete TQBF`（`Complexity.tqbf_pspace_complete`）までを Lean 4 で形式化した。
公理は Lean 標準の `propext` / `Classical.choice` / `Quot.sound` のみ（`lean/Audit.lean` で固定）。

## 定義（何を証明したか）

- **機械**（`TM.lean`）: 決定性 `k` テープ TM。状態 `0` 受理・`1` 拒否・`2` 開始、記号 `0` 空白・`1`/`2` 入力ビット。
  構成はテープを関数で持つ。停止状態では `step` は恒等。
- **クラス**: `Decides`（全入力で停止し、受理 ⇔ 所属）、`SpaceBounded s`（実行中の全構成が `s |w|` セルに収まる）、
  `PSPACE L := ∃ k M s, IsPoly s ∧ M.Decides L ∧ M.SpaceBounded s`、`PolyTimeComputable f`（多項式歩数で受理停止し、
  テープ 0 の先頭に `f w` とその後の空白）、`Reduces`（多項式時間多対一）、`PSPACEHard`、`PSPACEComplete`。
- **TQBF**（`Qbf.lean`）: 冠頭量化子列＋RPN 母式（未定義変数・スタック不足は `false`）。符号は 4 ビット固定幅トークン。
  `TQBF s := (Qbf.decode s).value = true`。復号は全域で、`decode (encode φ) = φ`（`QbfCodec.lean`）。
  符号でないビット列も何らかの式に復号される、という約束で言語を定めている。

## 証明の構成

1. **困難性の核**（`CfgEnc` / `WfSem` / `StepSem` / `Savitch` / `TopFormula`）: 構成をブロック変数で符号化し、
   `reach t X Y`（`2^t` 歩以内に到達）を Savitch の分割で量化子付き式にする。`reduction_correct`。
2. **機械の層**: 構造化プログラム → TM（`Prog.lean`）、リスト機械（各テープがスタック）→ 構造化プログラム
   （`ListMachine` / `Macros` / `ListCompile`）、入出力（`ListIO`）、`lm_pspace` / `lm_polytime`（`ListClasses`）。
3. **判定器**（`TqbfDecode` / `TqbfResolve` / `TqbfEval` / `TqbfFrames` / `TqbfDecider`）: ビット → トークン → 量化子と母式 →
   変数参照を「最新の同名量化子までの段数」に静的解決（葉では全変数が束縛済みのため）→ フレームのスタックで量化子を評価。
   領域は入力長の二次。`tqbf_in_pspace`。
4. **帰着**（`Tmpl` / `RedTmpl` / `TmplLM` / `TmplBound` / `Unary` / `Hardness`）: 帰着の出力 `encode (redQbf M S w)` を
   テンプレート（カウンタのループ・条件・名前の出力）で記述し（`redTmpl_denote`）、テンプレート解釈器の正しさ
   （`compileT_spec`）と歩数の多項式上界（`ucost_le`）で多項式時間計算可能性を示す。`tqbf_hard`。

## 正直に書いておくこと

- 空間上界 `s` は任意関数なので、帰着では `IsPoly` の上界 `c (n+1)^d` に取り替えている（`SpaceBounded` は単調）。
- 既存の Macro PEG の困難性（`MacroPeg/QbfHard.lean`、CNF 母式の QBF）との接続はまだ形式化していない（表現が違う）。
  Macro PEG 側の「PSPACE 困難」は引き続き「TQBF が PSPACE 完全」という事実を外部の前提として使っている。
- 途中で Sonnet（サブエージェント）が復号プログラムのバグ（`fin` の直前の `1` を捨てていなかった）を見つけ、修正した。
