# 一階CBVのTM上のP上界と、CBNからの共通分離

`PegSeparation.firstOrder_cbn_not_cbv` を無条件に証明した。
元の文字列言語 `L : List Char → Prop` に対し、結論は次の形。

```text
∃ L, IsFirstOrderMPEL L
   ∧ ¬ IsFirstOrderCBVPEL callByValuePar L
   ∧ ¬ IsFirstOrderCBVPEL callByValueSeq L
```

証人は既存の `PegSeparation.firstOrder_witness` が与える固定一階CBN文法。
その言語は共通の入力符号化で、実際のTM上のPに属さない。
今回、両CBV戦略の認識を実入力から停止までの多項式時間TMへ接続し、
同じCBN言語を認識するCBV文法が存在すると矛盾することを示した。

## 定義と範囲

- 一階は `MGrammar.FirstOrder` / `MExp.FirstOrder`。高階呼出しを含まないという意味で、
  固定した規則の引数個数には制限を置かない。
- CBNは `MacroObs`、CBVは戦略を明示する `SObs`。いずれも全入力を消費した成功で受理する。
- `IsFirstOrderCBVPEL s L` は、一つの固定文法・固定開始式がすべての文字列で `L` と一致すること。
  最終定理は、同じ `L` がParのどの文法にもSeqのどの文法にも属さないという共通の証人。
- 機械の入力には既存の `FirstLanguage` と同じ4ビット復号を用いる。
  短い最後のグループを捨てる処理も既存の `tokenWord` と同じ。
  元の文字列言語の同値性をこの共通入力へ制限して矛盾を導くので、最終結論は文字列言語上にある。
- P非所属や時間階層を追加の前提にはしていない。CBVからCBNへの包含はこの定理の主張に含めない。

## 実行する機械

`MacroPeg.CBV.inputProgram g s e` は、固定された文法と式から構成した具体的な数値スタック機械。
実行時に意味論の関数表や自由な配列アクセスを与えない。

1. 既存の `loadTokens` で実際のビット入力を復号し、入力表と長さを作る。
2. `MirrorBuild` が入力表を反転して残り入力長を添字にし、`SpanBuild` が全区間対の辞書を生成する。
3. `TableInit` が辞書長・入力長・固定文法から表のセル数を実算術で計算し、ゼロ表と反復カウンタを作る。
4. `EnvSweep` が引数番号ベクトルを辞書順に列挙し、`PositionSweep` が全位置の式評価を行う。
   `RuleSweep` は規則順に結果をつなぎ、`numericRound` と一致する次の表を生成する。
5. `Iteration` が次の表を実際に転送して入れ替え、`iterBoundV` 回の反復で対応する `tblV` に到達する。
6. `LoadedProgram` が開始式を評価し、返り値が残り入力ゼロの成功コードである場合だけ受理停止する。

`InputMachine.inputProgram_halts` が、この全経路の停止・答え・実行費用を証明する。
`CBV.language_in_P` は `PegSeparation.nprog_in_P` の検証済み変換を使い、
数値スタック機械から文字スタック機械、さらにTMへ接続する。

## 表と式評価の検証

- `Indexed` / `Spans` / `Address`: 規則・引数区間番号・位置を数値行へ対応づける。
  区間が同じ文字列を表す別名であっても、意味論の表と参照結果が一致する。
- `Arithmetic` / `TableRead`: 加算・乗算・アドレス計算と、保存された行の実走査。
  `compile_runs_used` / `tableRead_runs_used` は、式が使う入力レジスタだけに値を要求する。
- `SpanRegister` / `ParamMachine`: 成功区間を実減算で正規化して辞書を検索し、
  変数参照では環境行から番号と区間の両端を取得して入力を照合する。
- `CompareRows` / `ScanStep` / `ScanLoop` / `LiteralMachine` / `FixedLiteral` / `LexMachine`:
  実際の文字読出し・比較・照合と、EOF・失敗・返り位置の正しさ。
- `ControlMachine` / `StarMachine`: 未確定・失敗・成功を保つ選択・連接・否定、
  実比較による厳密な位置減少を条件とする反復。ローカルフレームは終了時に復元する。
- `RankedArgs` / `ArgStep` / `ArgsRuns` / `CallQuery`: 引数の早期終了、ParとSeqの位置制御、
  混合基数順位の累積、正しい規則セルの実参照。
- `ExprRuns.exprProgram_runs`: `EvalReady` と有効な番号環境の下で、
  全固定式の `NProg` 実行が数値評価器 `eval` と一致する。
  `eval_correct` / `numericAccept_iff` が、一階CBVの元の有限導出へ結果を接続する。

## 多項式上界と依存監査

辞書長は `(n+1)²` 以下。全規則のアリティの和を固定値 `A` とすると、表の長さと
反復回数は `規則数 · ((n+1)²)^A · (n+1)` 以下、引数の順位は `((n+1)²)^A` 以下。
表構築、文字比較、辞書・表の実走査、単進数での算術、表の転送をすべて費用に含める。
`loadedCost_poly` と `setupCost_poly`、既存の入力読込み上限から、実ビット長の多項式上界を得る。

`lean/MacroPeg.lean` / `lean/Shallot.lean` に統合し、`lean/Audit.lean` は主要部品から
`CBV.language_in_P` と `PegSeparation.firstOrder_cbn_not_cbv` までの依存を固定する。
依存は `propext`、`Classical.choice`、`Quot.sound` の標準項目のみ。
