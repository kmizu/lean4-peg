# 一階CBVの機械上界とCBNからの分離（作業中）

目標は、一つの固定した一階CBN文法の言語が、一階CBV-ParおよびCBV-Seqの
どの固定文法でも認識できないこと。既存の `PegSeparation.firstOrder_witness` を使う。
完成には、両CBV戦略の認識を実際の多項式時間TMへ接続する必要がある。
**この機械上界と最終分離定理は、まだ完成していない。**

## 現在証明した部分

`lean/MacroPeg/CBV/` に、既存の `DecideCBV` と同じ判定を有限の数値表で行う仕様を構成した。

- `Indexed`: 部分文字列の辞書と引数ベクトルに番号を振り、規則・引数番号・入力位置の組を
  数値リストのセルにする。`unpack_pack` と `iterate_pack` が既存の表との一致を示す。
  表の長さは `iterBoundV`、各セルの値は入力長+2以下。
- `Spans`: 辞書の各要素に入力区間を対応させる。同じ文字列を表す複数の区間を許し、
  `literalAt_spanId` と `lookup_pack_ids` が別名による検索の正しさを保証する。
- `Eval` / `EvalSpec`: 数値表と数値の引数番号を読む評価器。
  `eval_correct` が、旧 `evV` との結果一致を示す。未知・失敗・成功を区別する。
- `Decide`: 全反復を数値リストだけで行う `numericIterate` と `numericDecide`。
  `numericObservation_iff` / `numericAccept_iff` は両CBV戦略の有限導出と同値。
  `numericIterate_size` は、全反復で表の長さ・セルの値が多項式の大きさに収まることを示す。
- `Address`: 引数ベクトルの辞書順を混合基数の順位に直し、規則のオフセットと合わせる。
  `keys_get_address` / `pack_get_address` が、表全体のキー検索をせずに計算したアドレスの正しさを示す。
- `SpanMachine` / `SpanCost`: 既存の検証済み `Mach.internP` を再利用し、区間の番号を検索する
  **実際の `NProg`** とその実行証明 `spanLookup_runs` を与える。
  `spanLookupCost_poly` は辞書検索にかかる実際のスタック時間の多項式上限。

数値表で計算できること、表が多項式サイズであることだけではTM上のP所属は結論していない。
`numericDecide` の全計算を実行する機械の構成と時間上界が残る。

- `Arithmetic` / `TableRead`: アドレス式の加算・乗算を実際の `NProg` に翻訳し、
  入力と作業用スタックの保存・結果・実行時間を証明。`value_addressExpr` はその式が
  本当にCBVセルのアドレスであること、`tableRead_cell` は保存済みの表を実際に走査して
  意味論上の値を読むことを示す。`cost_poly` / `tableRead_cost_poly` が費用の多項式性を示す。

- `SpanBuild`: 入力長から区間辞書の全対を生成する二重ループ。
  `spanBuild_runs` が番号順を含む完全な出力を保証し、`spanBuildCost_poly` が生成費用を抑える。
- `Mirror` / `MirrorBuild`: 残り入力長を添字とする入力表。`mirrorBuild_runs` は読み込み済み表を
  実際に反転し、作業用スタックを復元する。`mirrorScan_literal` は区間の照合と通常のリテラルの一致。
- `CompareRows` / `ScanStep` / `ScanLoop` / `LiteralMachine`: 入力表の実際の二回走査による文字比較、
  残り長に従う照合ループ、返り値の生成とローカル領域の解放。
  `spanLiteral_runs` と `spanLiteralCost_poly` が動的リテラル全体の正しさと費用を保証する。
- `ParamMachine`: 引数番号から二つのアドレスを計算し、辞書表を走査して区間を取得する。
  `paramLiteral_runs` は辞書読出し・照合・区間フレームの解放を合成した実行証明。
  `paramLiteralCost_poly` はこれらすべてを含む多項式上界。
- `FixedLiteral` / `LexMachine`: 固定リテラル、任意文字、文字、文字範囲の実機。
  `fixedLiteral_runs` / `remainingLex_runs` は入力表を読んで正しい結果を返すことを保証する。
  `remainingLex_any` / `remainingLex_chr` / `remainingLex_range` / `literalCode_eval` が
  `eval` の基本式と対応し、それぞれ費用も多項式。
- `ControlMachine`: `altEval_runs` は明示的失敗でだけ再試行し、未確定値を保つ。
  `notAfter_runs` は否定の三値変換、`seqAfter_runs` は成功時に位置を復号して右式を評価し、
  呼出し元の位置スタックを復元する。右式の実行証明を引数に取る合成則で、全式の翻訳定理はまだ残る。

- `StarMachine`: `starEval_runs` は `evStar` と一致する完全な反復プログラム。
  実際の数値比較で厳密な位置減少を判定し、未確定・失敗・非消費成功も区別する。
  任意の呼出し元スタックの上へ局所位置・フラグを積み、終了時に復元。
  `starEvalCost_poly` は、内側の評価に多項式上界があれば反復全体にも付くことを示す。
- `SpanRegister`: 成功コードから区間の終点 `min j p` を実際の減算で作り、辞書を検索する。
  `registerSpan_runs` / `registerSpanCost_poly` は、開始位置と返り位置の大小を仮定せず、
  準備・正規化・検索・片付けのすべてを含む。
- `ExprProgram`: 全固定式の `exprProgram` と引数の `argsProgram` を具体的な `NProg` として定義。
  Parは現在位置を保ち、Seqは各引数の返り位置へ進む。引数番号を重み付き加算で順位へまとめ、
  最後に保存済みの規則表を読む。呼出しと反復は専用フレームを使う。
  **この定義全体の正しさと統一時間上界は、まだ未証明。**
- `CallArithmetic`: `rankUpdate_runs` は順位の更新を実行し、`ruleRead_runs` はその順位から
  意味論の正しい規則セルを読む。両者の実際の費用の多項式性も示す。
- `ExprState` / `CallFrames`: `EvalReady` が式の境界で保存する不変条件。
  `paramEval_runs` は環境行の実走査から動的リテラル照合までの変数参照を検証。
  呼出しフレームの準備・復元、ParとSeqの位置更新にも実行証明を与えた。
- 算術・表参照には `compile_runs_used` / `tableRead_runs_used` を追加。
  式に現れない変数レジスタが空でも利用でき、呼出し終了時に引数番号を片付けた後の表参照にも対応する。

## 残る接続

1. 固定文法に対する表の初期化とセル列挙。
2. `exprProgram` / `argsProgram` を `EvalReady` の下で相互帰納し、数値評価器との一致と統一時間上界を証明。
3. 各部品の実行証明を、完成済みの全式プログラム定義へつなぐ。特に引数の早期終了・順位累積・規則参照を合成する。
4. 規則表の全反復、開始式、受理停止までのプログラムと多項式上界。
5. 共通4ビット復号から入力表反転・辞書生成へつなぎ、`PegSeparation.nprog_in_P` へ接続して
   両戦略のTM上のP所属を証明。
6. `firstOrder_witness` のP非所属と矛盾させ、元の文字列言語で共通の非包含証人を組み立てる。

`spanLookupP` はレジスタを引数に取るので、引数の照合後に得る区間から番号を登録する際に再利用できる。
完成済みの局所部品をもって、全体のTM上界や最終分離が証明済みとはしていない。
