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

## 残る接続

1. 入力区間の辞書を生成する実機、固定文法に対する表の初期化とセル列挙。
2. アドレス計算・表参照のプログラム（完了）を各式の呼び出し評価へ組み込む。
3. 入力区間で与えたリテラルの照合、固定式の `eval` / Par・Seq引数評価を実行するプログラム。
4. 規則表の全反復、開始式、受理停止までのプログラムと多項式上界。
5. 既存の共通4ビット復号と `PegSeparation.nprog_in_P` へ接続して、両戦略のTM上のP所属を証明。
6. `firstOrder_witness` のP非所属と矛盾させ、元の文字列言語で共通の非包含証人を組み立てる。

`Complexity.Univ.subTo`、`Mach.ve_mul`、`peekAt` などの既存の検証済み部品を再利用できる。
`spanLookupP` はレジスタを引数に取るので、全体機械への組み込み時に別の機械へ書き直す必要はない。
