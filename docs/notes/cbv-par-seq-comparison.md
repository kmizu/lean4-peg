# 一階 CBV-Par と CBV-Seq の言語クラス比較

## 目標と現在の範囲

元の `List Char` 上で、固定文法・固定開始式・全入力消費による
`IsFirstOrderCBVPEL .callByValuePar` と `IsFirstOrderCBVPEL .callByValueSeq`
を比較する。目標は、言語を変えない双方向の文法変換、または片方のクラスに属して
他方に属さない言語の証明である。

**一階 Seq ⊆ 一階 Par を無条件に証明した。逆方向と真包含は未解決。**
言語クラスの定理は `Shallot.PegSeparation.firstOrder_seq_subset_par`
（`lean/Shallot/Peg/Separation/CBVStrategies.lean`）。
既存の CBN との結果を合わせると、`一階 Seq ⊆ 一階 Par ⊊ 一階 CBN` となる。

`ParSimulation.translate source start` は元の文法と開始式だけから一つの固定文法を作る。
`translate_recognizes` は、全ての元の文字列 `x : List Char` について、
生成先 Par の全消費成功とソース Seq の全消費成功が同値であることを証明する。
空入力も含み、符号化・パディング・入力長の制限・ソースの停止性を仮定しない。

## 接頭辞で位置を持つ

Par 文法の全補助規則を元入力 `x` の先頭で実行する。
数 `k ≤ x.length` を、リテラル `x.take k` として保持する。この表現なら、
他の位置へ移動せずに引数として何度でも渡せる。
元の捕捉文字列自体を値として運ぶ代わりに、その始点と終点を二つの接頭辞で運ぶ。

接頭辞の長さを比較するには、二つの値を同時に一文字ずつ伸ばす。
同時に入力末尾へ達する場合だけ等しい。この構成は入力文字の内容によらず、
入力の再符号化や特定の反復文字を必要としない。

証明は `lean/MacroPeg/CBV/` の次のファイルにある。

| ファイル | 証明したこと |
|---|---|
| `RootObservation.lean` | 任意の戦略の観測合成、有限の真偽テスト、失敗しても別分岐へ流れない条件分岐 |
| `PrefixCounters.lean` | Par の捕捉引数の一意性と呼び出し展開、接頭辞カウンタの等値判定 |
| `PrefixDecrement.lean` | 他のカウンタを保持した正のカウンタの減算。継続との観測同値 |
| `PrefixSearch.lean` | 他のカウンタを保持した全入力位置の有限探索 |
| `PrefixSpans.lean` | カウンタが指す位置の文字の検査、二位置の文字の比較 |
| `PrefixInterval.lean` | 元入力の任意の二区間の等値判定。固定二規則の全文字版も構成 |
| `PrefixEndpoint.lean` | 有限の評価結果の終点検査と、静的リテラルに対する正確な終点テスト |
| `PrefixOrder.lean` | 二つの接頭辞カウンタの大小関係の有限判定 |
| `PrefixClock{,Grammar}.lean` | 固定幅時計の借り下がり、実際の有限規則ブロックと継続の観測同値 |
| `ParSimulation/Control.lean` | ソースの部分的結果に対する選択・否定の合成、実際の名前付き規則による逐次合成の成功・失敗テスト |
| `ParSimulation/Terminals.lean` | ソースの全ての原子式について、任意の戦略・表近似・環境に対する `evV` の成功と明示的失敗の再現 |
| `ParSimulation/Parameters.lean` | 捕捉パラメータの成功と有限失敗、環境外の参照の失敗 |
| `ParSimulation/Repetition.lean` | 位置の進行を要求する反復。空成功や未定義から偽の受理を導かない |
| `ParSimulation/Compiler{,FirstOrder,Layout,State,Adapters}.lean` | 実行可能な生成器、一階性、実際のアドレス配置、捕捉環境と表近似を結ぶ状態表現 |
| `ParSimulation/Compiled{Parameters,Control,Sequence}.lean` | 実際の生成コードのパラメータ・選択・否定・反復・逐次合成の正しさ |
| `ParSimulation/{LookupRouting,LookupRules,CompiledLookup}.lean` | 実際の時計付き規則検索とソース表の一段の対応 |
| `ParSimulation/{ArgumentState,ArgumentRouting,CompiledArguments,CompiledCalls}.lean` | 捕捉値の順序・呼び出し元環境・逐次位置を保つ実際の引数段階 |
| `ParSimulation/CompilerCorrect.lean` | 時計帰納法と構文帰納法を組み合わせた無条件の有限表シミュレーション |
| `ParSimulation/Recognition.lean` | 全時計の初期化・空入力・元文字列の全消費による受理保存 |

`counterGrammar_interval` は、入力に依存しない一つの一階 Par 文法について、
全ての文字列・全ての有効区間・全ての観測を量化する。
区間が等しければ元入力の先頭で成功し、異なれば明示的に有限失敗する。
空入力、空区間、任意の Lean 文字も含む。

`predecessor_iff` は継続の停止性を仮定しない。継続が有限失敗する場合も、
観測が存在しない場合も含む観測同値である。
一方 `exists_obs` は検査対象の全位置でテストが有限に決まることを明示的に要求する。
未定義の評価を否定して「失敗」にする構成にはしていない。

`ParSimulation.sequence_success_test` と `sequence_failure_test` は、
構成要素の成功・失敗テストから、実際の探索規則と中間位置の検査規則を通じて
ソースの `seqResult` へ接続する。全体のシミュレーションでは、
これらの構文節の証明を引数段階と表検索の証明へ組み合わせている。

## 実際の生成コードへの接続

`ParSimulation.compileCandidate` は一つのソース Seq 文法と開始式から Par 文法を生成する。
入力依存の非終端記号や入力の再符号化を導入しない。
各ソース式には成功と明示的失敗の二つの検査規則を割り当て、
両方が偽となる表近似の未定義の場合を保存する。

`compileCandidate_firstOrder` は、出力される全規則の一階性を証明する。
`compileCandidate_at` は、収集した全ソース節の全局所スロットについて、
実際の生成文法での検索結果が生成した規則に一致することを証明する。

この配置を使って `compiledAtom_correct`、`compiledParameter_correct`、
`compiledAlt_correct`、`compiledStar_correct`、`compiledNot_correct`、
`compiledSequence_correct` を証明した。これらは、子の式の正しさを受け取り、
ソースの実際の `evV` に対応づける定理である。
`compiledArguments_correct` が実引数の捕捉を、`compiledLookup_correct` が時計を
一段減らす規則本体への遷移を証明する。これらにより
`compiledEvaluator_correct` には呼び出し処理やシミュレーションの仮定が残らない。

最終翻訳では、ソースの固定アリティ上界を `sourceArityBound` で取り、
`clockDigits` 個の基数 `n+1` の桁を全て `n` で初期化する。
非空入力では、既存の `fullClock_eval_iff` が全ての有限導出を捉える十分性を保証する。
空入力はソース依存の定数分岐で処理する。
最後に成功テストから元入力全体を消費することで、元の全消費の言語へ接続する。

`scripts/check-seq-par-candidate.lean` では、捕捉・複数引数・捕捉値の転送・再帰・
左再帰による未定義・空成功反復・否定・規則なし・引数個数不一致などを含む
228 ケースで、ソース Seq と生成先 Par の全消費の受理結果が一致した。
ソースは燃料400、生成先は燃料2000で比較し、生成先は全件で評価が完了した。
この有限検証は、任意の文法・入力に対する言語保存の証明を代替しない。

## 残る比較

一方向の包含は閉じた。目標全体を閉じるには、Par から Seq への同じ元文字列上の
翻訳、または Par で認識できて Seq のどの文法でも認識できない言語が必要である。
今回の翻訳は、補助規則を元入力の先頭で実行して接頭辞値を何度でも渡せる Par の
性質を使う。同じコードを Seq で実行すると、実引数の捕捉が入力を進めるため、
同じ不変条件にはならない。

単純な引数の段階化には、既に捕捉した値を補助規則へ渡すと再照合が起きる問題がある。
この局所変換の難しさだけから、言語クラスの非包含は結論できない。
また両戦略の P 上界から P との一致を結論することもできない。

`CBV/SequentialCaptures.lean` では、この制約を任意の成功した引数導出について
証明した。`partition` は、捕捉文字列の列 `words` に対して
`input = words.flatten ++ final` を与える。`length_accounting` は捕捉長の総和と
消費長の一致、`stationary` は `final = input` なら全捕捉値が空であること、
`strict_progress` は非空の捕捉値があれば呼び出し本体への移行で入力長が真に減ることを示す。
引数式が内部で先読みや再帰を使っていても成立し、停止性は仮定しない。

`forward_iff` は捕捉済みのリテラル列を直接渡し直す場合の必要十分条件である。
成功するのは、その連結文字列が現在位置の接頭辞として再び現れる場合に限られ、
本体はその接頭辞の直後から始まる。空でない値を保ったまま同じ位置へ渡す
Par の呼び出し規約を、Seq の引数式だけ変えて実現する方法は排除される。
ただし、別の値表現・継続の配置・文法全体の変換は排除されない。

### 先頭の再照合と引数消費の融合

`CBV/ReplayFusion.lean` は、捕捉値を失わず評価位置の差を吸収できる一つの形を示す。
全規則が一引数で `F(x) ← x B` という形の Par 文法を、規則ごとに
`F(x) ← B` へ変えた Seq 文法と比較する。開始式も入力も変えない。
`B` は任意の一階式で、捕捉値 `x` の再利用、再帰、否定、反復を含められる。
Par で引数が接頭辞 `w` を捕捉すると、規則先頭の `x` がその `w` を消費する。
Seq では引数評価自身が同じ `w` を消費するので、両方とも同じ捕捉値を持ち、
同じ残余入力で `B` に入る。

`parGrammar tails` と `seqGrammar tails` は入力に依存しない実際の有限文法である。
`evaluator_eq` は全ての表近似の段数で部分的な結果の一致を示し、
`observations_iff` は全ての元の文字列・全ての残余入力・有限失敗の観測を保存する。
未定義の保存も従い、停止性の仮定はない。`recognizes_iff` が全消費の言語保存である。
これはこの規則形に対する逆変換であり、任意の Par 文法に対する逆包含ではない。
一般化には、先頭で捕捉値を再照合しない本体、および複数の独立した引数を扱う必要がある。
元の規則へ単に再照合を付け足す操作は言語を変えるため、一般的な正規化としては使えない。

### 二つの共通始点の捕捉を、二つの区間で保持する

`CBV/PrefixPairFusion.lean` は複数の捕捉値の保持と開始位置の調整を同時に扱う。
テンプレートの呼び出し `F(A,B)` を、Par 側では `F(A,A B)`、
Seq 側では `F(A,B)` と解釈する。Par 側の二つの値が `u` と `u ++ v` なら、
Seq 側は互いに隣り合う区間 `u` と `v` を捕捉する。
テンプレートの第1パラメータ参照は、Seq 側で第0と第1のパラメータの逐次合成へ置き換える。
第0パラメータと合わせて、両方の元の値を後続の任意の箇所で再利用できる。

全規則を二引数とし、Par 側の本体は第1パラメータを先頭で再照合してから
変換したテンプレート本体へ進む。Seq 側は再照合を省く。
これにより、両本体は同じ残余入力から同じ値を表す環境で評価される。
呼び出し引数自身にパラメータ参照や再帰がある場合も含め、実際の固定有限文法と
開始式の生成器 `parGrammar`、`seqGrammar`、`render` について証明した。
テンプレートの二引数以外の呼び出しと高階構文は、両生成器で明示的な失敗に写す。

`parameters_eq` は区間表現による値参照の一致、`tables_shifted` は全段数の
規則表の対応、`evaluator_eq` は全ての部分的結果の一致である。
`observations_iff` と `recognizes_iff` は、空入力・任意の文字・有限失敗・未定義を含み、
元文字列上の観測と全消費の言語を保つ。捕捉値の長さに上限を設けない。
ただし、この生成器は任意の独立した二引数を自動的に分解するものではない。
一般化には、任意の引数対をこのように前半と残りへ分ける手続きと、
先頭再照合しない本体の処理が依然として必要である。

原設計の両方式とタグ照合の例は、
[2019年の原記事](https://kmizu.hatenablog.com/entry/2019/10/24/145039) を参照。
