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

通常の二文字アルファベット `a/b` 上では、同じ入力表現の機械上界と下界を接続し、
`一階 Seq_bin ⊆ 一階 Par_bin = P` を証明した。二文字版の逆包含は、Seq が P 全体を
認識するかという問いと同値である。原文字列上の一般の逆包含・真包含はまだ未解決。

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

### 捕捉文字列だけを持つ残余解析の限界

`CBV/CaptureObservability.lean` の `observations_iff` は、任意の一階 CBV 文法と
任意の後続式についての同値性である。二つの捕捉環境が、現在の入力の全ての接尾辞で
同じリテラル照合結果を返すなら、後続式は両環境を区別できない。
`dead_environment` は、先のどの位置でも再照合できない値だけからなる環境が、
未束縛の環境と同じ照合結果になることを示す。`evaluator_eq` が全ての表近似で
一致を保証するため、再帰・有限失敗・未定義を含む。

これにより、捕捉文字列だけを渡して引数の残りを解析する一般的な分解法は排除できる。
`A = .`、`B = 'a' . / 'b'` とすると、`A` が先頭を消費した後の入力は
`ac` と `bc` のどちらでも `c` になる。しかし `B` の残りは、前者では `c` を消費し、
後者では空消費でなければならない。先頭の捕捉値 `a` と `b` は残りの `c` の
どの位置でも照合できないので、捕捉値だけを受け取る固定の後続式では区別できない。
`no_literal_residual` は、どの一階 CBV 文法・どの一階の後続式でもこの二つの
結果を実現できないことを証明する。
例の `B` 自体は通常の PEG 式なので、これは言語の認識不可能性を示す例ではない。

これは特定の残余解析インターフェースの不可能性である。接頭辞を読む時点で
制御を分岐する方法や、別の値表現を渡す方法は排除していないため、言語クラスの
分離は従わない。この形式の逆変換を一般化するなら、捕捉値以外のどの情報を
持ち越すかが課題となる。また、目標は全消費の言語保存なので、残余入力の一致を
要求しない別の変換も候補となる。

`CBV/FiniteResidualControl.lean` は、接頭辞だけから選ぶ有限制御を足した場合も扱う。
`consumePrefix = 'a'* 'b'` は `a^n b c^m` から `a^n b` を消費し、残りを `c^m` にする。
元の零引数規則 `B ← 'a' B 'c' / 'b'` は、この入力族を全消費することと `n = m`
が同値である（`balanced_recognizes`）。これは Par・Seq のどちらでも成立する。

ところが、任意の固定有限数 `K` の後続式、任意の固定一階 CBV 文法、任意の
状態選択 `state : Nat → Fin K` を使っても、捕捉値 `a^n b` と `state n` だけを渡して
残りの `c^m` 上でこの受理条件を再現することはできない（`no_finite_summary`）。
状態選択に計算可能性の制限はないが、接頭辞の `n` だけで選ぶものとし、`m` には依存しない。
全捕捉値が `c^m` 上で照合不能なので、同じ状態を選んだ二つの異なる `n` を後続式で
区別できない。これは状態選択に無限集合から有限集合への単射を要求してしまう。

`no_balanced_factorization` は実際の元の文法の受理へ接続し、残余入力の完全一致を
捨てて全消費の受理だけを保つ場合にも、このインターフェースが不十分であることを示す。
ただし、入力接頭辞に依存する未処理の呼び出しスタック、別の値表現、先読みで残りも
調べてから選ぶ制御は、このインターフェースに含めていない。
例の零引数文法自身が Seq でも動くため、言語クラスの分離は示していない。
一般化の候補は、有限状態へ畳むのではなく、入力を消費する間の継続を保持する方法となる。

### Seq の表近似の線形時計

`CBV/SequentialClock.lean` は限定した規則形を仮定せず、Seq 全体の依存構造を扱う。
`arguments_metadata` は、成功した実引数評価の最終位置が開始位置を越えず、
同じ位置で終わるなら全捕捉値が空であることを表評価器について示す。
`expression_agree` は、現在位置より小さい残余長の全環境の表と、現在位置の
全空環境の表が一致すれば、任意の式の部分的結果も一致することを示す。
失敗・否定・反復・引数内の再帰も含む。

各位置にある全空環境の行は規則ごとに一つだけなので、規則数個の定義済みセルを
数えることで局所的な安定化を証明する。これを残余長について帰納すると、
`position_stable` により、位置 `p` の全ての正しいアリティの環境は
`(g.rules.length + 1) * (p + 1)` 段以降で安定する。
捕捉値の内容や長さ、最大アリティには依存しない。

`finite_eval_iff` は、任意の有限段で得られる結果が、入力長 `n` に対する
`(g.rules.length + 1) * (n + 1)` 段ですでに得られることを示す。
`decide` はこの時計を実際に用いる決定手続きで、`decide_iff` と `decide_none_iff`
が一階 Seq の全観測・有限失敗・未定義を元の文字列上で保存する。
空入力も含み、停止性の仮定はない。

これは **表近似の更新回数** の線形上界であり、実行時間の線形上界ではない。
一段で計算する表の環境数はアリティに依存して増える。
空間計算量の改善や Par との言語クラスの分離は、この定理だけからは主張しない。

### 表を保持せず、捕捉区間だけを持つ Seq 評価器

`CBV/SequentialRecompute.lean` は、表の行を生成せず、必要な規則・環境・位置の
一点だけを再計算する実際の評価器である。`query` は規則本体へ入るたびに時計を
一つ減らす。`query_eq` と `eval_at_clock` は、全ての時計段数で既存の表近似と
部分的結果が一致することを示す。`run` は線形時計で開始する。

`CBV/SequentialSpanRecompute.lean` は、捕捉環境を元入力の二つの端点の列で持つ。
実引数評価では端点の対だけを追加し、パラメータ照合は `matchCount` で元入力の
接尾辞をたどって比較する。捕捉文字列や部分文字列辞書を生成して環境に保持しない。
`decodeEnv` と `pre` はこの表現の正しさを述べる仕様に使うが、パラメータ照合の
実行コードは `pre` で文字列を取り出さない。

`arguments_valid` は、成功した実引数評価が一引数につき一対の端点だけを生成し、
各端点と最終位置が入力長以下であることを保証する。
`query_eq`、`run_eq`、`observation_iff`、`observation_none_iff`、`run_accepts_iff` が
実際の区間版評価器から一階 Seq の全観測・有限失敗・未定義・全消費受理へ接続する。
空入力・任意文字・任意の再帰を含み、停止性や捕捉長の制限を置かない。

ここまでで、表全体を保持することは意味論上必須ではなくなった。
ただし、評価中の呼び出しスタック、静的式の参照、入力カーソルの符号化まで含む
機械の空間上界はまだ証明していない。環境の端点の上界だけから、空間計算量や
Par との言語クラスの関係を結論しない。

### 明示的な継続機械と線形フレーム数

`CBV/SequentialStack.lean` は、区間版評価器を式・実引数列・規則照会・結果返却の
タスクと、逐次合成・選択・否定・反復・引数段階・呼び出しの継続フレームへ移す。
`step` は再帰評価器を呼ばず、一つのタスクを進める決定的な遷移関数である。
原子式は入力の照合を行い、反復の次の周回では直前の反復フレームを置き換える。

`initial_runs` は、任意の文法・開始式・入力について、区間版評価器と同じ結果への
有限の実遷移列が存在することを示す。`result_iff` は遷移の決定性と合わせて
異なる停止結果を排除する。実行関数 `drive` に対しても `drive_result_iff` と
`drive_accepts_iff` が対応し、元文字列上の全消費の受理まで接続する。
`drive` 自身の燃料切れと、停止して返す「元の評価は未定義」という値は区別する。

`CBV/SequentialStackRank.lean` は、実行時に格納しない順位の証人を使い、実際の
`step` に対する不変条件を証明する。`stack_linear_bound` は、途中の全到達状態で
フレーム数が次以下であることを示す。

```
((g.rules.length + 1) * codeBudget g) * (x.length + 1) + sizeOf start
```

`codeBudget g = 1 + Σ rule ∈ g.rules, sizeOf rule.body` は固定文法だけの定数である。
これは終点だけの評価ではなく、途中に保持するスタックに対する上界である。
ただし、数値のビット長まで含む符号化サイズの上界はまだ証明していない。
線形フレーム数を、そのまま機械の線形空間と読み替えない。
原子照合をチューリング機械で実装する際の作業域の上界も、別途接続が必要である。

### 全到達状態の環境幅・数値上界・静的コード

`CBV/SequentialStackPayload.lean` は、期待される結果を式の結果と `k` 個の実引数の
結果に分けて、実際の継続の型を追う。`argHead` は残りの引数列の長さに一つ加えた
個数を返し、`argCons` は個数を一つ増やし、`call` は規則の正しいアリティを要求する。
これは実行時に追加する型検査ではなく、既存の `step` の不変条件である。

`step_typed` と `reachable_typed` から、`reachable_payload_bounds` は全到達状態で、
各タスク・各フレームの捕捉環境の長さが `arityBudget g` 以下であることを示す。
`arityBudget` は全規則のアリティの和で、固定文法だけの定数である。
全ての端点と位置・成功結果の残余長は入力長以下で、時計は初期の線形時計以下に保たれる。
途中の実引数の結果と `argCons` の保持区間もこの上界に含む。

`reachable_capture_bound` は、各フレームへ保存した環境を共有せずに全て数えても、
タスクとスタック全体に残る区間の対の総数が次以下であることを示す。

```
(initialCap g x start + 1) * arityBudget g
```

固定した文法と開始式では、これは入力長について線形となる。
`CBV/SequentialStackCode.lean` の `reachable_code` は、全タスク・全フレームの式や
引数列の `sizeOf` が `codeBudget g + sizeOf start` 以下であり、規則照会の番号が
規則数未満であることも示す。コード部分を入力ごとに大きくする必要はない。

ここまでの結果は、実際の全到達状態の各フィールドと、保持する区間数の上界である。
二進符号化とその復号、遷移実装中の作業域まで含む空間定理は依然として未証明であり、
Par と Seq の言語クラスの一致・真包含も、この結果だけからは結論しない。

### 到達状態の自然数列への符号化と復号

`CBV/SequentialStackPool.lean` の `reachable_ok` は、途中の全タスク・全フレームの
式が、固定した文法と開始式から作る有限の構文プールに属することを示す。
`CBV/SequentialStackCodec.lean` は式をこのプールの番号で表し、タスク・環境・
継続スタックを自然数列へ符号化する。`reachable_roundtrip` は、全到達状態で
実際の符号化を復号すると元の状態がそのまま戻ることを保証する。

`CBV/SequentialStackCodecBound.lean` の `reachable_length` は、この自然数列の長さが
`(initialCap g x start + 1) * (7 + 3 * arityBudget g)` 以下であることを示す。
`reachable_numbers` は、タグ・長さヘッダ・構文番号・全数値フィールドを含めた
各要素が `numberBound g x start` 以下であることを示す。
固定文法・開始式では、列長と各要素の上界はともに入力長について線形である。
これは自然数セルによる可逆な符号化の定理であり、二進列への実装と復号、
遷移中の作業域を含むチューリング機械の空間定理はまだ証明していない。
Par と Seq の言語クラスの一致・真包含も未解決のままである。

### 二進符号化と全到達状態のビット上界

`CBV/SequentialStackBinary.lean` は自然数を固定幅・下位ビット先頭の二進列で表し、
列長から語数を計算して復号する。`unpack_pack` は各数が幅に収まれば完全に戻ることを
示す。幅ゼロと不完全な語は復号時に拒否する。

`width g x start = log₂(numberBound g x start) + 1` とすると、`reachable_roundtrip` は
全到達状態が二進列から元どおりに復元できることを保証する。`reachable_bit_bound` は、
文法と開始式だけに依存する定数 `C = cellCoefficient g start` と
`K = numberCoefficient g start` により、実際の符号列長が次以下であることを示す。

```
C * (n + 1) * (log₂(n + 1) + log₂(K) + 2)
```

これは全ての数値・タグ・長さヘッダ・静的式番号を数えた `O(n log(n+2))` の
**状態符号列サイズ** 上界で、空入力も含む。幅と上界の定数は証明用の定義であり、
状態の隠れた追加フィールドではない。符号化・復号・`stepBits` 自体は、明示的な幅を
引数として取る計算可能な関数である。
`stepBits_correct` は符号列上の実際の一遷移が元の `step` と一致することを示し、
`stepBits_bound` はその出力も同じビット上界に収まることを示す。

ここまでで状態の二進符号化と復号は接続したが、復号・遷移・再符号化中に使う
作業域のチューリング機械上界は未証明である。また、この状態サイズの上界だけから
Par の非包含を導く定理もない。一般の逆翻訳と真包含の問いは引き続き未解決である。

### 継続の一語だけを読む実行と途中の作業域

`Complexity/BinaryWord.lean` の `readP` は、元の二進スタックから単進カウンタで
指定した幅だけ取り出し、その一語だけを単進の局所レジスタへ復号する実際の
リストプログラムである。取り出しは残りの列に触れず、復号は上位ビットから
`acc := 2*acc + bit` を実行する。算術用の作業レジスタは空に戻る。

`take_runs`、`horner_runs`、`read_runs` は、実行の全途中状態で `LenOK B` を保つ。
初期レジスタが `B` に収まり、一語の値が `v` で `3*v+4 ≤ B` なら十分であり、
残りの二進列を単進の自然数列へ展開する必要はない。
`CBV/SequentialWordRead.lean` の `read_word_runs` は、既存の固定幅符号
`word width v` について正しい値 `v` が得られることを接続する。
`read_word_tape` はさらに、コンパイルしたテーププログラムの走査・コピーの
途中も含めた `TFits B` を保証する。これは意味関数だけの復号結果ではなく、
実際のプログラム実行の空間不変条件である。

### 固定幅の書き戻しと一語の往復実行

`Complexity/BinaryWordWrite.lean` の `halfP` は局所の単進値を二つずつ消費し、
商と余りを返す。`digitP` は余りの一ビットを出力して値を商へ置き換え、
`emitP` は指定幅だけこれを繰り返す。`writeP` は出力の向きをそろえて、
保持していた継続の先頭へ一語を追加する。上位のゼロも含め、正確に指定幅を使う。
`half_runs`、`digit_runs`、`emit_runs`、`write_runs` は全途中状態の `LenOK` を保証する。
`write_runs` の終了時には、局所の値・商・余り・幅カウンタ・一時ビット列の
各レジスタが空に戻る。
必要な容量は初期状態、一語の値 `v` に対する `v+3`、出力列長に対する容量であり、
保持していた二進列の各数を単進へ展開することはない。

`CBV/SequentialWordWrite.lean` の `write_word_runs` と `write_word_tape` は、
出力が既存の `word width v` と一致すること、およびテーププログラムの走査・コピー
途中も含む容量上界を接続する。`SequentialWordCycle.lean` の `cycle_runs` と
`cycle_tape` は、9本のレジスタ／テープで、読み出し、永久幅レジスタからの
消費用カウンタの復元、書き戻しを実際に順に実行する。
元の一語と任意の残りの列が完全に戻り、消費用カウンタだけが空になる。

`field_cycle_runs` と `field_cycle_tape` は、任意の到達状態の任意の数値フィールドに
この局所処理を適用できることを証明する。ただし、そのフィールドから始まる符号列を
局所処理へ渡す前提であり、先行フィールドの走査・保持はこの定理の実装に含まない。
容量 `fieldSpace` は元の状態のビット列長に `3*numberBound+4` を加えたもの。
`fieldSpace_bound` により、これは前節のビット上界と入力長に比例する追加領域の和で
抑えられる。局所の一語を読み書きするために状態全体を復号する必要はない。

有限個の局所フィールドを使う各遷移、入力上の区間照合、初期化・停止・受理まで
接続した Seq 機械全体の空間定理はまだない。その空間定理から言語クラスの
非包含が自動的に従うともしていない。

### 全遷移の局所化と、先頭部分を読むテープ実行

`CBV/SequentialFront.lean` の `step_front` は、**全ての** Seq 遷移が、現在のタスクと
最上位フレームだけで決まることを示す。`front` はこの部分、`tail` は残りの継続で、
局所遷移の結果へ `tail` を付け直すと元の遷移に完全に一致する。
停止・型の合わない状態の `none` も含む。局所遷移の出力フレームは最大二つである。

`prefixCode` はタスク、継続全体の長さヘッダ、局所フレームだけを書き、
`suffixCode` は残りのフレームの符号をヘッダなしで連結する。
`encoded_step` は、元の一遷移が `prefixCode` だけの書き換えとなり、同じ
`suffixCode` をそのまま保持できることを示す。到達状態について、入力側の先頭は
`13+6*A` 語以下、出力側は `19+9*A` 語以下である。ここで `A = arityBudget g` は
固定文法だけで決まる。引数の捕捉・返却を含む一般の遷移が対象である。

`CBV/SequentialFrontRead.lean` の `readFront` は、一語のリーダーを繰り返す実際の
リストプログラムである。読み出した数だけを局所の単進フィールド列へ移し、
幅カウンタと再利用する作業レジスタを毎回復元する。残りの二進列には触れない。
`read_runs` と `read_tape` は任意の有限フィールド列について、全途中状態の容量と
正しい出力を保証する。`reachable_read_runs` と `reachable_read_tape` が、実際の
到達状態のタスク・継続長・最上位フレームへ接続する。

この局所列は最大 `13+6*A` 個の数を持ち、各数は `numberBound` 以下である。
したがって、`frontSpace` は元の状態のビット列長に
`(17+6*A)*(numberBound+1)+8` を加えれば十分である。`frontSpace_bound` は、
入力長に比例する追加領域と既存の二進符号長の上界でこれを抑える。

**このリーダーには、読む先頭部分の語数を正しく設定したカウンタを渡している。**
この前提を使わずにタグや環境の長さで進む実際のパーサは、次節で接続した。
また `step_front` は元の意味遷移の局所化であり、その全演算をテーププログラムへ
コンパイルした定理ではない。各演算、書き戻しまでをつないだ一遷移、
入力照合と機械全体の初期化・受理が残る。

### 語数を外から渡さない、タグとヘッダによる局所パーサ

`CBV/SequentialFieldFetch.lean` の `fetch` は一語を読み、局所列へその値を保存しながら、
分岐・回数制御用のレジスタにも単進値を残す。前の値の消去、幅カウンタの復元、
読み出し、局所列へのコピーを全て実際に実行する。`fetch_runs`、`repeat_fetch_runs`、
`counted_fetch_runs` は、全途中状態の容量と正しい出力を保証する。最後の処理は、
長さヘッダの回数だけ一語または二語ずつ読み、制御カウンタを空へ戻す。

`CBV/SequentialFrontScan.lean` は、タスク・値・結果・フレームの全タグを扱う
固定の制御プラン `parser` と、実際のリストプログラム `parserProgram` を定義する。
環境のヘッダなら二語ずつ、式の列なら一語ずつ進み、継続長がゼロならフレームを
読まず、正なら最上位フレーム一つだけを読む。`parser_correct` と `splitFront_correct` は、
元の符号から計算した停止位置が、ちょうど前節の `prefixCode` の終わりになることを
任意の構成について保証する。合計語数を引数に取らず、`Config` の中身を見る処理もない。

このフィールド列上の証明だけで実機を主張せず、`SequentialFrontScanMachine.lean` の
`eval_trace` と `compile_trace` でプランから実際の `LProg` 実行まで接続する。
正のタグ分岐では保存済みの単進値を一つ減らし、回数制御では長さヘッダをカウンタへ
コピーする。語の取得には上記の検証済み `fetch` を使い、未実装の読み取り命令や
遷移を仮定しない。

`reachable_parser_runs` と `reachable_parser_tape` は、任意の到達状態の二進符号から、
タスク・継続長・最上位フレームの全フィールドを読み、残りの継続を二進のまま保つ
実行を保証する。初期の制御カウンタは空で、**先頭部分の語数を渡す前提はない**。
幅のレジスタは与えており、VM 初期化の証明は別に残る。
テープの走査・コピー途中も含め、前節の `frontSpace` の容量に収まる。
局所の意味演算と書き戻しをつなぐ一遷移全体、区間照合、
機械全体の初期化・停止・受理はまだ接続していない。

### 局所フィールド列全体の書き戻しと、実機での往復

`CBV/SequentialFrontWrite.lean` は、パーサと同じ11本のレジスタを使って、
局所の単進フィールド列を元の固定幅二進形式へ戻す。最後のフィールドから
末尾の `1` を局所値へ移し、区切りの `2` を除き、幅を復元して一語を書き出す。
語を残りの継続の先頭へ置くので、逆順に処理したフィールドは元の順序へ戻る。
初期の分岐用レジスタの値は消去し、各語の処理後には作業レジスタを空へ戻す。

`write_runs` と `write_tape` は、任意の有限フィールド列について、値が幅に収まること、
初期の容量、各値 `v+3` と完成後の二進列長の容量を前提に、実際の出力と
全途中の `LenOK`／`TFits` を保証する。書く語数を外から渡すことはなく、
局所フィールド列が空になったところで止まる。

`SequentialFrontRoundtrip.lean` の `roundtrip_runs` と `roundtrip_tape` は、
タグ・長さヘッダ駆動のパーサとこの書き戻しを実際に続けて実行する。
任意の到達状態で、元の二進符号と全ての作業レジスタが元に戻り、
保存していた継続の残りにも変更がない。前節と同じ `frontSpace` で、
テープの走査・コピー途中まで収まる。

`write_attach` は、更新後の局所結果のフィールド列が既に作られている場合の
書き戻しインターフェースである。その列を同じ継続の残りへつなぐと、
`encode (attach tail localNext)` に正確に戻ることを示す。
出力列長と局所データの容量条件は明示的に前提としている。
この定理は `step` の局所演算を実行するものではなく、往復実行も状態を更新しない。
次節で否定先読みからの返却を一遷移として接続した。それ以外の局所演算と
入力照合、VM 初期化と受理は残る。

### 状態を変える一遷移：否定先読みからの返却

`CBV/SequentialNotReturn.lean` は、タスクが式の結果、最上位フレームが `notP p` の
場合の局所数値プログラムを実装する。未定義は未定義へ、失敗は保存していた位置 `p` の
成功へ、成功は失敗へ変える。同時に最上位フレームを取り除き、継続長を一つ減らす。
`numeric_runs` は、三つの結果を**同じプログラム**が正しく処理することを示す。
数値スタック機械上のステップ数は50以下であり、`p` や位置、継続長の大きさに依存しない。
これは数値プリミティブを展開した後のテープ機械が定数時間だという意味ではない。

この固定回数に既存の `nexec_space` と `nexec_compile` を適用すると、数値の上界を
`N` として、局所のコンパイル済み処理は `scratchSpace N = 57*N+2559` の容量で足りる。
値の回数だけ反復する処理へ同じ評価を適用しているのではない。
`Complexity/ListRename.lean` の `rename_frame` は、コンパイルした局所処理を11本の
レジスタの一部へ配置し、他のレジスタを保持する。これにより二進の継続や永久幅を
局所数値スタックの符号へ変換する必要はない。`local_runs` が、元の局所フィールド列から
正しい更新後の列を実際に計算することと、全途中の容量を保証する。

`SequentialNotReturnMachine.lean` の `transition_runs` と `transition_tape` は、
パーサ、局所演算、書き戻しを続けて実行する。任意の到達可能な
`⟨value (expr result), notP p :: K⟩` の元の二進符号から、実際の `SequentialStack.step` の
次状態の二進符号までつながる。更新後の列やシミュレーションの正しさを前提にせず、
三つの結果、任意の残りの継続 `K`、継続長の更新を含む。
全途中の `TFits` は `frontSpace + scratchSpace N` で保証し、`space_bound` は
既存の状態ビット長の上界に入力長に比例する追加領域を足した形でこれを抑える。

ここまでで完成したのは否定先読みから戻る分岐である。この分岐へ振り分ける全体制御、
他の演算の局所更新、元入力上の照合、VM 初期化・停止・受理はまだ接続していない。
Seq 全体の空間上界でも、Par/Seq の一致・非包含の証明でもない。

### 捕捉環境を保つ一遷移：連接の右側への受け渡し

`CBV/SequentialSeqReturn.lean` は、式の結果から `.seq m E b` フレームへ戻る
局所プログラムを実装する。成功位置 `q` なら、同じ捕捉環境 `E` を保持した
`.expr m E b q` へ進み、失敗・未定義ならその結果を保持してフレームを外す。
全ての場合で継続長を一つ減らす。

`numeric_runs` は、環境の符号列を任意の有限リストとして扱い、三つの結果を
同じ数値プログラムが正しく更新することを示す。成功時には環境の全フィールドを
元の順序で移し、位置・時計・右式の識別子と合わせて次のタスクを構築する。
フィールドの値の大きさを回数とするループは使わない。

到達状態の捕捉環境長は `A = arityBudget g` 以下なので、入力の局所フィールド数は
`M = 9+2*A` 以下、数値機械のステップ数は `T = 12*A+100` 以下である。
`scratchSpace_linear` により、局所作業域は次で足りる。

```
(M + T) * numberBound + (M + T*(T+1) + 2)
```

`compiled_runs` と `local_runs` は、この数値処理を局所レジスタへコンパイルし、
二進の継続、永久幅、パーサの保持値をそのまま保つ。数値機械の4本のスタックと
コンパイラ用作業域には、既存の11本のうち5本を使い、終了時に局所列以外を空へ戻す。

`SequentialLocalPipeline.lean` はパーサ・局所処理・書き戻しの共通の合成補題である。
具体的な局所処理の実行証明を受け取り、実際の `step` の次状態へ全体を接続する。
`SequentialSeqReturnMachine.transition_runs` と `transition_tape` が、上記の実装で
この局所処理の前提を満たし、任意の到達可能な捕捉環境・残りの継続での一遷移を示す。
更新後のフィールド列を外から渡さず、捕捉区間を含む環境の保持、次位置への移動、
フレーム除去、書き戻しまでを実際に実行する。
`space_bound` は、全途中のテープ状態を、既存の状態ビット長の上界と
入力長に比例する追加領域の和で抑える。

否定先読みと連接の返却は接続した。残りの演算、全体の分岐制御、元入力の照合、
初期化と受理は未接続で、Seq 全体の空間定理と元の言語クラス比較は引き続き未解決である。

### 保存位置から再開する一遷移：順序付き選択の返却

`CBV/SequentialAltReturn.lean` は、左側の結果から `.alt m E b p` フレームへ戻る
三つの場合を同じ局所数値プログラムで処理する。失敗なら、保存した位置 `p` と
同じ捕捉環境 `E` を使って右式 `b` を開始する。成功なら左側の成功位置を含む結果を
保持し、未定義なら未定義を保持する。全ての場合でフレームを除き、継続長を減らす。

`numeric_runs` は、環境の符号列を任意の有限リストとして、正しい出力と
`6*環境符号長+90` 以下の数値機械ステップ数を保証する。フィールドの数の上界を
`M=10+2*A`、数値機械の回数の上界を `T=12*A+110` とすれば、固定文法では
どちらも入力長によらない。局所作業域は次に収まる。

```
(M + T) * numberBound + (M + T*(T+1) + 2)
```

数値処理のコンパイルと局所レジスタへの配置は、`SequentialNumericBlock.lean` の
共通補題で接続する。この補題は具体的な数値機械の実行、その回数・初期フィールド数・
値の上界を受け取り、二進の継続を保った実際の `LProg` 実行を保証する。
`SequentialAltReturn.local_runs` が上記の数値プログラムからその前提を満たす。

`SequentialAltReturnMachine.transition_runs` と `transition_tape` は、任意の到達可能な
順序付き選択の返却状態について、パーサ、局所更新、書き戻しを一つの実行へつなぐ。
失敗時の保存位置への復帰と捕捉環境の保持、成功結果の保持、未定義の返却、
継続長の更新を、実際の `SequentialStack.step` の次状態まで証明する。
`space_bound` は全途中のテープ状態を、既存の状態ビット長の上界と入力長に比例する
追加領域で抑える。更新後の符号列を外から与える前提はない。

これで否定先読み・連接・順序付き選択の返却が接続した。残りの演算、
これらの処理を選択する全体制御、元入力の照合、初期化・受理が残る。
Seq 全体の機械上界と、元の Par/Seq 言語クラス比較はまだ閉じていない。

### 引数環境を組み立て、関数の問い合わせへ渡す実行

`CBV/SequentialCallReturn.lean` は、引数評価の結果から `.call m i` フレームへ
戻る処理を実装する。成功した環境 `W` と位置 `q` を `.query m i W q` へ渡し、
失敗・未定義なら対応する式の結果へ変える。規則番号・時計・継続長を
フレーム末尾から取り出し、環境の符号列を元の順序で保持する。
`SequentialCallReturnMachine.transition_runs` と `transition_tape` は、三つの結果すべてで、
パーサ、局所演算、書き戻しから実際の Seq の次状態までを接続する。
問い合わせから関数本体へ入る処理は、これとは別の遷移である。

`SequentialArgConsReturn.lean` は、既に保持している捕捉区間 `(a,b)` を、返ってきた
引数環境の先頭へ追加する。成功時には環境長のヘッダを一つ増やし、
`(a,b)::W` の順序と戻り位置 `q` を保つ。失敗・未定義ならその引数結果を保持する。
`SequentialArgConsReturnMachine.transition_runs` と `transition_tape` が、この処理も
任意の到達状態から実際の次状態まで接続する。

どちらも同じ固定の数値プログラムが三つの結果を扱う。引数環境長が `A` 以下なら、
入力フィールド数は `9+2*A` 以下、数値機械ステップ数は `12*A+100` 以下であり、
連接の返却と同じ `scratchSpace` および全途中の `TFits` の保証を使える。
問い合わせへ渡す環境や、区間を追加した後の環境を前提として与える必要はない。

`SequentialArgumentBind.bind_runs` と `bind_tape` は、この二つの実際の遷移を
続けて実行する。成功時は、捕捉区間を先頭へ追加してから、
`.query m i ((a,b)::W) q` の符号まで進む。失敗・未定義も対応する式の結果へ進む。
保存している継続の残り、引数順序、位置、規則番号、時計を含む実行の証明である。
`space_bound` は二つの返却処理の容量の和を、既存の入力長に比例する項と
状態ビット長の上界の和の二倍で抑え、全途中のテープ状態まで保証する。

引数の区間を最初に作る `argHead`、反復の返却、構文ノード・問い合わせの処理、
全体の分岐制御、入力上の照合、初期化・停止・受理は残る。
Seq 全体の空間定理や、Par/Seq の一致・真包含はまだ証明していない。

### 比較へ直接つなぐ次の候補：Par の計算表照会

状態サイズの上界だけでは、Par で認識できて Seq で認識できない言語はまだ得られない。
この上界から分離が従うとは扱わず、一般の逆翻訳と並行して、Par の下界を構成する
候補を調べる。候補は、時刻・位置を固定桁数の接頭辞カウンタで持ち、計算表の
状態・ヘッド位置・セル内容を一つ前の時刻への真偽照会で再計算する方法である。
この候補の構成と受理への接続は後節で証明した。言語クラスの分離はまだ主張しない。

`CBV/PrefixSuccessor.lean` は、そのための固定幅加算を実際の一階 Par 規則で実装する。
`succClock_spec` は基数 `n+1` でちょうど一つ増えることと桁幅・有効性、桁あふれを
保証する。`pred_succClock` は既存の減算との往復を保証する。
`successor_iff` は、加算・桁あふれ後の継続と、元入力上の全ての観測で一致する。
他のカウンタを保持し、継続が有限失敗・未定義になる場合も含む。

`CBV/PrefixTupleSearch.lean` は、固定次元 `d` の全タプル `{0,…,n}^d` を探索する
`2*d` 個の規則を生成する。`tupleRules_rules` は実際の有限ブロックの全規則位置を
検証し、`tupleRules_firstOrder` は一階性を示す。`tupleBlock_test` と
`tupleSearch_predicate` は、各候補の照会が有限に真偽を返すとき、全探索も有限に
終了し、ちょうどそのタプル集合の存在量化を返すことを保証する。
空入力・ゼロ次元・任意の文字を含み、入力の符号化やパディングは使わない。
未定義の照会を偽とみなす仮定にはしていない。

`scripts/check-par-counter-programs.lean` は、生成したタプル探索について元入力上の
文字検査と外側カウンタの保持を136例、加算の桁上がり・桁あふれ・継続への接続を
70例確認する。これは上記の任意入力の証明を代替する検証ではない。

この段階で残っていた接続は、実際の多項式時間 TM の計算表をこの真偽照会へ落とす
生成器と時刻帰納法による正しさであり、後節で閉じた。既存の `HigherOrder/Tableau/Grammar.lean` と
`Sim.lean` には、状態・ヘッド位置・セル内容の再帰照会と実際の `TM.run` との
対応がある。`Complexity/StepSem.lean` の `step_state`、`step_pos`、`step_cells`、
`or_combF` も有限状態・読み取り記号の分岐を既に扱う。
これらの TM の補題と場合分けを活かし、数値操作と入力参照を接頭辞カウンタへ
置き換えるのが次の候補である。既存の高階版は別の入力符号化を使うため、その
文法や受理定理をそのまま元入力上の Par の定理として使うことはできない。
これが得られても、Seq からの非包含または一般の Par から Seq への逆翻訳が
必要という最終目標は変わらない。

### TM 照会文法の実装と局所的な正しさ

`CBV/ParTableau/Compiler.lean` は、実際の `Complexity.TM k` と固定桁数から、
状態・ヘッド位置・セル内容・読み取り記号の照会を行う有限 Par 文法を生成する。
時刻と位置は元入力の接頭辞のタプルで表し、時刻の減算、位置の増減、
全位置タプルの探索を既存の規則ブロックへ接続する。停止後の状態・ヘッド・セルは
`Complexity.nextState`、`moveOf`、`writeSym` の吸収的な遷移を使う。
初期入力は各文字を直接読み、`'b'` を真、それ以外を偽へ写す一文字ごとの解釈で、
位置コードやパディングを入力へ加えない。

`FirstOrder.lean` は、生成文法と開始式の一階性を無条件に示す。
`Layout.lean` の `compile_at` は、全ての生成ノードの全アドレスが、生成器の
実際の規則と一致することを示す。`Routing.lean` の `timed_call_iff` は、
生成した状態・ヘッド・セル照会が、実際の減算ブロックを通って、時刻ゼロの規則か
前時刻の規則へ入ることを全観測について示す。読み取り探索の実際の配置も接続した。

`Transitions.lean` の `stateNext_test`、`headNext_test`、`cellNext_test` は、
前時刻の状態・読み取り・ヘッド・セル・位置演算の有限な照会が正しいという明示的な
前提 `Previous` のもとで、生成本体が実際の `TM.step` と一致することを示す。
これは帰納段階の局所補題であり、前時刻の全照会の正しさを仮定なしに得た定理ではない。

`Read.lean` の `compiled_read_test` は、全ての有効な位置タプルに対する
ヘッド・セル照会が正しく、ヘッドが表現範囲内にあるとき、生成した読み取り照会も
実際の記号と一致することを示す。`PrefixNumerals.lean` が、範囲内の全ての位置に
有効な固定幅表現が存在することと、全有効表現の数値上界を証明し、探索の完全性を支える。

`scripts/check-par-tableau.lean` は、生成文法を直接実行して、実際の `TM.run` の
状態・ヘッド・セル・読み取りと875例で照合した。右移動、左端での左移動、書き換え、
停止後の吸収、多テープの記号の相互参照、空入力、複数桁を含む。
この有限検証は、全時刻のシミュレーション定理を代替しない。

ここまでの局所補題だけから全体のシミュレーションを仮定せず、残っていた
初期テープ・位置演算・全時刻の帰納法・桁幅・空入力・受理の接続を次節で証明した。

### 多項式時間 TM から元文字列上の一階 Par への変換

`CBV/ParTableau/Atoms.lean` と `Initial.lean` は、桁のゼロ判定と、元入力の直接参照を
実際の `initCfg` のセルへ接続する。高位桁が非ゼロなら入力の外側の空白であり、
下位桁だけが有効な入力位置を表す。空入力・ゼロ桁も含め、一般的な正しさを示す。
`Position.lean` は、実際の加算・減算ブロックと引数の並べ替えを接続し、
桁あふれ・位置ゼロの有限失敗と、左端で止まる左移動を含む `Move.apply` を再現する。

`Sim.lean` の **`tableau_sim`** は、全ての有効な時刻タプル・位置タプルについて、
実際の生成文法の状態・ヘッド・セル照会が `TM.run` と一致することを証明する。
`good_previous` は既存の `Previous` の各前提を実際の読み取り探索と位置演算から
導出するので、全体定理にはシミュレーションや停止性の仮定は残らない。
`read_sim` も同じ全時刻の読み取り照会を保証する。

`Recognition.lean` の `start_recognizes` は、開始式の全消費受理が
時刻 `(n+1)^digits-1` の受理状態と同値であることを示す。
多項式上界 `T(n) ≤ c*(n+1)^degree` に対し、
`polynomialDigits c degree = degree+c+1` は非空入力で十分である。
`polynomialStart` は空入力だけを定数時刻 `c` の結果で分岐し、それ以外はこの十分な
時計で実行する。**`polynomial_recognizes`** は、TM が `T` 時間以内に決定する言語
`L` について、全ての元文字列 `x` で生成文法の受理が `L (inputBits x)` と一致する。
`inputBits` は一文字を一ビットへ解釈するだけで、入力の追加・反復・位置符号化は行わない。

言語クラスへの接続は `Shallot/Peg/Separation/CBVParLower.lean` にある。
`firstOrder_par_contains_P_projection` は、既存の機械ベースの `KEXP 0 L` から、
元の `List Char` 上の言語 `fun x => L (inputBits x)` が
`IsFirstOrderCBVPEL .callByValuePar` に属することを示す。
`firstOrder_par_contains_P` は通常の二文字アルファベット `'a'`/`'b'` 上の版で、
任意の P 言語を入力に依存しない一階 Par 文法で認識する。文字列はそのまま読み、
パディング・位置コードは加えない。
既存の上界で使う4ビット・トークン入力 `tokenWord` との表現の差は、次節で
一文字ずつの実際の入力機械を作って解消した。結論は通常の二文字アルファベット上の版である。

`scripts/check-par-tableau-recognition.lean` は、空入力・非空入力・Unicode 文字を含め、
生成した開始式を直接実行して受理と拒否を確認する。任意入力の根拠は上記の Lean 証明である。

**Par 側の P 下界は接続したが、Par と Seq の一致・真包含は依然として未解決。**
これを決めるには、一般の Par から Seq への同じ元文字列上の逆翻訳、または
Seq のどの文法でも認識できない Par 言語が必要である。

### 同じ二文字入力での Par = P と、比較に残る条件

`Shallot/Peg/Separation/BitWord.lean` は `bitWord w` を一ビット一文字の
通常の `a/b` 語として定義する。`BitWordInput.lean` の `readLetter_spec` と
`nruns_loadLetters` は、実際の数値スタック機械が入力ビットを一つずつ読み、
その語の文字行と正しい長さを構築することを証明する。入力を4ビット単位にまとめたり、
不完全な末尾を捨てたりしない。静的な文字コードの出力だけに既存の命令を再利用する。

`CBV/BitWordMachine.lean` は、この行を既存の辞書・全区間・表評価器へ実際に渡す。
`bitWordProgram_halts` は機械の停止と結果を、全入力の正確な費用
`160*(n+1) + 2 + setupCost n + loadedCost g e n` で保証する。
`bitWordLanguage_in_P` が Par・Seq 両方式について通常の `a/b` 入力での P 上界であり、
4ビット入力用の `encodedLanguage` とは異なる定理である。

`Shallot/Peg/Separation/CBVBinary.lean` の `IsFirstOrderBinaryCBVPEL` は、
固定の一階文法で通常の二文字語を認識する言語クラスである。
**`binary_par_iff_P`** がこのクラスと機械ベースの `KEXP 0` との一致を示す。
下界も上界も同じ `bitWord`、同じ元の語を使い、空入力も含む。

残る比較は次のように正確に切り分けられる。

- `binary_reverse_iff_seq_covers_P`：二文字版の Par から Seq への包含は、
  Seq が全ての P 言語を認識することと同値である。どちらもまだ証明していない。
- `original_reverse_requires_seq_P`：元の任意の文字列言語を保つ一般の逆翻訳があれば、
  特に二文字版で Seq が P 全体を認識する。この必要条件だけで一般の逆翻訳を得たとはしない。
- `binary_P_witness_separates_original`：二文字版の Seq クラス全体に属さない P 言語が
  一つあれば、`L(inputBits x)` により元の文字列クラスの真の非包含証人になる。
  そのような言語自体はまだ構成していない。

以上は言語クラスを揃えた比較であり、同じ文法の評価結果の差や特定の引数渡しの
失敗から非包含を結論するものではない。元の目標を閉じるには、依然として
一般の逆翻訳か、Seq の全ての文法を排除する具体的な言語証人が必要である。

関連研究では、[Uezato, ICALP 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.155)
が後方参照と先読みを持つ正規表現による NLOG の特徴付けを与える。
ただし同論文の選択は結果集合の和であり、正の先読みから変数更新が外へ残る
意味論である（§3）。この結果を Macro PEG の優先選択と局所的な捕捉へそのまま
移すことはできない。両モデル間の翻訳はここでは主張しない。

原設計の両方式とタグ照合の例は、
[2019年の原記事](https://kmizu.hatenablog.com/entry/2019/10/24/145039) を参照。

### 捕捉端点の比較と選択の途中作業域

`Complexity/NShrinkingCompare.lean` は二つの数値スタックの先頭を
同時に減らす実機プログラムを与える。第1引数は専用スタック、第2引数は
保存済みの任意の数値列の上に置ける。`exec` は全ての途中状態について
初期状態と同じ `NFits B` を保証し、実行回数を `4*a+1` 以下に抑える。
終了時、第1スタックが空であることは `b<a`、第2スタックの先頭が正で
あることは `a<b` と同値である。`compiled_runs` は同じ容量で実際の
リストプログラムへ接続する。位置に比例する実行時間から二次の作業域を
導く必要はない。

`SequentialCaptureMin.lean` は元の位置 `a,b` と任意の二つの局所ペイロードを
保存したまま、`[min a b,b]` を作り、比較用に第2引数の下へ保存した列を
復元する。容量条件は初期 `NFits B` と `2*max a b+4 ≤ B` であり、
全ての途中状態も同じ容量に収まる。これは捕捉区間の端点選択に使う部品である。
`SequentialNumericBlock.annotated_local_runs` は、このように途中作業域を
直接証明した数値実行を既存の局所テープレジスタへ組み込む入口を与える。

捕捉開始フレーム全体の書き換え、反復の帰還、残りの遷移と全体の停止・空間上界の
接続は未完成である。これらの比較部品から Par/Seq の一致や分離は結論しない。

### 捕捉開始フレームからの全帰還

`SequentialArgHeadReturn.lean` は成功した引数評価の帰還を実機で行う。
保存した位置 `p` と返された位置 `q` を比較し、捕捉区間 `(p,min q p)` を
`argCons` フレームへ保存して、残りの引数を `q` から評価する。
捕捉環境と残りの引数の符号は全てその順序を保つ。
比較には `SequentialCaptureMin` の直接の途中作業域不変条件を使い、
前後の有限個のフィールド移動だけに時間から空間への上界を適用する。

`SequentialArgHeadDispatch.lean` は入力の結果タグを読み、未定義・失敗・成功の
3通りを一つの固定プログラムで処理する。未定義・失敗では `args` の同じ結果へ
帰還してフレームを取り除き、成功では上記の捕捉フレームへ置き換える。
`NShrinkingCompare.caseTop_exec` がタグ判定の間も同じ `NFits` を保つ。
局所数値プログラムの容量は、文法の最大引数数を `A`、数値上界を `N` として
`(14+3*A)*(N+1) + grow N (18*A+120) + 2` 以下であり、固定文法では `N` の一次式である。
実行回数に位置依存の項があっても、これを追加の空間として計上しない。

`SequentialArgHeadReturnMachine.transition_runs` と `transition_tape` は、
到達可能な実際の状態から、入力駆動の読取り・タグ分岐・局所更新・書戻しを
通して `SequentialStack.step` と全く同じ次状態へ至ることを、全3ケースで示す。
外側の継続列は元の二進符号のまま保持される。`space_bound` は全ての途中の
テープに、既存の状態符号長上界と入力長の一次項の和で上界を与える。

これで捕捉開始フレームの帰還は接続した。反復、残りの構文・引数・問い合わせの
遷移、全体の制御と停止判定はまだ未完成である。Par/Seq の一致・分離についての
結論は引き続き得ていない。

### 反復の厳密な進行判定と全帰還

`Complexity/NTableLookup.lean` は固定の数値表を分岐コードへコンパイルし、
指定したスタックの先頭だけを表の値へ置換する。`SequentialStarLookup.lean` は
これを使い、反復本体の式番号から `star` 式の番号を引く。表は固定文法の
式プールだけから作り、入力依存の位置を表の大きさへ含めない。

`SequentialStarReturn.lean` は返された位置 `q` と保存位置 `p` を破壊的に比較し、
**`q < p` の場合だけ**式番号を引いて反復式の評価へ戻る。`q = p` を含め、
位置が減っていない成功は未定義を返す。内側の式が失敗した場合は保存位置 `p` で
成功し、未定義の場合はそのまま未定義を返す。捕捉環境は再開時に順序も含め保持する。
`SequentialStarDispatch.lean` はこの全ケースを一つの結果タグ分岐プログラムにまとめる。

`SequentialStarReturnMachine.transition_runs` と `transition_tape` は、到達可能な
元の状態の二進符号から `SequentialStack.step` と等しい次状態の二進符号への
実際の読取り・分岐・更新・書戻しを証明する。式プールの利用可能性は到達可能性から
導き、表の正しさを未証明のコールバックとして仮定しない。
局所容量は `M=12+2*A`, `T=12*A+3*H+100` として `M*(N+1)+grow N T+2`。
`H` は固定文法の式プール長であり、固定文法では `N` の一次式である。
比較の実行回数が位置に依存しても、その時間を空間へ変換しない。
`space_bound` は、途中の全テープを既存の状態符号長上界と入力長の一次項の和で抑える。

これで7種類の帰還フレームにはそれぞれ具体的な実機遷移がそろった。
構文からの評価開始、引数・問い合わせ・原子的照合の残りの遷移、全体の分岐・制御、
初期化・停止・受理への接続は未完成である。全体の Seq 空間上界や Par/Seq の
一致・分離をこの節では主張しない。

### 全帰還フレームの入力駆動分岐

`SequentialReturnScan.lean` は既存のフィールド読取りを、番号つきの継続を
葉に持つパーサへ拡張する。結果の種類と可変長の捕捉環境、スタック長、フレームの
タグとペイロードを実際の入力から読む。`parser_trace` は7種類の各フレームで
正しい継続番号へ到達することを示し、`compile_trace` は各読取り・分岐・
長さヘッダに従う繰返しの途中にも `LenOK` を保つ。

`SequentialReturnScanMachine.selected_runs` は読取り後に元の二進状態を
書き戻し、選択した継続へ渡す。この復元により既存の独立した帰還機械をそのまま
接続できる。処理対象のフィールド数やフレーム番号を外部から与える必要はない。

`SequentialReturnMachine.program ns` は7種類の帰還機械を含む一つの固定プログラム。
`transition_runs` と `transition_tape` は、到達可能な値タスクに先頭フレームがあり、
`step` が次状態を返す場合、その次状態と同じ二進符号へこのプログラムが進むことを
証明する。式結果の5種類と引数結果の2種類を全て既存の具体的な実行証明で接続しており、
未実装の分岐先や一般のシミュレータを仮定していない。

共通容量は5種類の既存容量の和とする。引数追加・関数帰還はシーケンス帰還と同じ
容量を使えるため、この和で7種類全てを覆う。`space_eq` はこの容量を
`5*frontSpace + C*N + D` と表し、`C,D` は文法だけから決まる。
`space_bound` は入力長の一次項と従来の状態符号長上界の5倍による明示的な上界を与える。
選択のための読取りと復元も含め、途中の全テープがこの容量に収まる。

これは非終端の**帰還遷移全体**の統合である。式・引数・問い合わせの評価開始や
原子的照合、初期化、終端での受理判定、全遷移を反復する制御の接続はまだ残る。
全体の Seq 空間上界や Par/Seq の一致・分離は引き続き未解決である。

### 引数列の評価開始と捕捉環境の保存

`Complexity/NCountedTransfer.lean` は長さヘッダで数えた固定長チャンクの転送と、
一つのスタックから二つの出力へのコピーを実機プログラムとして与える。
任意の保存済み接頭列と他レジスタを保つこと、正確な出力順序と実行回数を証明する。
`SequentialNumericFive.lean` は5本の数値スタックを既存の11本のテープへ埋め込み、
二進の継続部分・語幅・保持値を保存して、更新後に一時領域を空へ戻す。

`SequentialArgsEntry.lean` は引数列のヘッダを入力から読み、一つの固定プログラムで
空列・非空列を処理する。空列なら空の捕捉環境と同じ位置を引数結果として返す。
非空列なら最初の引数を同じ位置で評価する式タスクを作り、元の捕捉環境と残りの引数を
`argHead` フレームへ保存する。捕捉環境は式タスクとフレームの双方に同じ順序でコピーし、
外側のフレームの符号も保存する。長さヘッダとフレーム数も実際に更新する。

`SequentialArgsEntryMachine.transition_runs` と `transition_tape` は、先頭フレームの
有無を含む任意の到達可能な引数タスクで、実際の二進状態から `step` と等しい次状態へ
読取り・更新・書戻しが進むことを証明する。更新でフレームが増える場合も扱い、
既存の局所次状態長上界 `19+9*A` を使って増えた出力の書戻し容量を確保する。
数値処理は `M=13+6*A`, `T=80*A+200` に対する `M*(N+1)+grow N T+2` の容量で実行できる。
`space_eq` と `space_bound` はこの処理と増加分を含めた全途中テープに、
既存の状態符号長上界と入力長の一次項の和による明示的な上界を与える。

引数開始は接続できたが、式の構文別の評価開始、問い合わせから規則本体への遷移、
原子的照合、初期化・終端判定、全体の制御への統合は未完である。
全体の Seq 空間上界や Par/Seq の一致・分離は引き続き未解決である。

### 規則問い合わせから本体への評価開始

`SequentialRuleLookup.lean` は固定文法の規則列から本体の式番号の表を作り、
入力にある規則番号を `NTableLookup` の実機分岐でその式番号へ置換する。
`runs` は `ruleAtM` と表の一致、保存済みの接頭列と他レジスタの保存、
実行回数 `2*R+H+3` の上界を証明する。`R` は規則数、`H` は式プール長で、
どちらも固定文法から決まる。

`SequentialQueryEntry.lean` は捕捉環境の長さヘッダを読み、その全要素を順序通り保持する。
時計がゼロなら未定義の式結果へ帰還し、正なら時計を一つ減らして、入力の規則番号で
選んだ本体の式タスクを同じ位置・同じ捕捉環境で作る。一つの固定プログラムが両方を扱い、
外側のフレームと全一時領域も所定の状態へ戻す。

`SequentialQueryEntryMachine.transition_runs` と `transition_tape` は全ての到達可能な
問い合わせ状態について、実際の二進入力から `SequentialStack.step` と同じ次状態へ
読取り・更新・書戻しが進むことを示す。規則番号が範囲内であることは既存のコード不変条件、
位置が入力長以下であることは既存の型付き状態不変条件から導く。したがってこの接続では、
有効な規則や有効な位置を外部から与える追加の仮定を要しない。
任意の未到達な不正状態の処理を証明したとはしない。

局所数値容量は `M=13+6*A`, `T=60*A+3*R+H+200` に対する
`M*(N+1)+grow N T+2` である。`space_eq` と `space_bound` は途中の全テープに、
既存の状態符号長上界と入力長の一次項の和による明示的な上界を与える。
数値スタック機械での命令回数は文法サイズだけで決まる上界に収まり、表の大きさも固定される。

引数開始と問い合わせ開始は接続した。式の構文別の評価開始、原子的照合、
初期化・終端判定、全遷移を選び反復する制御はまだ残る。
Par/Seq の一致・分離と、全体の Seq 空間上界は引き続き未解決である。

### 構文別の評価開始とフレーム生成

`SequentialFrameBuild.lean` は4種類の継続フレームを数値スタック機械で作る。
シーケンスは時計・右側の式・環境を保存し、選択と反復は保存位置も持つ。
否定先読みは保存位置を持つ。`runs` は出力順序と外側のフィールド列の保存、
一時スタックが空に戻ること、数値命令回数の上界を全4種類について証明する。

`SequentialStructuralEntry.lean` は実際の入力から式番号を取り出し、固定の式プールに
対応する分岐コードで `seq`・`alt`・`notP`・`star` を選ぶ。プログラムには
構文の種類や子式の番号を外から与えない。子式の番号は選択された元の式から決まり、
最初の子を同じ時計・同じ位置・同じ捕捉環境で評価する式タスクを作る。
環境の長さヘッダを読み、環境をタスクと必要なフレームへ順序通りコピーして、
フレーム総数を一つ増やし、元の外側フレームを保存する。

`SequentialStructuralEntryMachine.transition_runs` と `transition_tape` は、この4構文の
到達可能な状態から、`SequentialStack.step` と等しい次状態の二進符号へ進むことを示す。
式プール内の分岐が選択できることは到達可能性の利用可能性不変条件から導く。
定理の構文パラメータは入力状態の記述であり、実行プログラム自身は式プールだけから
決まる。先頭フレームの有無を含む任意の外側継続を扱い、局所出力が2フレームになる
場合の書戻し容量も確保する。

局所数値容量は `M=13+6*A`, `T=80*A+8*H+250` に対する
`M*(N+1)+grow N T+2`。`space_eq` と `space_bound` はパーサと増加した出力の
書戻しを含む途中の全テープに、従来の状態符号長上界と入力長の一次項の和による
明示的な上界を与える。数値命令回数の上界は文法サイズだけから決まる。

構文別開始のうち、関数呼出しの開始と原子的照合はまだ残る。
初期化・終端判定・全遷移を選び反復する制御も未完であり、全体の Seq 空間上界や
Par/Seq の一致・分離は引き続き未解決である。

### 関数呼出し開始の規則・引数個数検査

`Complexity/NPushFields.lean` は固定のフィールド列を具体的な定数プッシュ列へ
コンパイルし、出力の順序・他レジスタの保存と命令回数上界を証明する。
`SequentialCallEntry.lean` は入力の式番号から元の `call i es` を選び、固定文法で
規則が存在して引数個数も一致する場合にだけ引数評価を開始する。規則の存在と個数は
固定の元の式・文法から決まるため、式ごとの分岐コードへ組み込む。

有効な呼出しでは、元の時計・位置・捕捉環境を引数タスクへ渡し、長さヘッダを含む
元の引数式列を出力する。呼出しフレームには時計と規則番号を保存し、フレーム総数を
一つ増やして外側の継続を保持する。規則なし・引数個数不一致では式の失敗を返し、
フレーム総数と外側の継続を保つ。元の捕捉環境は全要素を順序通り読み、必要な出力へ
コピーする。全ケースで一時領域は所定の空状態へ戻る。

`SequentialCallEntryMachine.transition_runs` と `transition_tape` は全ての到達可能な
呼出し状態について、二進入力から `SequentialStack.step` と同じ次状態への
読取り・式番号分岐・更新・書戻しを証明する。有効な呼出しだけを仮定することはなく、
不正な規則参照と個数不一致の経路もこの定理に含む。

`A` を文法の最大引数数の上界、`R` を規則数、`H` を式プール長とし、
`P=(A+1)*(A+H+2)+2` と置く。引数フィールドの出力を含む局所命令回数は
`T=80*A+2*R+2*P+8*H+250` 以下、初期セル数は `M=13+6*A` 以下で、
局所数値容量は `M*(N+1)+grow N T+2` である。有効な呼出しの引数個数が `A` 以下に
なることは規則と個数の一致から証明し、無効な呼出しでは引数列を出力しない。
`space_eq` と `space_bound` は出力フレーム増加とパーサ・書戻しも含め、
途中の全テープを既存の状態符号長上界と入力長の一次項の和で抑える。

これで構文側の呼出し開始まで接続した。原子的照合、初期化・終端判定、各開始・帰還を
選び反復する全体制御はまだ未完である。Par/Seq の一致・分離と全体の Seq 空間上界は
引き続き未解決である。

### 元入力を復元する文字参照

`Complexity/NBoundedTransfer.lean` は、数値フィールドを一つずつ転送する途中の
`NFits B` を直接証明する。ヘッダで指定した個数を転送する `counted_runs` では、
転送前と転送後の状態が同じ容量に収まれば、途中も同じ容量に収まる。
転送元は小さくなり、転送先は最終列の接頭列として増え、カウンタは減る。
このため、入力長に比例する走査回数を空間の増加へ変換する必要がない。

`SequentialInputRead.lean` は元入力の文字コード列を別の数値スタックに保持し、
残り位置 `p` の先頭文字を読む具体的な5スタックプログラムを与える。
`p>0` なら末尾から `p-1` 文字を一時領域へ移して対象を読み、同じ個数を戻す。
`p=0` なら末尾を示す `0` を返す。原入力用スタックを完全に復元し、一時スタックと
カウンタを空へ戻して、結果コード一つを出力する。`read_runs` は任意の元の
`List Char` と有効な位置に対して `sfx x p` の先頭文字との一致を証明する。
数値機械の命令回数は `8*p+10` 以下である。

文字コードは `Char.toNat+1` とし、`code_injective` が異なる文字の区別を、
`result_zero_iff` が結果 `0` と末尾位置の同値を保証する。空入力・末尾も含み、
二文字アルファベットへの制限はない。`UInt32` の一般的な上界から、符号化した入力の
長さは `(2^32+1)*n` 以下となる。`compiled_runs` と `read_tape` は、
`(2^32+2)*n+3` の容量で途中の各テープが収まる実際の実行へ接続する。
この定数は粗いが、入力長について一次である。

この部品の開始状態には、既に符号化した原入力と残り位置が入っている。
原入力をこのスタックへ読み込む初期化、原子的照合と捕捉区間比較の全処理、
既存の状態更新機械とのレジスタ統合はまだ残る。全体の Seq 空間上界と
Par/Seq の一致・分離は引き続き未解決である。

### Restoring two-cursor character comparison

`Complexity.NRename` now injects numeric subprograms into a larger fixed register
set. `NExec.rename_frame` preserves the exact step count and `NFits B` capacity
at every intermediate state; registers outside the injection retain their
ambient values. This lets the original-input reader coexist with capture
cursors, counters, and a previously read character, without deriving extra
space from the input-dependent traversal time.

`SequentialInputPair` reads at two valid suffix positions of the same original
`List Char`, retaining the two codes in distinct registers. Both traversals
restore the original encoded input. The seven-register numeric program then
uses the shrinking comparator; the two comparison registers are zero exactly
when the original character codes agree. `compiled_compare` and `compare_tape`
verify this execution through list programs and the eight-tape machine. All
intermediate tapes have the same capacity `(2^32 + 2) * x.length + 3` as the
single-character reader, with no captured-substring buffer. The constant is a
coarse fixed alphabet bound, not a dependence on the grammar or input contents.

`matchCount_step` connects this actual comparison result to the next-character
guard of the existing capture matcher. For a positive remaining capture count,
it advances both suffix positions exactly when the codes agree, and fails on a
mismatch or target EOF. Character zero is still distinct from EOF. The theorem
covers arbitrary original `Char` inputs and valid numeric capture positions.

This is the inner comparison and its semantic bridge, not yet the full capture
loop. The remaining-count loop, environment-span lookup, atomic-expression
selection, original-input initialization, and whole-evaluator integration still
need connection. It does not resolve general CBV-Par versus CBV-Seq equality
or separation.

### Complete runtime capture-interval scan

`SequentialSpanMachine` now connects the inner comparison to a complete numeric
loop over a capture interval. Its ten numeric registers contain the original
encoded input, the fixed comparison workspace, two persistent suffix positions,
and the remaining count. `setup_runs` computes `a - b` from the runtime interval
endpoints by shrinking comparison. The loop copies the two positions into the
comparison registers, restores the original input after both reads, advances
both persistent positions and decrements the count on a match, and stops with an
empty count register on a mismatch. A zero count denotes success. Comparison
scratch is cleared after each iteration.

`scan_correct` proves the final success/position result equals the existing
`SequentialSpanRecompute.matchCount`. `span_value` therefore identifies the
result with `matchSpan x a b p`, for arbitrary original character inputs and
valid positions. Empty captures, target EOF, mismatches, and successful scans
are covered. The program is fixed: the capture length is runtime data, with no
input-dependent unrolling and no materialized captured substring.

`compiled_span` and `span_tape` carry the entire endpoint setup and loop through
the list compiler to eleven actual tapes. Every intermediate tape fits the
same linear capacity `(2^32 + 2) * x.length + 3`. The numeric running-time bound
is `4*b + 5 + (a-b)*(16*x.length + 4*2^32 + 31) + 1`; the list execution bound
multiplies this by `ncost` of the capacity. The final encoded original input is
preserved on register zero. The initial state already contains that encoded
input and the endpoints; environment lookup, the ordinary-input loader, atomic
selection and evaluator integration remain to be connected. The general
Par/Seq equality-or-separation objective remains open.

### Runtime parameter lookup followed by interval matching

`SequentialEnvLookup` consumes the existing `writeEnv` encoding and extracts the
pair for a fixed source parameter index `k`. It tests the runtime environment
length before each pair. An absent parameter therefore stops at the environment
boundary even when following frame fields are nonempty. After the selection it
drains the remaining counted environment, retaining the following fields in
their original order. Its numeric time is at most `8 * E.length + 10`, independent
of the values of endpoints. The grammar fixes `k` and bounds environment length
by its arity budget; this stage can use the constant-time-to-space argument
without applying it to the input-dependent interval traversal.

`SequentialParamMachine` composes that lookup with the complete span machine.
The original encoded input occupies its own register; the lookup obtains both
endpoints directly from the runtime environment. A missing parameter returns
failure. A present parameter invokes the interval loop, including empty
captures and target-EOF failure. `param_value` identifies the final result with
`SequentialStack.atom x E (.param k) p` on the same original character input.
The original encoded input and the fields following the environment survive.

`linear_param_runs`, `compiled_param`, and `param_tape` verify the combined
program through thirteen numeric registers and fourteen actual tapes. For
`E.length <= A`, at most `M` following fields, and field bound `N` covering the
input length and arity, every intermediate tape fits

```
(2^32 + 2) * x.length
  + (1 + 2*A + M + (8*A+10)) * N
  + (1 + 2*A + M + (8*A+10)*(8*A+11) + 5).
```

`capacity_linear` proves this expression equals the capacity used in the
execution theorem. For fixed grammar and a local front, `A` and `M` are
constants. The remaining work is selecting atomic expressions from the encoded
task, implementing the other atomic cases, loading ordinary input, and
integrating all transitions and terminal decisions into the evaluator. This
component still starts with the original input already encoded. The general
Par/Seq equality-or-separation question remains unresolved.

### Original-input character and literal atoms

`SequentialCodeTest` implements numeric tests for any character, one fixed
character, and a fixed inclusive character range. EOF is code zero; original
characters use `toNat + 1`. The arbitrary-character test checks positivity.
The fixed-character and range tests use shrinking comparisons with grammar
constants, including immediate failure for reversed ranges. The code tester
clears its code and comparison scratch and returns a success flag.

`SequentialCharacterMachine` copies the saved runtime position into the reader,
reads and restores the original encoded input, applies the chosen code test,
and decrements the saved position only on success. `character_value` identifies
its result with `SequentialStack.atom` for `.any`, `.chr`, and `.range` for every
original `List Char`, valid position, and capture environment. This includes EOF,
NUL, arbitrary Unicode characters, and empty or reversed ranges. The compiled
program uses eight actual tapes. `capacity_linear` gives the exact capacity
`(2^32 + 2) * n + 3 + SequentialCodeTest.capacity kind`.

The potentially long original-input traversal keeps its direct linear space
annotation. Only the character-code tester uses time-to-space conversion: its
initial code is bounded by the fixed alphabet constant `2^32`, and its time bound
depends on that constant and fixed source characters, never on the input length.
Thus that conversion contributes a fixed additive capacity.

`SequentialLiteralRead` composes fixed-character machines for a grammar literal,
clearing the success flag between stages and stopping at the first mismatch.
Its program depends only on the literal. `scan_correct` proves the exact result
of `stripPrefix?`, and `literal_value` connects it to `.lit` in the existing atom
semantics, including the empty literal and EOF. `compiled_literal` and
`literal_tape` verify the whole composition on eight tapes. All intermediate
tapes fit `(2^32 + 2) * n + 3 + reserve literal`, where `reserve` is a fixed sum
of code-tester capacities. Both character and literal machines retain the
original encoded input in register zero.

The evaluator still needs source-expression selection and task/result encoding
around these atom machines, together with the trivial non-reading atoms,
ordinary-input initialization, and the complete transition/terminal loop.
These components start with the original input already encoded. They do not
yet decide the general CBV-Par versus CBV-Seq equality-or-separation question.

### Source-ID dispatch and atom result encoding

`SequentialAtomCodec.prepare` reads the existing expression-task prefix and
separates the source expression ID, saved input position, and reversed runtime
environment plus following frame fields. It drops the unused clock for an
atomic step. `prepare_runs` proves the transformation from the ordinary
`inputFields` encoding, rather than assuming a separately supplied operator.

`select` combines that normalization with a fixed branch table generated from
`exprPool ns`. `selected_runs` proves that the runtime ID selects the matching
source expression branch. It allows a branch to use additional ambient numeric
registers, including a preserved original-input register outside the injective
normalization map. All intermediate states retain the same `NFits B` bound;
branch correctness is an explicit premise of this generic composition theorem.
The input-reading atom adapters still need to discharge that premise in one
unified layout.

`SequentialAtomCodec.finish` consumes the runtime result tag and position and
writes `[3,0] ++ writeRes result ++ [frameCount] ++ frameFields`, clearing its
work registers. The three tags represent undefined, failure, and success.
`finish_runs` handles every `Res`, and `input_prefix` / `output_prefix` identify
both formats with the evaluator's actual `prefixCode`. `original_step` links
these endpoints to the original stack transition for atomic expressions.
Normalization and assembly take time bounded by the local environment/frame
field counts, so their time-to-space conversion is linear in the numeric field
bound for a fixed grammar and local front.

`SequentialSimpleAtom` supplies complete source-selected branches for atoms
that do not read input: `eps`, `dbg`, and `lam` succeed without consumption;
`callParam` fails and `invoke` returns undefined, as in the existing semantics.
The branch consumes only the header-counted environment and retains all
following frame fields. `numeric_runs` starts from the encoded expression task,
selects by its actual source ID, executes the branch, and returns the encoded
value task. `numeric_tape` carries this entire path through six actual tapes,
with exact agreement with `SequentialStack.atom`. Its `space_linear` theorem
makes the numeric-field dependence explicit.

The separate parameter, character, and literal machines still require layout
adapters and result-tag conversion to use this common dispatch and assembly.
The ordinary-input loader and complete evaluator loop also remain unconnected.
No general Par/Seq equality or separation follows yet.

### Read results now return ordinary encoded value tasks

`SequentialAtomResult` supplies a common thirteen-register return layout for
all input-reading atoms. Register zero retains the original encoded input;
registers seven, eight, and nine hold an optional source cursor, the target
position, and the success marker; eleven retains the following frame fields.
The adapter removes the temporary source cursor, converts the marker to the
ordinary success/failure tag, and invokes `SequentialAtomCodec.finish` through
an injective register map. The final state has only the original input and the
encoded value-task fields in register twelve; all work registers are empty.
The following frame fields and frame count are included unchanged in that
value-task encoding.

`NBoundedConstant.push_runs` verifies the status constants directly at the same
space capacity, rather than enlarging the surrounding input workspace.
`bounded_result_runs` discharges the local assembler's numeric bound from the
returned position, frame count, and bounded following fields. `space_linear`
provides its exact affine dependence on the numeric field bound for a fixed
local front.

`SequentialParamResult` connects the entire runtime environment lookup and
original-input interval comparison to this return adapter. `scan_bounds` and
`view_bounds` prove that the returned cursors stay within the original input
positions, including failure. `param_runs`, `compiled_param`, and `param_tape`
now end in `outputFields (atom x E (.param index) p) frameCount frameFields`,
not just a position and success flag. Their fourteen-tape execution retains the
original input, clears the work registers, and has an explicit capacity affine
in input length and the numeric field bound. It still starts from the separate
original-input/environment/position layout used by parameter evaluation.

`SequentialReadResult` embeds character and literal readers into the same
layout and applies the same assembler. `character_tape` and `literal_tape`
verify their full path to the ordinary encoded value-task result on fourteen
tapes. Character predicates include any character, a fixed character, and an
inclusive range. These adapters start after the caller has discarded the
capture environment, while preserving the frame fields. `literal_scan_bound`
justifies the result bound even after a partially matched literal fails.
`characterSpace_linear` and `literalSpace_linear` give exact affine capacity
formulas. All inputs remain arbitrary original character strings.

The source-ID selector must still be connected to these return adapters through
one common branch layout; the separate parameter path includes environment
lookup while character/literal paths need the environment-discard step first.
The ordinary-input loader and complete evaluator/terminal loop also remain.
The general CBV-Par versus CBV-Seq comparison is still unresolved.

### Unified source-selected atomic transitions

`SequentialAtomBranch` now places every atomic constructor in one common
thirteen-register layout. Parameter branches perform runtime environment
lookup and interval matching. Character and literal branches first drain only
the header-counted environment, preserving the saved position and following
fields, then invoke their reader/result adapter. Non-reading branches use the
same environment/position fields and the ordinary result codec. `branch_runs`
proves all these paths return the actual `SequentialStack.atom` result while
retaining the original encoded input. Each branch returns an ordinary encoded
value-task word with its frame count and following frame fields unchanged.

`SequentialAtomSelect` combines this branch table with the expression-task
normalizer. The entire input/output word occupies register twelve, the original
input register zero, and the temporary source ID register fourteen. The
normalizer reads that ID from the existing task encoding; `caseTop` consumes it
before invoking a branch. Thus the program is fixed by `exprPool ns` and does
not receive an external choice of atomic operation. `selected_runs` connects
the encoded expression-task word to the encoded value-task word for every
atomic source expression in the pool.

The capacity includes the normalization budget, local environment/result work,
and the sum of the reader reserves of the fixed source pool. Every selected
reserve is bounded by this sum. `reserve_affine`, `space_affine`, and
`capacity_affine` verify that these finite sums retain an affine capacity. In
particular, for fixed source pool, arity bound, and local frame-field count,
there are constants `a`, `b`, and `c` such that the compiled capacity is
`a * inputLength + b * numericFieldBound + c`. The original task's field bounds
also imply the normalized environment/position bounds; they are not additional
unverified post-normalization assumptions.

`bounded_selected_runs` discharges the task's encoded-size bound using its
arity, frame-field, clock, source-pool, and position bounds. `compiled_selected`
and `selected_tape` carry the complete normalization, actual-ID selection,
atomic evaluation, and value-task assembly through sixteen actual tapes. The
output state retains the original encoded input and the returned task word;
all work registers, including the temporary source ID, are clear. Arbitrary
original `List Char` inputs, empty captures/literals, EOF, absent parameters,
all character predicates, and undefined atomic results remain covered by the
respective branch correctness theorems.

This completes the unified numeric atomic transition component. Its initial
state still has the original input already encoded and the local task word
already decoded from the binary evaluator state. The binary front parser and
writer, full transition dispatch, ordinary-input initialization, and terminal
loop still need connection. The general Par/Seq equality-or-separation claim
remains open.

### Atomic transitions now include binary front parsing and writing

`SequentialInputHost` extends the existing eleven-list binary evaluator layout
to twenty lists. The original input encoding occupies register eleven. An
injective placement of the sixteen compiled atom lists leaves the binary
continuation, held value, constant two-marker, and field width untouched.
`old_runs` embeds an existing eleven-list program while preserving the input
register and fresh workspace; `atom_runs` embeds the unified atom program while
preserving the binary continuation and metadata. Its local-word register is
the same register used by the existing front parser and writer.

`SequentialInputPipeline` composes the embedded front parser, a twenty-list local
operation, and the embedded writer. Its transition theorem retains the original
input register through all three stages. It uses the parser's verified endpoint
space annotation and the writer's bit-capacity condition; no input-dependent
traversal time is converted to extra space.

`SequentialAtomMachine.transition_runs` now covers every reachable atomic
expression task. It starts with the complete encoded binary evaluator state,
parses the actual task/front, selects and evaluates the atomic source expression,
assembles the ordinary value-task word, and writes the next binary state with
the continuation unchanged. The separate original-input encoding survives the
entire operation. `transition_tape` carries that complete transition through
twenty actual tapes. The environment validity, clock, source-pool membership,
frame-field count, and numeric field bounds are derived from the reachable
original stack configuration.

`space_eq` isolates the additional numeric/input workspace as an affine term
in input length and the existing numeric field bound. `space_bound` then uses
the verified linear numeric bound and binary state-storage bound to obtain
`C * (n+1)` plus the existing `O(n log n)` state-storage term, with constants
fixed by the grammar and root expression. The theorem bounds every intermediate
state of this parser/atom/writer transition, rather than only its endpoints.

All transition kinds now have compiled components: the other entry/return
machines still use eleven lists and can be embedded with `old_runs` into the
same input-preserving host. A single outer dispatcher, terminal handling,
ordinary-input initialization, and complete evaluator loop remain to be
connected. In particular, this atomic transition still starts with the original
input already encoded in its separate register. The general Par/Seq
comparison remains unresolved; this space analysis alone gives no separating
language in P.

### One dispatcher for all nonterminal transitions

`SequentialStepScan` labels the existing front-read plans with seven transition
keys. It reads the actual task tag and, for expression tasks, the actual source
ID. Source expressions select atomic, structural, or call entry; the other task
tags select argument entry, rule query, or return. A value with an empty stack
selects a separate terminal continuation. `parser_trace` proves the selected key
and exact consumed front for every source-pool-valid configuration. No operator
or front-length selector is an extra runtime input.

`SequentialInputScan` compiles these labelled plans into the twenty-register
host with arbitrary twenty-register continuations. Its `compile_trace` lifts
the verified field fetches and counted reads while preserving the original
input register. `SequentialStepScanMachine` restores the unchanged binary front
before entering the selected continuation, so the existing complete transition
machines can be reused. The extra parse/restore pass is deliberate; it does not
change the intermediate space capacity.

`SequentialStepMachine` now binds all six nonterminal keys to the actual
compiled components. Atomic transitions use the twenty-register machine;
structural/call/argument/query/return transitions embed their existing
eleven-register machines and retain the original input and fresh workspace.
`transition_runs` covers every reachable configuration with an actual next
`SequentialStack.step`, and `transition_tape` carries that entire selection and
transition through twenty actual tapes. The end state is again the complete
binary evaluator configuration with its separate original-input encoding.

The capacity is the sum of the parser and component bounds. `space_eq` reduces
it to eleven copies of the binary front bound plus an affine numeric/input
term. `space_bound` then gives a single grammar-dependent linear term plus
eleven copies of the existing `O(n log n)` binary-state storage term, uniformly
for reachable configurations. It bounds every intermediate state of the whole
selected transition, not merely the selected component's endpoints.

The terminal continuation remains an explicit program parameter: this theorem
handles all nonterminal steps and does not claim a complete recognizer. Terminal
acceptance, repeated evaluation, and loading ordinary input into the initial
binary/original-input state remain to be connected. The general Par/Seq
comparison remains unresolved; no class separation follows from this upper
bound alone.


### Terminal acceptance and the complete initialized evaluator

`SequentialTerminalTest` reads the numeric terminal value word and accepts
exactly `some (some 0)`. Missing results, failures, and successful matches with
unconsumed input all produce a false answer. `compiled_runs` proves the actual
numeric-to-list compilation, with a linear bound on workspace.

`SequentialTerminalMachine` connects this check to the binary front parser and
the seven-way dispatcher. Its handler consumes the whole terminal configuration,
leaving the binary-state register empty and storing an acceptance marker in
register 17. The original input encoding remains in register 11. The parser's
remaining scratch value is harmless and stays within the verified capacity.

`SequentialEvaluationMachine.loop_of_runs` follows a finite `SequentialStack.Runs`
trace by induction, running the actual dispatcher once per nonterminal step and
once more for the terminal check. Every encoded configuration has a nonempty
binary-state register, while the terminal handler empties it. Consequently the
actual compiled loop terminates without an externally supplied iteration count.
`initialized_halts` includes the final acceptance-marker branch;
`initialized_tape` transfers the entire execution to twenty actual tapes.
`answer_iff` identifies its computed answer with full-consumption sequential CBV
observation for first-order grammars and root expressions.

The loop uses one capacity for the whole run: `reachable_space` chooses the
previous grammar-dependent linear plus `O(n log n)` upper bound uniformly over
all reachable configurations. Thus the proof bounds every intermediate scan,
copy, terminal check, loop test, and final branch; it does not merely bound
configuration endpoints. This is a space bound, with no new running-time bound.

The initial tapes in these theorems already represent the binary initial stack
configuration and the separately encoded original input. A loader from ordinary
input still needs to compute the input length, initialization clock, numeric
field width, and initial binary fields. The general Par/Seq equality or
separation remains open. The initialized evaluator and its space bound alone do
not establish a language-class separation from P.


### Computing initialization numbers from the runtime length

`Complexity.UnaryAffine.affine_runs` computes a fixed affine function of a
runtime source-list length, restoring that source and its temporary register.
Its capacity annotation covers all intermediate copies and constant pushes.
`Complexity.BinaryWidth.width_runs` repeatedly executes the existing division
and digit program, counting one unary cell per halving. It consumes the value,
clears its scratch registers, and leaves the exact binary bit length in the
output register. For positive values, `positive_width_runs` gives `log2 N + 1`;
`width_tape` transfers the same bound to the actual compiled tape execution.

`SequentialInitializationNumbers.bound_eq` expresses the evaluator's exact
`numberBound` as a grammar-dependent affine function of the input length.
The stage's actual program first computes this bound, then computes its bit
length, and finally computes `SequentialClock.positionClock`. Its input
`seed n X` contains only the unary input length in register 13 and the encoded
original input in register 11. The result keeps these registers and places the
width in register 8 and the clock in register 3. The bound value and arithmetic
scratch registers are empty afterward. `runs` and `tape` verify the full stage;
`space_linear` proves a grammar-dependent linear capacity in the original
input length, including the preserved original-input encoding.

This removes externally supplied clock, numeric-bound, and width values from
this initialization stage. The full ordinary-input loader still needs to
produce the length and original-input encoding, assemble the six initial
numeric fields `[0, clock, n, rootExprId, 0, 0]`, and invoke the verified binary
front writer. The initialized evaluator is already available after that
boundary. General Par/Seq equality or separation is still unresolved.


### Initial-field assembly and evaluation from the length/input seed

`SequentialInitializationFields.initial_fields` identifies the six initial
numeric fields exactly as `[0, clock, n, rootExprId, 0, 0]`. The fixed assembly
program appends the field markers and root ID, transfers the runtime clock and
length into their fields, initializes the two-marker register, and consumes
the length/clock registers. `assemble_runs` proves the resulting state is the
existing front writer's exact input, with the original-input register retained.
`runs` invokes that verified writer and produces precisely
`SequentialStepMachine.state g x e (SequentialStack.initial g x e)`.
`space_linear` bounds the entire assembly and emission stage, including every
copy and scan, by a grammar-dependent linear function of input length.

`SequentialSeedMachine.program` now composes numeric initialization, field
assembly and binary writing, and the complete evaluator on the same twenty
registers. `halts` proves termination from `seed n X`, and `tape` transfers the
entire computation to twenty actual tapes. `recognizes` attaches the exact
first-order Seq full-consumption observation on the same original `List Char`
to its halting answer. No clock, width, bound value, expression selector, or
binary initial configuration is supplied separately. `space_bound` adds only
a linear initialization term to the previously proved `O(n log n)` binary
stack bound.

The seed still contains the unary input length and `encS (codes x)`. An
ordinary-input loader must produce both of these from the actual input tape;
these theorems do not yet provide that loader or a standard-input TM class
membership theorem. The general Par/Seq language-class comparison remains
open, and the current space upper bound alone supplies no separating language.


### Recovering input length and evaluating from a single encoded input

`SequentialInputLength` scans the complete original-input encoding, counts its
field-marker cells, and moves the scanned cells onto a temporary stack. It then
reverses that transfer to restore the exact original encoding. `scan_runs` proves
the actual loop, including all intermediate moves and counter updates.
`encS_count` shows that each numeric field contributes exactly one marker;
`original_runs` therefore produces the evaluator's seed with the exact original
character count. Empty inputs are covered. The workspace capacity is the encoded
input length plus four cells, so `space_linear` bounds this stage linearly in
the original character length.

`SequentialEncodedMachine` composes this restored-input length computation with
the complete seed evaluator. Its sole initial data is `encS (codes x)` in
register 11; all other registers are empty. No input length, clock, width,
selector, or initial stack is provided separately. `halts` proves the whole
program stops, `tape` transfers it to twenty actual tapes, and `recognizes`
identifies its actual halting answer with first-order sequential
full-consumption observation on the same original character list. `space_bound`
retains the previous grammar-dependent linear plus binary `O(n log n)` capacity.

The theorem still starts with the original input already encoded as numeric
fields. It does not yet start at the standard raw input configuration, and
therefore does not establish a standard-input TM space-class theorem. The
ordinary-input encoding/loader and the general Par/Seq equality or separation
remain unresolved. In particular, the current space upper bound alone does
not give a separating language in P.


### Standard-input TM space bound on ordinary a/b words

`SequentialBinaryLoader` reads the standard list input, one input bit per
ordinary a/b character. It emits each character's numeric field into a temporary
stack in reverse order, then reverses the complete transfer into register 11.
`runs` gives exactly `SequentialEncodedMachine.input (bitWord w)`. It supplies
no repeated input, extra clock, length field, or binary stack state. The loader
uses at most `100*n+4` cells per tape, including intermediate constant pushes.

`SequentialBinaryInputMachine.program` composes the existing standard tape
initializer `initP` with this loader and the complete evaluator. `tape` starts
at the actual `initTapes 20 w`. `recognizes` ties its halting answer to sequential
CBV full-consumption observation of `bitWord w`, the ordinary a/b word with one
character per input bit. `finite_alphabet` obtains a fixed finite tape alphabet
from the finite list program, and `machine` transfers the entire run to an
actual deterministic twenty-tape TM from `initCfg 20 w`.

For each fixed first-order grammar and root expression, that TM decides the
same ordinary binary language with capacity

```
(C + 104)*(n+1) + 11*(A*(n+1))*((n+1).log2 + B.log2 + 2)
```

where `C`, `A`, and `B` depend only on the fixed source grammar and expression.
This is an `O(n log(n+1))` bound on every intermediate configuration of the
standard-input computation, including input import, encoding, length recovery,
clock/width computation, initial-stack writing, evaluation, and final acceptance.
No running-time improvement is claimed.

This closes the standard-input connection for the ordinary a/b alphabet. The
arbitrary-Char input decoder remains separate. General Par/Seq equality or
separation is still open, and the space upper bound alone does not separate
Seq from Par=P on the binary alphabet.


### The language-class consequence and the remaining lower bound

`Complexity.SpaceNLogN` states deterministic `DSPACE(n log(n+1))` with the
standard binary-input convention: one fixed finite-tape TM and one constant
`C` bound every input run by `C*(n+1)*(log2(n+1)+1)` cells per tape.
`SequentialBinaryInputMachine.space_nlog_bound` absorbs the previous explicit
source constants into this conventional bound.

`Shallot.PegSeparation.binary_seq_in_nlog_space` therefore applies to the
entire first-order Seq class on the ordinary a/b alphabet, without assuming
a particular source grammar or a separate initialization routine.
`binary_reverse_requires_P_nlog_space` and
`original_reverse_requires_P_nlog_space` combine it with the verified binary
Par=P theorem: either binary reverse inclusion or a general original-character
reverse translation would imply that every P language belongs to this space
class.

`P_outside_nlog_space_separates_original` gives the other direction needed by
a possible space-based separation strategy: an explicit P language outside
this deterministic space bound would be recognized by a fixed Par grammar,
while no Seq grammar could recognize it. It includes the already proved
Seq-to-Par inclusion and the genuine original-character-language separation
conclusion, using the same unpadded input correspondence.

These are implications, with the complexity lower bound an explicit hypothesis.
No such P witness is constructed here, and no converse from a space upper bound
to Seq recognition is claimed. Consequently none of these theorems decides the
Par/Seq comparison. This isolates the missing mathematical step in a space-based
strategy; merely improving the input loader or repackaging the upper bound does
not supply it. Direct reverse compilation, or a genuine non-inclusion witness,
remains the requested conclusion.

The [2019 article](https://kmizu.hatenablog.com/entry/2019/10/24/145039) also uses
both evaluation conventions for tag matching. Rechecking that example confirms
the calling-position distinction; it does not itself supply a language-class
separation or a general translation. The repository's `SequentialCaptures`
results already rule out retaining a nonempty literal capture at the same
Seq argument/body position, and the earlier residual-interface impossibility
results explicitly leave whole-grammar transformations and retained continuations
open.


### Direct reverse translations for recursive replay tests

`CallLookahead` separates input restoration from capture evaluation. For an
arbitrary fixed first-order Par grammar, let `tested g` put a positive lookahead
around each rule body. Let `wrapped g` instead transform all body call sites
into positive lookaheads, recursively transforming their argument expressions.
`observations_iff` proves that `tested g` on an original expression and
`wrapped g` on its transformed expression have exactly the same finite
observations on every original input. The proof relates all table-approximation
clocks with `Peeked`: successful rule results are reset to the caller position,
while explicit failure and undefined results are retained. Calls of arbitrary
arity, recursive calls, argument failure, missing rules, and arity mismatches
are covered. No totality premise is required. This particular rule-to-call
lookahead movement is proved for Par; it is not claimed for Seq, whose arguments
already consume input before the body is entered.

`ReplayTestFusion` composes this movement with the verified replay fusion.
Its Par source rules have the shape `F(x) <- &(x B)`. The fixed Seq target
rules are `F(x) <- translated(B)`, and every translated call is under positive
lookahead. The Seq argument consumes the prefix which the Par body replays;
the literal capture remains available in `B`, and the enclosing call lookahead
restores the original caller position after the test. `observations_iff`
preserves every finite observation, and `language_translation` constructs an
actual fixed first-order target grammar and root expression recognizing the
same original character strings, including empty input. Recursive first-order
tails may freely reuse their captured literal values.

`PrefixPairTestFusion` extends the same construction to the earlier factored
two-prefix interface. Template calls `F(A,B)` mean `F(A,A B)` in the Par source
and `F(A,B)` in the Seq target. Par retains the two common-origin values `u`
and `u++v`; Seq captures consecutive chunks `u` and `v` and reconstructs both
values when referenced. The source body tests a replay of its full second
prefix followed by its template tail. The target omits that leading replay
and uses positive lookahead at each call site to restore the caller position.
`render_commute`, `wrapped_pair`, `observations_iff`, and `language_translation`
connect the actual recursive fixed grammars. Template calls are required to
have two arguments everywhere; this condition is stated by `PairCalls`.

These results add genuine Par-to-Seq translations for recursive capture-using
tests whose call results do not advance their callers. They do not normalize
arbitrary Par bodies into replay-test form, nor factor arbitrary independent
Par arguments into adjacent chunks. The earlier residual-interface
impossibilities are not contradicted: the new construction changes call-site
control and the callee's position together. The general equality/separation
question remains open; these fragments are progress toward a reverse compiler,
not a proof that the whole classes coincide.


### Static literal captures: reverse compilation without leading replay

`LiteralArguments` isolates a different route around the calling-position
problem. When an actual argument is a literal expression or a forwarded
parameter, its captured word is statically known from the enclosing value
environment. This does not make the argument evaluation optional: the literal
must still match at the original caller position, even when the callee ignores
its parameter. `arguments_eval` proves that the actual left-to-right Par
argument evaluation resolves the value vector and checks every word against
that same original suffix. A missing forwarded parameter fails, and empty
literals are covered. `guards_eval` realizes these checks as non-consuming
positive-lookahead guards.

`LiteralSpecialization` enumerates one finite specialization for each source
rule and each value vector of the rule's arity over a fixed finite palette.
`mem_specs` and `specs_valid` prove coverage and validity of the actual
input-independent enumeration. The compiler replaces each parameter with its
literal value and each call with argument guards followed by a zero-argument
call to the appropriate specialized rule. Missing rules, arity mismatches,
and unresolved arguments preserve failure. `target_zero_arity` verifies that
every generated rule has arity zero. There is no leading-replay restriction
on the source rule body.

`evaluator_of_related` and `tables_related` connect the actual finite generated
grammar to the source Par evaluator at every table clock. The target Seq call
receives no consuming arguments, while the guards check the original arguments
at the caller's unchanged position. `limit_eq` uses both fixed-point stability
bounds; it does not assume that the differently sized source and target grammars
have identical iteration bounds. `observations_iff` consequently preserves
success with every residual input, finite failure, and absence of a finite
result through arbitrary recursive supported bodies.

`LiteralSpecializationCompiler` removes the supplied-palette premise. It
collects the argument literals from all source rules and the root expression,
proves that every resolved value stays within that palette, and produces one
fixed first-order Seq grammar and root from the source syntax alone.
`language_translation` preserves full-consumption recognition on exactly the
same original character strings, with no totality or input-size assumption.
Source bodies may contain arbitrary supported recursion, sequencing, choice,
negation, repetition, and reuse of their parameters.

The precise restriction is syntactic: every actual argument at every call is
a `.lit` expression or a `.param` forwarding an existing value. The result does
not yet cover `.any`, `.range`, an arbitrary finite-valued argument parser, or
unbounded dynamically captured strings. Those require additional value-selection
or residual parsing machinery. This gives a direct reverse compiler for a
new source fragment with unrestricted body placement, but does not establish
the general Par-to-Seq inclusion or a language-class separation.


### Input-dependent finite choices and committed continuation failure

`ChoiceArguments` extends the finite-value argument interface to nested ordered
choices of literals and forwarded parameters. The captured word can now depend
on which alternative matches the original input. The selector's continuation
runs at the unchanged caller position after that value has been chosen.

Plain distribution across the continuation would be incorrect: if `A` matches
but its specialized callee fails, a naive alternative may retry `B` and accept
with a different captured value. `plain_distribution_changes_result` gives a
concrete formal counterexample on the same input `ab`: committed selection
fails, while naive distribution accepts the entire word. `branch_eval` and
`select_eval` prove the required commitment, including a continuation with no
finite result. The implementation tests the first argument alternative with
positive lookahead and protects the other branch with its negative guard.
`selectArgs_eval` composes these selectors in the original argument order;
all argument alternatives are checked against the same caller input.

`ChoiceSpecialization` connects these selectors to the actual finite
rule/value-vector enumeration from `LiteralSpecialization`. Every successful
selected value stays in the palette (`arguments_bounds`), every generated rule
has arity zero, and the selected specialization's result agrees with the source
Par table. `tables_related`, `limit_eq`, and `observations_iff` preserve every
finite observation through recursive source bodies. The proof uses the two
grammars' separate stability bounds, rather than assuming equal-sized grammars.

`ChoiceSpecializationCompiler` recursively collects literals from the ordered
argument choices in all rules and the root. `language_translation` constructs
one fixed first-order Seq grammar and root from this source syntax, preserving
full-consumption recognition of exactly the same original character strings.
There is no leading-replay restriction on source bodies.

The argument grammar proved here is precisely `literal | parameter | argument /
argument`. Arbitrary nesting and forwarding are covered. Character/range
captures, concatenation of argument parsers, arbitrary finite-valued recursive
argument parsers, and unbounded dynamically captured strings are not yet
covered. This extends the reverse compiler to a concrete input-dependent
finite-value fragment; general Par/Seq equality or separation remains open.


### Sequential argument composition with a checked finite domain

`SequenceArguments.selectAt` extends the selector to argument sequencing.
Its continuation still runs at the original caller position. When the first
part selects `u`, the next selector tests the second part after the known
prefix followed by `u`; this replay occurs entirely inside lookahead. The
selected result is `u++v`. `probe_eval`, `pre_concat`, and `selectAt_eval`
prove that the probed position and the concatenated captured word agree with
the actual sequential argument evaluation. Ordered choices retain their
commitment before the continuation. `selectArgs_eval` then evaluates each
whole Par argument against the original common caller position.

`SequenceArgumentDomain.possible V a` enumerates the syntactically possible
words of an argument: literals are singleton sets, parameters range over the
palette `V`, choices combine lists, and sequences form concatenations. `Closed`
requires the supported argument syntax and membership of every possible final
word in `V`. Intermediate pieces of a composite argument need not themselves
be members of `V`; `concrete_concatenation_checked` demonstrates that a palette
containing only `ab` can cover the composite literal argument `a b`.
`success_possible` and `arguments_bounds` prove this syntactic check covers
every value selected in an actual run. `closedB_iff` and `supportedB_iff`
connect the executable finite checks to their precise predicates.

`SequenceSpecialization` connects this selector to the fixed finite
rule/value-vector enumeration. Every target rule has arity zero. The full
table, limit, and observation proofs cover recursive source bodies and
preserve success, failure, and undefinedness. `check` tests a supplied finite,
input-independent palette against every source rule and the root expression.
`checked_observations` and `checked_language_translation` prove that a successful
check produces one fixed first-order Seq grammar recognizing the same original
character strings, without a leading-replay or totality requirement.

A finite palette is an actual restriction, not an automatic consequence of
argument sequencing. `no_nonempty_palette_for_duplication` proves that the
syntactic closure check for `param(0) param(0)` cannot succeed with a palette
containing a nonempty word: closure would contain words of arbitrarily large
length. This theorem concerns the finite-domain interface and does not prove
language-class non-inclusion. The check also overapproximates possible parameter
combinations, so no completeness claim for finite-valued source semantics is
made.

The exact supported argument syntax is literal, parameter, sequencing, and
ordered choice. Character/range atoms, argument repetition and recursion,
and general unbounded captures remain outside this compiler. General Par/Seq
equality or separation remains open; the finite-domain construction does not
replace the required unbounded representation or a genuine separating witness.


### One unbounded runtime capture with finitely many auxiliary values

`HybridReplayFusion` combines the unbounded-capture replay transformation with
finite static specialization. For a fixed number `d` of auxiliary parameters,
each source rule has arity `d+1` and body `head tail`, where `head` replays
parameter zero. The first actual argument may be an arbitrary supported
recursive first-order expression, including repetition and reuse or duplication
of the runtime head. The remaining actual arguments are literal words or
positive-index parameter forwards, whose values remain in a finite palette.
They are all evaluated against the same original Par caller input.

The target enumerates only rule/auxiliary-value-vector specializations. Each
generated Seq rule retains arity **one** (`target_arity_one`): the head word
remains a real runtime capture, with no global length bound and no membership
requirement in the finite palette. Positive parameters in the source body are
replaced by their specialized literals; parameter zero remains a parameter.
The source's leading head replay is omitted in the target because the Seq
argument evaluation already consumes that same prefix.

Argument evaluation order is essential. The compiled call first checks the
translated head argument under lookahead, then checks the finite auxiliary
arguments at the unchanged caller position, then invokes the specialized Seq
rule with the translated head argument. The preliminary head check prevents
an undefined first argument from being hidden by a later failing or unresolved
auxiliary argument. The actual Seq call evaluates the head again; determinism
makes its captured value and remainder agree with the preliminary check.
The proof covers undefinedness, finite head failure, failed auxiliary matches,
unresolved forwards, and successful entry to the body.

`evaluator_of_shift` preserves this calling convention for arbitrary supported
bodies. `tables_shifted` connects all recursive table approximations while
retaining the unbounded head as a runtime value. `limit_eq` handles different
fixed-point bounds of the source and specialized target. `observations_iff`
and `language_translation` preserve every finite observation and the same
original character language, without assuming totality.

`HybridReplayCompiler` collects only the literal auxiliary values from all
source tails and the root, proving the required palette property automatically.
The head expression is traversed for nested calls, but its captured word is not
placed in that palette. It therefore builds a fixed first-order Seq grammar
and root from the source syntax alone. `duplication_shape` verifies that
`param(0) param(0)` is permitted as a head argument: the finite-domain
obstruction proved for specializing *all* values does not apply to this runtime
head representation.

This construction keeps one unbounded value and specializes any fixed number
of finite auxiliary values. Its restrictions remain explicit: every source
body begins by replaying the head, all source rules have the common arity
`d+1`, and auxiliary arguments are literals or non-head parameter forwards.
It does not yet accommodate several independent unbounded captures, arbitrary
body placement, or a general Par normal form. Consequently it is a further
direct reverse fragment, not a proof of general equality or separation.

### Arbitrary overlapping captures: disjoint runtime values and finite body views

`CommonOriginCaptures` removes the restriction to one or two unbounded values
at the **value representation** level. Every successful `DerivesArgsPar`
derivation produces words that are prefixes of its common caller input
(`par_prefixes`). Sort these words by length and split adjacent prefixes at
their boundaries. `chunks` constructs exactly as many consecutive pieces as
there were arguments. Empty captures and repeated lengths give empty pieces;
they require no special exclusion. The total stored character count is at
most the caller input length (`storage_bound`).

`ranks` records, in the original parameter order, how many pieces reconstruct
each captured word. `reconstruct` proves exact recovery of the entire tuple.
For arity `d`, all ranks lie between zero and `d`, and the rank vector belongs
to the input-independent list `controls d d`. This list has exactly
`(d+1)^d` entries, counting all vectors rather than only reachable ones. No
captured word or character value belongs to a finite palette. The runtime
pieces can have arbitrarily large lengths and arbitrary character contents.

`par_representation` connects this representation to the actual argument
semantics: the literal expressions for those pieces form a successful Seq
argument list on the original input, producing exactly the disjoint runtime
values and leaving the suffix after the longest capture. This literal list
is computed from **already evaluated capture values**. The theorem therefore
does not supply a fixed Seq parser for discovering the pieces.

`CaptureViews.prefixExpr k` replays the first `k` consecutive runtime pieces.
`prefixExpr_eval` proves that this expression has the same partial evaluator
value as the reconstructed captured literal. The general `evV_rebind` lemma
then extends equality of parameter views to any first-order expression,
including ordered choice, repetition, predicates, and calls under either
argument convention. `finite_body_choice` provides an input-independent finite
list of first-order body variants, one of which preserves the original body's
full three-valued evaluation with the disjoint environment. The final
`par_body_representation` packages successful Seq value capture and this body
view together for arbitrary successful Par argument derivations; it imposes
no replay, literal-argument, or finite-capture restriction on the source.

This is a representation and local evaluation result. Both sides of each
body equality use the **same input position, grammar, strategy, and recursive
table**. Calls inside a body still enter the original rules with the same
argument values. No equivalence of a globally transformed recursive grammar
or of different Par/Seq calling strategies follows yet. A general reverse
translation must still discover the correct pieces and finite control from
the source syntax at runtime, preserve argument failure/undefinedness and
order, and reconcile the original Par body position with the later Seq body
position. Multiple unbounded values themselves now have a verified disjoint
representation; these operational obligations remain open, as does the
language-class equality/separation question.

### Why disjoint capture values alone cannot repair body-entry position

`PartitionResidualControl` tests the preceding representation against the
remaining entry-position obligation. The obstruction is stronger than the
earlier single-literal residual result: even an arbitrary prefix-selected
partition with any fixed arity bound, plus arbitrary finite prefix-selected
body control, cannot provide a general local residual interface.

For a bounded environment whose nonempty words cannot match any remaining
suffix, `signature` records exactly which parameter slots contain the empty
word. Empty words remain observable, while nonempty dead words and missing
slots all fail. `agree_iff_signature` proves that this is the exact
`EnvAgree` quotient. The signature belongs to `controls 1 arity`, a list of
size `2^arity`, independently of the captured lengths and contents. This
handles empty chunks explicitly; simply declaring every chunk dead would be
incorrect.

`no_finite_tuple_summary` allows any bounded runtime tuple with this property,
not just the canonical sorted differences. It shows that no finite
prefix-selected body state together with that tuple can recognize `n=m` on
the remaining suffix `c^m` for all prefix counts `n`. The proof combines the
finite body state and the empty-slot signature into one finite key. Equal
keys give indistinguishable continuations in an arbitrary first-order target
grammar, contradicting the infinitely many required residual behaviors.

For every partition of the consumed prefix `a^n b`, all its nonempty pieces
are dead on `c^m` (`partition_dead`). `no_partitioned_factorization` therefore
rules out this interface for the actual balanced source grammar
`B <- 'a' B 'c' / 'b'`, even for whole-input acceptance. The target grammar
and its recursive bodies are arbitrary; the selected entry state and tuple
must depend only on the consumed prefix, and the tuple length has a fixed
bound. `CommonOriginCaptures.chunks_cover` identifies the canonical chunks
with the whole prefix whenever the common-origin tuple contains that longest
prefix. `no_common_origin_factorization` applies the obstruction directly to
that representation and arbitrary finite body variants.

The balanced grammar itself recognizes `a^n b c^n` under **both** CBV
strategies, as `FiniteResidualControl.balanced_recognizes` already proves.
This is not a separating language. The residual interface discards any
unbounded pending caller continuation before entering the suffix; a genuine
Seq recognizer can retain its recursive callers. Selection that has already
inspected the suffix is also outside this interface. Thus a general reverse
construction cannot consist solely of capturing a bounded tuple of past
segments and selecting a finite body at the advanced position. It must
preserve additional computation, use a different evaluation arrangement, or
otherwise avoid these explicit hypotheses. General Par/Seq equality or
language-class separation remains open.

### Moving Seq body tests to call sites while retaining runtime consumption

`SequentialCallLookahead` supplies an evaluation rearrangement that may inspect
the suffix while holding arbitrary runtime captures. As in `CallLookahead`,
`tested g` replaces each rule body `B` with `&B`. Here the strategy is Seq,
so a call still consumes its actual arguments before testing that body.
Moving the body test to a plain `&F(args)` at the caller would erase this
argument consumption. `plain_peek_changes_result` gives an actual derivation
counterexample: a one-argument empty rule consumes the input `a`, while the
plain call peek leaves it untouched and fails whole-input acceptance.

The corrected translation replaces a call by

```
&F(render(args)) sequenceArgs(render(args))
```

and replaces each target rule body with its recursively rendered body.
`sequenceArgs` evaluates the argument expressions consecutively and returns
their final position, discarding only the resulting value tuple. The call
probe first evaluates those arguments and invokes the rule with their actual
captured words, so its body can inspect the remaining suffix with those
values bound. Failure or undefinedness of that call propagates before the
second argument pass. If the probe succeeds, argument re-evaluation is
deterministic and reproduces the same final position. The enclosing caller
therefore advances exactly as it did with the body test in the source.

`evaluator_of_peek` and `arguments_of_peek` prove this simultaneously for
expressions and Seq argument lists under related arbitrary recursive tables.
`tables_peeked` establishes the relation at every recursive approximation.
Rule counts and arities stay equal, so `iterBound_eq` connects the actual
fixed-point decision procedures. `observations_iff` preserves every finite
observation on the original character strings, and `language_translation`
constructs the fixed first-order Seq target grammar and root.

There is no finite capture palette, bound on capture lengths, or restriction
to a replay-first body or a fixed argument count. Recursive calls in arguments,
repetition, predicates, failure, and undefinedness are included. Values remain
bound inside the probed call; the construction does not export captures from
a lookahead. The transformation concerns a **Seq source with body tests**
and a Seq target. Inserting tests into an arbitrary source grammar is not
claimed to preserve its original language. Nor does the result reconcile
overlapping Par argument values or the original Par body position. It is a
verified whole-grammar component for suffix-informed evaluation arrangements;
the general Par-to-Seq translation and language-class comparison remain open.

### A fixed Seq evaluator for forward Boolean reference programs

`ForwardQueryScan` and `ForwardBooleanProgram` implement a concrete use of
runtime captures, suffix inspection, and retained recursive callers. One
fixed first-order Seq grammar evaluates every finite forward Boolean program
from its serialization. There is one recursive rule of arity one; the grammar
does not depend on the program, its labels, or its computed values.

An identifier is `a^n b`, with no bound on `n`. A record is `[identifier]gate;`.
The gate forms are `1`, `0`, `!identifier`, and `&identifier,identifier`.
The whole input begins with the queried identifier and then the record list.
Lookup selects the first matching later definition. Operands of that gate
are evaluated in the strict record tail after its definition; missing
references are false. These rules give total semantics for every finite
record list, including repeated labels, while admitting arbitrarily large
forward acyclic circuits with shared references.

The grammar has the following shape, using Seq calls throughout:

```
Id      <- 'a'* 'b'
Q(name) <- &((!('[' name ']') .)* '[' name ']'
            ('1' / '!' !Q(Id) / '&' Q(Id) ',' Q(Id)))
Start   <- Q(Id) .*
```

`Q(Id)` captures the actual reference word before its body runs. Its body
searches later declarations while that captured value remains bound. On
success the lookahead restores the position immediately after the reference,
so a conjunction can then read its comma and second operand. Nested queries
retain their callers rather than exporting values out of lookahead. The
strict declaration-tail induction proves that every query on a serialized
program terminates with success or finite failure. The empty program and
missing definitions are included.

`seek_header_here` and `seek_header_skip` verify the actual capture-dependent
search. `query_observation` connects all finite programs to recursive Boolean
evaluation, including short-circuit conjunction and negation. `table_correct`
identifies this semantics with a right-to-left table that computes and retains
shared gate results. `program_observation` and `table_recognizes` connect the
fixed root to whole-input acceptance on every serialized program. For example,
`b[b]&ab,ab;[ab]!aab;[aab]0;` evaluates the same referenced negation twice and
accepts. `accepted_identifier_unbounded` proves that accepted inputs actually
use captured identifiers beyond every fixed length bound.

The preceding Seq lookahead relocation applies to this entire recursive
machine. `normalized_observations` preserves all character-input observations,
including malformed inputs, between the body-test grammar and its translated
call-probe grammar. `normalized_program_recognizes` connects the translated
grammar to the same Boolean table on the original serialized program strings.

The program-correctness theorem is stated on serialized program inputs; it
does not assert a syntax-validation characterization for arbitrary malformed
strings. No polynomial-time hardness reduction or simulation of every P
language on its unchanged original input has been established here. In
particular, generating a circuit encoding from some other input would not
supply the language-preserving Par-to-Seq translation required by the main
question. This construction verifies a uniform, unrestricted-size runtime
lookup mechanism and its recursive use; general Par/Seq equality or
language-class separation remains open.

### Exact forward-program language, including malformed inputs

`ForwardBooleanSyntax` closes the preceding promised-input gap by adding a
syntax guard to the existing fixed evaluator. It introduces no program-specific
rules or input rewriting. The validator reads the root identifier and zero or
more complete records, then requires end of input. Its gate parser recognizes
exactly the four serialized gate forms and checks all operand delimiters.
The entry is `&validator Start`, with the same one-rule Seq grammar as before.

`readId_sound`, `gateSyntax_sound`, and `recordSyntax_sound` recover the
serialized objects from arbitrary successful parses. `syntax_sound` handles
every original character string and recovers a root identifier and complete
program. The converse is proved by `syntax_complete`; `syntax_iff` gives exact
syntax recognition. `syntax_total` proves finite evaluation on every input:
identifier repetition consumes a character on each step, and every successful
record consumes its opening marker. Thus malformed strings are covered by a
termination proof, not merely omitted from the program specification.

`ProgramLanguage x` is the explicit character-language predicate

```
exists n P, x = identifier(n) ++ encode(P)
            and tableLookup(evaluateTable(P), n) = true.
```

`language_iff` proves acceptance equivalent to this predicate for **all**
`List Char` inputs. `nonserialization_failure` gives actual finite failure
for every malformed serialization. `entry_decides` strengthens acceptance
equivalence to a finite Boolean decision on every string, ruling out both
undefinedness and a partially consumed success. The previous semantics of
missing references and repeated labels is retained: this layer checks syntax
and does not silently add a unique-label or defined-reference condition.

`normalized_language_iff` and `normalized_entry_decides` connect the validated
entry to the call-probe version on the same original strings, including all
malformed inputs. `CBVForwardBoolean.forwardBoolean_is_seq` packages the fixed
grammar and root as actual `IsFirstOrderCBVPEL` membership, and
`forwardBoolean_normalized_is_seq` gives the second concrete Seq witness.
`forwardBoolean_is_par` applies the existing language-preserving Seq-to-Par
translation to exactly the same character language.

This supplies a total language recognizer and a concrete common language-class
member, rather than only evaluator correctness on an assumed syntax domain.
A complexity-hardness reduction and an input-preserving simulation of all Par
grammars remain separate obligations. Neither general equality nor separation
of Par and Seq follows from this common member.

### Numbered Boolean circuits and a quadratic data encoding

`Complexity.BoolCircuit` defines a separate, grammar-independent circuit
model. Gates occur in evaluation order and are Boolean constants, negations
of numbered wires, or conjunctions of two numbered wires. `WellFormed`
requires each operand to refer to an earlier gate. Evaluation appends each
computed bit to the value vector; an unavailable wire defaults to false,
so the evaluator is also defined for ill-formed gate lists.

`CircuitProgram` connects this model to the fixed forward-program Seq
recognizer. A left fold emits gate `i` as a record with label `i`, prepending
it to the previously emitted records. Thus circuit evaluation order becomes
the reverse declaration order needed by forward queries. Each gate becomes
exactly one record (`program_length`); sharing is preserved as references,
without expanding a circuit into a formula tree.

`compileFrom_correct` proves that appending a circuit bit and prepending its
forward definition preserve the whole wire-value function. `program_correct`
and `table_correct` connect every output index to the previously verified
forward-query and table semantics. `recognizes` and `normalized_recognizes`
then identify full-input acceptance by the fixed validated Seq grammars with
the circuit's output bit. These semantic theorems cover every finite numbered
gate list; well-formedness is needed for the size statement, not hidden as a
semantic assumption.

For `N` gates in a well-formed circuit and a root index at most `N`,
`input_length_bound` proves that the complete character input has length at
most `N * (3*N + 8) + N + 1`. The proof bounds emitted labels and all operands,
then the actual unary identifier, header, gate payload, and program lengths.
The grammar remains fixed independently of `N` and the circuit contents.

`input_language_iff` states the explicit mapping into the exact
`ProgramLanguage` predicate. This is a semantic reduction with a verified
quadratic output-size bound. No logspace or polynomial-time Turing-machine
implementation of the encoder, or P-hardness theorem, is asserted. The mapping
also changes an input circuit into its character serialization: it does not
provide the unchanged-input simulation of every P language needed to close
the Par/Seq comparison. General equality and separation remain open.

### Research audit: regex and auxiliary-pushdown comparisons

The [ICALP 2024 REWBLk paper by Uezato](https://drops.dagstuhl.de/storage/00lipics/lipics-vol297-icalp2024/LIPIcs.ICALP.2024.155/LIPIcs.ICALP.2024.155.pdf)
identifies its regex model with NLOG. Its syntax has finite capture variables
and iteration, without recursive grammar rules. Its choice takes a union of
possible results, and positive lookahead retains variable updates (Sections
3.1–3.2). These hypotheses differ from Macro PEG's prioritized choice,
callee-local captures, and recursive activations. In particular, Macro PEG's
double-negative lookahead returns no updated caller environment. Applying the
NLOG theorem to Seq would require a separate semantics-preserving translation;
the similar capture and lookahead notation does not establish one.

The [auxiliary-pushdown review in Allender and Lange, 2014, Section 1](https://theoryofcomputing.org/articles/v010a008/v010a008.pdf)
also distinguishes two bounds that must not be conflated. A logspace auxiliary
pushdown machine has a stack excluded from its work-space charge. With
unrestricted running time the deterministic model characterizes P; imposing
polynomial time gives Log(DCFL) for deterministic machines, and Log(CFL) for
nondeterministic machines. Thus merely identifying logspace local storage and
a pushdown stack would not provide a strict upper class below P.

The current Lean evidence is more specific than either analogy:

- `SequentialStackCodecBound.task_length` and `frame_length` bound each local
  record by a grammar-dependent number of integer fields.
- `SequentialStackPayload.reachable_payload_bounds` bounds the stored capture
  endpoints, positions, and clocks at every actual reachable state.
- `SequentialStackRank.stack_linear_bound` bounds the number of live frames
  linearly in input length; `SequentialStackBinary.reachable_bit_bound` charges
  the whole retained stack, not just the active environment.
- `CBVSeqSpace.binary_seq_in_nlog_space` connects the complete initialized
  machine to the actual binary Seq language class in deterministic
  `O(n log(n+1))` space.

These are proved interpreter bounds. No polynomial running-time bound for the
same stack-recomputation algorithm has been proved. The separate memo-table
P upper bound cannot be combined with a different algorithm's local memory
bound to obtain a simultaneous time/space theorem. Likewise, the interpreter
can store capture origins as numeric input intervals; a source grammar's
captured value is a word, not an instruction for arbitrary coordinate access.
A reverse simulation must implement the needed access with Seq syntax.

The audit therefore changes the next proof obligation. A smaller-class upper
bound needs one complete algorithm satisfying that class's simultaneous
resource conditions, including all pending environments. A P lower bound via
auxiliary pushdown machines needs an actual input-preserving Seq simulation,
including input-head motion, stack manipulation, and capture access. Neither
obligation follows from the existing stack interpreter. The already proved
`original_reverse_requires_P_nlog_space` remains a necessary consequence of
general equality; it is not a proof of equality or separation. This audit
adds literature evidence and narrows the available methods, without claiming
a new Lean theorem or a solution of the language-class question.

### Capture frontiers across actual Seq continuations

`SequentialCaptureRegions` adds an operational interval invariant for the
existing `SequentialStack.step` machine. It does not change the machine or
store additional runtime metadata. Positions are suffix lengths: after
progress, a position becomes smaller. `Past E p` says that every captured
interval in `E` ends before the cursor at `p` in the original input order.

`Window p q W` records consecutive intervals from argument evaluation,
with endpoints `p = j0 >= j1 >= ... >= jd = q`. Empty intervals are allowed.
`Window.weight` telescopes their numeric lengths to `p-q`.
`Window.decoded_weight` proves the same equality for the lengths of the
actual captured character words, under the original-input bound. The
representation therefore accounts for the values used by grammar semantics,
not merely numeric spans.

The `ScopedValue`, `ScopedTask`, `ScopedFrame`, and `ScopedStack` certificates
track cursor bounds and argument windows through all transition cases.
`return_scoped` includes sequencing, ordered-choice restoration, both predicate
results, repetition progress and stalling, argument assembly, and call entry.
`step_scoped` and `reachable_scoped` connect these certificates to every
reachable state of the unmodified initialized transition machine.

`reachable_past` proves that the task's captures and all captures retained in
every continuation frame precede the current cursor. When a returned task
contains a successful argument tuple, `reachable_arguments` proves more:
there is one consumed window, and every fresh interval in it is after every
older interval retained anywhere in the remaining stack. In suffix-length
coordinates, `fresh.start <= old.end`. `reachable_decoded_arguments` packages
this global separation with the exact consumed character count.

This establishes the freshness condition needed to study total retained
capture storage. It does not assert that two older frames have disjoint
environments: structural continuations can retain copies of the same caller
environment. Bounding those copies, accounting for all saved cursors and
clocks, and implementing any proposed compressed representation remain
additional obligations. The current deterministic space upper bound remains
`O(n log(n+1))`; no linear-space bound or Par/Seq separation is claimed here.

### One environment per Seq activation and a global capture-payload bound

`MacroPeg.CBV.SequentialSharedStack` now implements a second deterministic
Seq evaluator. A configuration stores one current capture environment.
Sequence, choice, negation, repetition, and argument-head continuations carry
no environments. When a query enters a rule body, it saves the caller's
current environment once in a scope frame and installs the new argument
environment. Returning through that frame restores the caller environment.
In particular, a nested call inside an argument restores the environment
needed to evaluate the remaining arguments.

This is an executable transition function, not an assumed semantic operation.
`expression_runs`, `arguments_runs`, and `query_runs` prove its finite-clock
semantics and environment restoration. `original_result_iff` equates its
terminal results with those of the existing `SequentialStack` on the same
original `List Char` input. `accepts_iff` connects it to first-order Seq
observations. The fuelled `drive` returns the whole terminal configuration;
`drive_result_iff` checks both the result and restoration of the empty outer
environment, including failed and undefined finite-clock results.

`MacroPeg.CBV.SequentialSharedSpace` proves a global bound that was unavailable
for the evaluator with duplicated continuation environments. It charges a
span `(p,q)` by `p-q` and counts every retained copy: the current environment,
all suspended scope environments, every pending argument head, and an
argument environment stored in the current task or returned value.
`reachable_weight` bounds their total charged length by the input length at
**every reachable state**. `reachable_captured_characters` consequently bounds
the sum of lengths of all their decoded character words by the same input
length, even if each retained span is materialized as a separate word.

The proof uses the exact argument-window conservation law from
`SequentialCaptureRegions`: successful arguments started at `p` and ending
at `q` have total capture length `p-q`. A proof-only continuation certificate
assigns the fresh callee environment this consumed-input credit. On entry to
a body, its environment length plus its starting cursor is at most the
caller's credit. A scope return releases the callee environment. Structural
continuations save no capture payload, and pending argument heads telescope
against the starting cursors of the argument tails. The certificates add no
runtime accounting fields.

This bounds captured **character payload**, not the total space of a Turing
machine. It does not bound the number of empty captures or scopes, compress
integer cursor and clock metadata, or implement bounded-space allocation and
parameter lookup. The previously proved complete TM bound remains
`O(n log n)`. Neither a general Par-to-Seq translation nor a language-class
separation follows from this payload bound; the general comparison remains
open.

### Sharing the Seq query clock across all continuations

`MacroPeg.CBV.SequentialSharedClock` removes the clock fields from every task
and continuation frame. The configuration has one current clock. Entering an
existing rule body at a valid cursor decrements it; returning through a scope
frame increments it. A zero-clock query, a missing rule, or an invalid cursor
produces the same undefined result as before and leaves the clock unchanged.
Thus a nested call restores both the caller environment and the clock needed
by its remaining computation.

The executable transition function is related to `SequentialSharedStack` by
`inflate`: it reconstructs a structural frame's clock from the current clock
and the number of intervening scopes. `step_commutes` proves exact agreement
of **every** transition on arbitrary configurations. `runs_inflate` and
`Runs.lift` transfer finite executions in both directions. `initial_runs`,
`result_iff`, and `accepts_iff` connect the new machine to the original Seq
semantics on unchanged `List Char` input. `drive_result_iff` checks the result,
the empty restored outer environment, and the restored initial clock for the
fuelled executable driver.

`step_clock_mass` proves the invariant

```
current clock + number of active scopes = initial clock.
```

Consequently `reachable_clock_bounds` bounds both quantities by
`(number of grammar rules + 1) * (input length + 1)` at every reachable state.
The global captured-character bound also transfers without duplication:
`reachable_captured_characters` still counts the current environment, every
suspended environment, pending argument heads, and current argument results.
The reconstruction function is used in proofs only; the runtime continuation
stack contains no per-frame clocks.

This eliminates one source of repeated integer metadata and bounds the number
of scope records, including scopes with empty environments. It does not yet
bound all structural frames or empty captures in this machine, compress
saved cursors and span endpoints, or implement a linear-space TM simulation.
The established complete TM bound remains `O(n log n)`, and the general
Par/Seq language-class question remains open.

### Counting every shared-machine frame and capture record

`MacroPeg.CBV.SequentialSharedRank` now relates every intermediate state of
`SequentialSharedClock` directly to the original `SequentialStack`.
`eraseStack` reconstructs the lexical environment and clock of each structural
frame while dropping scope frames. A scope return erases to a stuttering
step; every other transition is simulated by one original transition.
`step_erases` and `runs_erase` prove this for the actual machines, without
assuming that the new machine's states have an extra well-formedness type.

`eraseStack_length` gives exact accounting: the original stack length plus
the number of dropped scopes equals the new stack length. Combining the
original stack rank with clock conservation gives `stack_linear_bound`.
Writing `R` for the number of rules, `C` for `SequentialStackRank.codeBudget`,
`n` for input length, and `e` for the start expression, every reachable state
satisfies

```
number of all frames <= (R + 1) * (C + 1) * (n + 1) + sizeOf e.
```

This counts structural continuations, call continuations, pending argument
heads, and scope records, including those with no character payload.

`MacroPeg.CBV.SequentialSharedPayload` also bounds environments saved only
for restoration. Such an environment can be absent from the erased original
stack, so its validity cannot simply be read from that stack's payload
bound. `step_envs_ok` and `reachable_envs_ok` explicitly maintain all current
and suspended environments. Newly installed query environments come from the
original machine's argument-count invariant. Saved scope environments are
preserved by body entry and recovered by scope return.

Let `A` be the sum of grammar rule arities. `reachable_task_captures` and
`reachable_frame_captures` bound every retained environment by `A` entries.
`reachable_capture_records` therefore proves

```
number of all retained capture entries <= (number of frames + 2) * A.
```

`capture_records_linear` substitutes the linear frame bound. This count
includes **empty captures** as well as nonempty ones. Together with the
previous captured-character bound, it controls both the total word payload
and the number of word delimiters. `reachable_valid_captures` verifies that
every retained span satisfies `0 <= end <= start <= n`, including captures
in scope environments that disappear under erasure.

A complete linear-space simulation is still missing: span endpoints and saved
input cursors remain integer metadata, and bounded-space implementations of
the required operations have not been supplied. These results do not prove
a general reverse grammar translation or a language-class separation. The
complete TM upper bound established so far remains `O(n log n)`.

### An actual shared Seq machine with word-valued captures

`MacroPeg.CBV.SequentialSharedWords` now implements capture environments as
`List (List Char)`, rather than lists of origin-coordinate pairs. Parameter
matching uses `stripPrefix?` on the stored word. A successful argument creates
its word with `pre x p q`; pending argument continuations retain that word,
and scope frames retain the caller's word environment. Tasks and frames have
no capture-origin fields. The machine still uses one current environment,
one shared query clock, and the unchanged original input.

`atom_decode` equates parameter matching with matching a valid numeric span.
`step_commutes` proves that decoding a span configuration commutes with an
actual transition; its only validity hypothesis concerns the current capture
environment. No semantic operation is supplied as an oracle to the word
machine. `runs_decode` moves real initialized span executions to the word
machine. Conversely, `lift_step` and `runs_lift` show that every execution
reachable in the word machine has a matching initialized span execution.
Thus agreement covers intermediate states in both directions, not just a
selected successful run.

`original_result_iff` equates terminal results with the original
`SequentialStack` on the same `List Char` input. `accepts_iff` connects this
to first-order Seq observations. The executable driver's `drive_result_iff`
checks the result together with restoration of the outer empty word
environment and the initial clock, including failed and undefined
finite-clock results.

`MacroPeg.CBV.SequentialSharedWordSpace` transfers the resource bounds to
**every reachable word-machine state**. `decode_retained_words` counts every
copy in the current environment, suspended scopes, pending argument heads,
and current query or argument-result values. Consequently
`reachable_word_characters` bounds their total character count by input
length. `reachable_word_records` also counts empty words, and
`stack_linear_bound` counts all continuation records.

The capture stream codec stores each word as tagged characters followed by
one terminator, including a terminator for an empty word.
`decodeWords_encodeWords` proves a left inverse and
`encodeWords_injective` proves that no word sequence is lost.
`encodeWords_length` is exactly the total character count plus the number of
words. `capture_stream_linear` therefore gives a linear symbol bound for the
whole retained-word sequence, with an alphabet independent of input length.
This stream codec preserves the word sequence; it is not yet a codec for
environment grouping or the complete machine state.

Capture-origin endpoints are eliminated from the runtime word machine.
Saved input cursors still remain, and a complete state codec and bounded-space
implementations of the operations are missing. In particular, this does not
yet establish a linear-space TM simulation, a general Par-to-Seq grammar
translation, or a language-class separation. The proved complete TM bound
remains `O(n log n)`.

### Monotone saved cursors and a linear binary position stream

`MacroPeg.CBV.SequentialSharedCursors` extracts the current cursor, when
present, followed by the saved cursors in stack order. It includes expression,
argument, and query tasks, successful returned-value cursors, and positions
stored in choice, negation, repetition, and argument-head frames. It omits
failed or undefined result cursors, since those results store no position.
These are all the word machine's input-position fields: captured words and
scope environments no longer retain origin endpoints.

`reachable_chain` proves that this complete position list is nondecreasing
from the top towards the bottom of the stack, starting above zero and bounded
by the original input length, at **every reachable word-machine state**.
This includes intermediate argument evaluation and failed or undefined
results, not just successful terminal runs. The proof extracts position
bounds from the shared-machine scope certificates: each saved cursor is the
bound of its incoming continuation kind, and those bounds never decrease
along the stack. The initialized span/word execution correspondence transfers
the certificate to the actual word machine.

`MacroPeg.CBV.SequentialCursorChain` implements difference encoding and its
inverse. For a cursor list `p1 <= ... <= pk`, it stores the differences
`p1, p2-p1, ..., pk-p(k-1)`. Each difference is written as that many `true`
bits followed by one `false` delimiter. Zero differences require only their
delimiter. `Chain.restore`, `decodeDeltas_encodeDeltas`, and
`Chain.decode_encode` prove exact recovery on the increasing domain;
`Chain.encode_injective` proves that distinct valid position lists cannot
collapse under saturating subtraction.

The sum of differences is at most input length, so the entire position stream
uses at most `input length + number of stored positions` bits. There are at
most `number of frames + 1` stored positions. `cursor_stream_correct` verifies
the codec on every reachable state, and `reachable_cursor_bits` consequently
bounds the stream length by

```
input length + number of frames + 1.
```

`cursor_bits_linear` substitutes the fixed-program linear frame bound. This
removes the logarithmic factor from the **stored position stream** without
assuming that many equal or nearby saved cursors cost a binary integer each.

The capture-word stream and the position stream are still separate partial
encodings. They have not been assembled with syntax references, environment
grouping, frame tags, and the shared clock into a complete verified state
codec. In particular, the executable inverse returns cursor values; no proof
yet shows that all operations on the compressed streams run in linear TM
space. The established complete TM upper bound remains `O(n log n)`, and
neither a general reverse translation nor a Par/Seq language-class separation
has been proved.

### A lossless whole-state representation with linear stored length

`MacroPeg.CBV.SequentialSharedPool` transfers the original fixed-program
expression-pool certificates to every reachable word-machine task and frame.
Scope frames contain no syntax. The other frames recover their certificates
through scope erasure, including the argument tails and repetition bodies.

`MacroPeg.CBV.SequentialSharedStateCodec` now assembles all runtime fields.
Its logical input has three streams: control integers, ordered cursors, and
ordered capture words. Control records include task/frame tags, rule and
expression-pool references, argument-list lengths, environment lengths, and
the stack length. A reader consumes the exact number of words and positions
required by each record. `readTask_write`, `readFrame_write`, and `read_write`
prove recovery while preserving arbitrary tails of all three streams. Thus
the reconstruction restores word environments and field associations, rather
than just an ungrouped list of words or positions.

The complete `Packed` representation has four streams over fixed alphabets:

- one unary block for the shared clock;
- unary blocks for the control integers;
- the monotone difference encoding of the ordered cursor list;
- tagged characters with terminators for the ordered word list.

There are no unencoded runtime fields in `Packed`. The fixed expression pool
is determined by the grammar and start expression and is the codec context.
`reachable_decode_encode` proves exact recovery of the whole configuration
at every initialized reachable state. `encode_injective` proves that valid
states cannot collapse to one representation. The executable `packedStep`
decodes, performs an actual word-machine transition, and re-encodes;
`reachable_step_commutes` proves its agreement with that transition.

`MacroPeg.CBV.SequentialSharedStateBound` counts the complete representation,
including the control stream and all environment/grouping headers. Write
`P` for the expression-pool length, `D` for the fixed program budget, and `R`
for the number of rules. Its control budget is the source-only constant

```
B = D * (P + 1) + D + R + P + 10.
```

Argument tails have length at most `D`; expression identifiers are at most
`P`; live rule references are below `R`. The sum of environment-length headers
is charged to the already counted retained word records. Consequently, for
`K` frames and `W` retained word records, `control_cost` bounds the unary
control stream by `(K + 1) * B + K + 2 + W`. Both nonempty and empty words are
included in `W`, and the one stack-length header is also counted.

Combining this with clock, character, cursor, and frame bounds gives
`encoded_state_linear`: for every grammar `g`, start expression `e`, original
input `x`, and reachable word-machine state `c`,

```
length (encode (compilerNodes g e) c) <= linearFactor g e * (x.length + 1).
```

Here length is the total number of symbols in all four streams, each over an
alphabet independent of input length. The coefficient depends only on the
fixed source program. This is a complete stored-state size theorem, including
syntax references, frame tags, environment grouping, capture values, input
positions, and the shared clock.

It is still **not a complete linear-space TM simulation**. In particular,
`packedStep` materializes the decoded cursor list and configuration, and no
linear workspace bound is asserted for this implementation. The next
operational obligation is to implement the needed transitions on the
compressed streams with bounded workspace and connect that implementation to
the initialized TM model. The existing complete TM theorem remains
`O(n log n)`. General Par/Seq equality and language-class separation are still
open; a compact state representation alone proves neither conclusion.

### Direct compressed-cursor operations with intermediate tape bounds

`MacroPeg.CBV.SequentialCursorEdit` gives local algebra for the reversed
binary cursor stream, using symbol `1` for a true bit and symbol `0` for a
block delimiter. Removing a cursor merges its difference into the next block;
when no next cursor exists, it discards the obsolete data bits. Adding an
identical cursor inserts a zero-difference block. Removing the second cursor
preserves the first cursor while merging the second cursor's difference into
the following block. The algebra proves agreement with the original absolute
cursor lists on the previously verified increasing domain.

`MacroPeg.CBV.SequentialCursorEditMachine` implements these operations as
actual `Complexity.LProg` programs using copy, pop, push, tests, and loops:

- `dropBlock` removes the first cursor, merging the difference or clearing it
  at the end of the stream;
- `duplicate` duplicates the first cursor by adding one zero-difference block;
- `dropSaved` removes the second cursor while preserving the first.

The common `scan` moves only the leading unary block and stops at its
delimiter. None of these programs decodes the suffix to a list of integers or
receives a precomputed prefix-length counter. `scan_runs`, `dropBlock_runs`,
`duplicate_runs`, and `dropSaved_runs` prove the actual list executions with
`LenOK B` at **every visited instruction state**. Scratch starts and ends
empty, and unrelated tapes are preserved. Deletion fits the existing tape
capacity; duplication needs only one additional cell. `drop_current_runs`,
`duplicate_current_runs`, and `drop_saved_runs` connect the raw stream edits
to the intended absolute-cursor list edits.

`tape_runs` applies the existing list-to-tape compiler and proves execution
under `TFits B`, covering intermediate tape head positions and writes as well
as completed subroutine states. This supplies operational space evidence that
the previous materializing `packedStep` did not provide.

`MacroPeg.CBV.SequentialCursorEntryMachine` connects the duplicate operation
to actual word-machine entries for choice, negation, repetition, and argument
heads. `actual_step` checks the source transitions. `layout` holds the complete
packed state's cursor, control, clock, and word streams on six tapes, with
empty scratch tapes. `cursor_update` and `cursor_update_tape` update the cursor
component for every such initialized reachable entry with capacity

```
linearFactor g e * (input length + 1) + 3.
```

The other packed-state streams survive unchanged during this **cursor
component update**. The result is not yet the fully updated packed successor:
control and word changes still need their own implementation and composition.
The current-cursor decrease needed after successful input consumption also
remains to be implemented, as do complete dispatch, initialization, and the
final TM recognition connection. The general Par/Seq comparison remains open,
and the proved complete recognizer's space bound remains `O(n log n)`.

### Decreasing a cursor directly after successful consumption

`MacroPeg.CBV.SequentialCursorDecrease` gives the remaining local cursor
algebra. Decreasing the current cursor by one removes one true bit from its
head block and adds one true bit to the next difference block, if there is a
next saved cursor. At the end of the cursor list, the obsolete bit is simply
discarded. `lowerRest_relative` and `lower_current` prove that this direct edit
preserves all the saved absolute positions on the increasing domain.

`MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement` implements that edit
with actual list instructions. It removes the leading bit, scans the remaining
head block into scratch, removes the delimiter, conditionally adds a bit to
the suffix, and restores the delimiter and head block. It receives neither
the old absolute position nor a new result position as a runtime input.
`decrement_runs` and `decrement_current_runs` prove the encoded result, empty
scratch restoration, preservation of unrelated tapes, and `LenOK B` for every
instruction state using the **original capacity**.

`consume` repeats this edit using a unary counter of consumed characters.
`consume_runs` proves that consuming `used <= p` characters changes the first
cursor from `p` to `p-used`, preserves the saved cursor list, and empties both
the counter and scratch. `consume_tape` supplies the compiled `TFits B` tape
execution, covering all intermediate states. The counter's production by a
dynamic input/word matcher remains a separate obligation. For a source-fixed
length, `consumeFixed` creates the unary counter itself with fixed push
instructions; `consumeFixed_runs` proves the complete allocation, edit, and
cleanup within the same capacity. This is a cursor operation, not a literal
matching test.

`MacroPeg.CBV.SequentialAnyCursorMachine` connects the operation to the actual
`any` atom. Its program tests the last symbol of the compressed cursor stream:
a positive cursor ends in a true bit and takes the decrement branch; zero
ends in a delimiter and takes the existing cursor-deletion branch. Thus both
success and empty-input failure select their cursor update from the stream
itself, with no supplied success flag, consumed-length counter, or new result
position. `actual_step` checks the real Seq transition; `cursor_update` and
`cursor_update_tape` prove the corresponding cursor-component update for all
initialized reachable `any` states with capacity

```
linearFactor g e * (input length + 1) + 2.
```

The other complete packed-state streams remain on their tapes unchanged.
`decrement_constOK`, `consumeFixed_constOK`, and `finite_alphabet` also verify
the fixed pushed-symbol alphabet requirements. These programs still update
only the cursor component. Complete control/word updates, actual dynamic
matching, dispatch, initialization, and the final TM recognition connection
remain open, as does the general Par/Seq language-class comparison. The
proved complete recognizer's space bound remains `O(n log n)`.

### A complete compressed-state `any` transition

`MacroPeg.CBV.SequentialControlEditMachine` supplies the control-stream
operations that the cursor-only atom update lacked. `moveBlock` saves one
complete unary field, including its delimiter. `discardHead` and
`discardBlock` erase a field without decoding its value. `saveMany` and
`discardMany` repeat these operations a source-fixed number of times.
`replace` saves the header fields, discards an old record, writes a fixed new
record, and restores the headers. Field values are never supplied to the
program as a decoded integer array.

`replace_runs` proves the actual list execution, arbitrary suffix preservation,
scratch cleanup, and `LenOK B` at every instruction state. Capacity sufficient
for the initial state and the complete replacement also suffices for all
partial copies and intermediate states. `replace_constOK` verifies that only
the two fixed bit symbols are pushed, regardless of the field values.

`MacroPeg.CBV.SequentialAnyPackedMachine` combines this operation with the
direct cursor updates. The first two control fields, environment length and
stack length, are saved unchanged. The old task fields `[0, anyExpressionId]`
are discarded and replaced by `[3, 2]` for success or `[3, 1]` for failure.
The source cursor's leading bit chooses the branch **before** the cursor is
modified; neither a success flag nor a new position is supplied externally.
The clock, captured words, and continuation stack remain unchanged by this
atom, and both scratch tapes are empty again at completion.

`after_layout` proves equality with the whole successor representation,
including all four packed streams. `transition_runs` checks the actual Seq
step and constructs the complete encoded successor on the list machine.
`transition_tape` then supplies the compiled six-tape execution for every
initialized reachable `any` state, covering both success and empty-input
failure, with capacity

```
linearFactor g e * (input length + 1) + 2.
```

This bound covers all intermediate tape positions and writes, not just
stored endpoints. `finite_alphabet` verifies the complete transition's fixed
pushed-symbol alphabet. The initial and final space bounds come from the same
reachable-state theorem; the proof also verifies reachability of the actual
successor before using its bound.

This is the first complete transition for the compressed machine, rather
than only an update of its cursor component. It is still a subroutine entered
at a preloaded reachable `any` state. Other instructions, dynamic matching,
dispatch, standard-input initialization, and the complete TM recognition
connection remain to be constructed. General Par/Seq equality or separation
is unresolved, and the established complete recognizer bound remains
`O(n log n)`.

### Complete compressed structural entries

`SequentialControlEditMachine.incrementSecond` saves the first unary control
header, pushes one bit into the second header, and restores the first header.
`incrementSecond_runs` verifies the exact result, empty scratch restoration,
and every intermediate state's capacity using only the initial and final
length bounds. Header values are neither decoded nor supplied as program
parameters.

`MacroPeg.CBV.SequentialEntryPackedMachine` now implements complete structural
entries for ordered choice, negation, repetition, and nonempty argument lists.
Its program first duplicates the current cursor, replaces the old task by the
new task and continuation frame, and increments the stack-length header. The
environment-length header, shared clock, captured words, and previous stack
are preserved. Performing the replacement before the header increment lets
the final reachable-state bound also cover the intermediate control stream.

`before_control`, `after_control`, and `after_layout` identify the complete
source and target representations. `transition_runs` and `transition_tape`
construct the actual successor for each initialized reachable entry with
capacity `linearFactor g e * (input length + 1) + 3`, including all intermediate
tape states. `finite_alphabet` proves the fixed pushed-symbol alphabet. The
source expression and compiler node list determine each program template;
runtime environment and stack lengths are not built into the template.

These are still subroutines for preloaded reachable states, not a dispatcher
or a recognizer. The remaining instructions, dynamic matching, dispatch,
ordinary-input initialization, and complete recognition connection are open.
The established complete recognizer bound remains `O(n log n)`. General
Par/Seq equality or separation remains unresolved; even a completed linear
space upper bound would require a separate argument to settle that comparison.

### Complete compressed sequence, choice, and negation returns

`MacroPeg.CBV.SequentialReturnControlMachine` implements the inverse header
edit: `decrementSecond` saves the environment-length field, removes one unary
bit from the positive stack-length field, and restores the environment header.
`decrementSecond_runs` preserves the suffix and all other tapes, clears scratch,
and bounds every intermediate state by the initial capacity.

Its `dispatch` subroutine saves a fixed number of header fields and inspects
the result tag directly. Unary tags 0, 1, and 2 select undefined, failure, and
success continuations. The first positive bit is temporarily transferred
before the second test. Every branch restores the complete original source
and clears scratch before entering its continuation. `dispatch_runs` verifies
this behavior and composes arbitrary bounded continuation runs. Neither a
decoded tag nor a branch flag is supplied at runtime. `dispatch_constOK` also
checks the fixed pushed-symbol alphabet requirement.

`MacroPeg.CBV.SequentialReturnPackedMachine` composes that dispatcher with
complete returns from sequence, ordered choice, and negation frames. All nine
frame/result combinations are covered. Sequence retains a successful result
cursor when it starts the right expression. Choice retains the current result
cursor and removes the saved one after success, restarts the right expression
at the saved cursor after failure, and removes the saved cursor on undefined.
Negation removes both current and saved cursors after success, reuses the saved
cursor as its successful result after failure, and removes the saved cursor on
undefined. These are operations on the difference-encoded cursor stream;
absolute positions and the other saved positions are never decoded.

For each case, the control edit first decrements the stack-length header and
then replaces the task and top frame by the actual successor task. The
remaining continuation stack, environment, clock, and captured words survive.
`actual_step` checks the source machine transition, `after_layout` identifies
all successor streams, and `transition_runs`/`transition_tape` construct the
complete successor from every initialized reachable source state. Capacity
`linearFactor g e * (input length + 1) + 2` covers every intermediate tape
position and write. `finite_alphabet` checks the compiled return programs.
The programs depend on the source continuation syntax, not on its saved
position or its runtime result.

This supplies runtime **result-tag** dispatch within these return subroutines.
Whole-machine instruction selection, the other returns (including capture
creation), dynamic matching, ordinary-input initialization, and the complete
recognition connection remain open. The complete recognizer's established
bound remains `O(n log n)`, and the general same-input Par/Seq language-class
comparison remains unresolved.

### Copy an actual capture from the unchanged original input

`MacroPeg.CBV.SequentialCaptureCopyMachine` implements the character-copying
part of a successful argument-head return. The compressed cursor stream on
tape 0 begins with the current cursor `q` and the saved cursor `p`; its two
unary blocks have lengths `q` and `p-q`. Tape 6 holds the original input's
positive character symbols in their original order. Neither decoded cursor
values nor an externally computed substring is supplied to the program.

The fixed `program` transfers one original-input symbol per bit of the first
cursor block into a temporary suffix buffer. It saves that block's delimiter,
then transfers one symbol per bit of the next difference block, also copying
each character into the word tape. A zero delimiter is pushed before those
characters. Finally, both the original input and the complete cursor stream
are restored and the two scratch tapes are cleared. All unrelated tapes,
including the clock and control stream, are preserved.

`transfer_runs` proves the actual runtime loop for arbitrary lengths and
symbol lists. `capture_runs` composes both loops and restorations. The proof
covers empty captures, empty suffixes, and arbitrarily many remaining saved
positions. `original_input_runs` and `original_input_tape` prove that the
produced word is exactly `pre x p q`, in the same character order and with the
same delimiter as the existing retained-word codec (`wordCode_encode`).
Capacity bounds apply at every intermediate instruction and compiled tape
state, including both temporary source copies.

`withInput` extends the six packed-state tapes by the unchanged original
input and one reserved environment-prefix scratch tape. For every initialized
reachable state with those first two cursors, `reachable_buffer_runs` and
`reachable_buffer_tape` execute the same fixed copier with capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

`finite_alphabet` verifies the pushed-symbol requirement, and
`character_bound` gives a fixed Unicode symbol bound independent of the input.

The resulting word is currently appended to the top of the word tape as a
temporary buffer. This is not yet a complete argument-head return: the
retained-word order requires the new capture **below the current environment**.
`argHead_word_target` identifies the exact required target for every
environment and continuation stack: the reversed stack-word suffix, followed
by the new word, followed by the reversed current environment. A streaming
save/restore of the environment prefix using the environment-length header,
the final cursor and control edits, ordinary-input loading, other instructions,
and whole-machine selection remain to be composed. The complete recognizer
still has the established `O(n log n)` bound; general Par/Seq language-class
equality or separation remains unresolved.

### Complete capture creation and all argument-head returns

`MacroPeg.CBV.SequentialCaptureSpliceMachine` closes the environment-placement
obligation left by the temporary capture buffer. `scanWord` finds each word's
zero delimiter while moving its actual characters. `moveWord` also moves that
delimiter, so empty words remain distinct records. `saveEnv` reads the unary
environment-length header on the control tape: each bit transfers one complete
word from the word tape to the reserved environment scratch tape. Neither the
environment size nor its words are supplied as program constants.

`stash` restores the environment-length header, leaving the current environment
in scratch and the continuation's word suffix on the word tape. The existing
fixed copier then reads `pre x p q` from the unchanged original input. Restoring
the saved environment places the new word below it, exactly as required by
`argHead_word_target`. `splice_runs` and `splice_tape` verify this composition
for every environment, including empty words and an empty new capture. The
control header, complete cursor stream, input, and scratch are restored. The
initial and final word-tape capacities suffice for every intermediate copy,
including the environment scratch.

`MacroPeg.CBV.SequentialArgCapturePackedMachine` composes that word splice with
the remaining successful argument-head return. It removes the saved cursor,
retains the successful current cursor, replaces the expression-result task
by the remaining-argument task, and replaces the argument-head frame by the
new actual-word capture frame. The stack-length header stays unchanged because
one frame replaces another. The program depends only on the fixed source
syntax and compiler node list; runtime positions, environment values, and the
captured substring are not supplied to it. `withInput_update` checks the whole
successor representation, rather than just the changed components.

`MacroPeg.CBV.SequentialArgHeadPackedMachine` adds failure and undefined
returns and the actual runtime result-tag dispatcher. These two outcomes
remove the saved cursor and top frame, decrement the stack-length header, and
return the corresponding argument-result tag while preserving the environment
and existing captured words. The single fixed `program` reads the old result
tag from the control stream and selects all three outcomes without an external
branch flag. `actual_step` checks the original word-machine transition, and
`transition_runs`/`transition_tape` construct its complete encoded successor
for every initialized reachable argument-head return.

The eight-tape bounds include the unchanged original input and every
intermediate tape state, with capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

All three modules verify their fixed pushed-symbol alphabet requirements.
This completes the argument-head return subroutine, including real capture
creation under arbitrary environments. It is still entered at a preloaded
reachable state. The other instructions and returns, captured-word matching,
whole-machine instruction selection, ordinary-input initialization, and the
complete recognition connection remain open. The established complete
recognizer bound remains `O(n log n)`, and general same-input Par/Seq equality
or separation is unresolved.

### Assemble captured words into the argument environment

`MacroPeg.CBV.SequentialWordRotateMachine` provides `stashAfter`: skip a
source-fixed number of unary control fields, use the next field to save whole
words, and restore the complete control stream. Unlike the earlier environment
stash, it also permits an existing word prefix in scratch. Its loop reads the
actual word count, so neither the word count nor the words become program
parameters. `incrementAfter` changes a unary count below fixed header fields
without decoding it.

The fixed `program` rotates a pending captured word `w` into its position as
the first argument of `w :: W`. On the reversed word tape the source is

```
continuation words ++ wordCode w ++ wordTape E ++ wordTape W
```

and the target is

```
continuation words ++ wordTape E ++ wordTape W ++ wordCode w.
```

It first saves the evaluated arguments using their runtime count behind four
headers, then saves the current environment using its own runtime count. The
pending word is moved to separate scratch, both prefixes are restored, and
finally the word is restored above them. `rotate_runs` proves this exact
permutation, scratch cleanup, and every intermediate capacity using only the
initial word-tape bound. `discard_runs` instead deletes the pending word below
the current environment when the argument result is undefined or failure.
Empty words remain separate terminated records in both operations.

`MacroPeg.CBV.SequentialArgConsPackedMachine` composes successful rotation with
an increment of the argument count, a decrement of the stack count, and removal
of the capture-frame tag. The cursor, clock, original input, and current
environment survive. `before_words` and `after_words` match the actual retained
word ordering, and `transition_runs`/`transition_tape` construct the complete
encoded successor of the original Seq transition. The program has no grammar,
syntax, captured word, word count, or environment parameter.

`MacroPeg.CBV.SequentialArgConsReturnPackedMachine` adds the undefined and
failure returns and the runtime argument-result dispatcher. The same single
fixed program handles all three outcomes: success prepends the actual word
to the argument environment; undefined and failure delete it while preserving
the corresponding argument-result tag. All three decrement the stack count
and remove the pending capture frame. `transition_runs` and `transition_tape`
prove complete successor-state equality from every initialized reachable
capture-cons return, with every intermediate eight-tape state bounded by

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

The fixed pushed-symbol alphabet requirements are also verified. These are
complete return subroutines for preloaded reachable states. Call/query/scope
transitions, remaining instructions, captured-word matching, whole-machine
instruction selection, ordinary-input initialization, and the complete
recognition connection remain open. The existing complete recognizer still
has its established `O(n log n)` bound. General same-input Par/Seq language-class
equality or separation remains unresolved.

### Pass actual captured arguments from a call frame to its query

`MacroPeg.CBV.SequentialCallPackedMachine` implements the complete return
from a call continuation for all three argument outcomes. On success the
actual argument environment `W` and current position `q` become the query
`query i W q`, while the caller environment stays `E`. `other_streams` proves
that the packed words, cursor stream, and shared clock are exactly unchanged;
only control information changes. Undefined and failure argument outcomes
become the corresponding expression outcomes, also preserving those streams.

The successful program first removes the old call frame's tag and rule index,
then decrements the stack-length header, then replaces the argument-result
fields by the query tag and source-fixed rule index. Removing the frame first
avoids temporarily storing that rule index twice. The runtime argument-count
field is preserved as a unary stream throughout. The unsuccessful program
similarly removes the call frame and changes only the task tag, preserving
the actual undefined/failure result tag.

`success_runs` and `unsuccessful_runs` verify every intermediate list state,
arbitrary continuation suffix preservation, and cleared scratch. `program i`
uses the existing runtime argument-result dispatcher; no decoded result flag,
environment, argument count, or input position is provided to it. Its parameter
`i` is the fixed rule index of the source call template. Whole-machine selection
of such templates is still a separate construction.

`actual_step` checks the original Seq transition. `before_control` and
`after_control` identify both control streams; `control_only_update` and
`other_streams` verify the complete successor representation. `transition_runs`
and `transition_tape` construct that successor from every initialized reachable
call return, with all eight-tape intermediate states bounded by

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

`finite_alphabet` verifies the fixed pushed-symbol alphabet, independently of
the rule index's unary length. This completes the call-return subroutine;
it does not yet execute the query's rule body. Query entry must install `W`
as the current environment, save `E` in a scope frame, and decrement the clock.
Query/scope transitions, other remaining instructions, captured-word matching,
whole-machine selection, ordinary-input initialization, and the complete
recognizer connection remain open. The established complete recognizer bound
is still `O(n log n)`, and general same-input Par/Seq equality or separation
remains unresolved.

### Complete query entry, including zero clock and absent rules

`MacroPeg.CBV.SequentialQueryInstallMachine` moves the query's actual unary
metadata into the new environment and scope fields. The old current-environment
length becomes the saved scope's length; the query's argument count becomes
the new current-environment length; the stack count increases by one. The
query tag and rule-index fields are discarded and the fixed rule-body code
is written. Each saved unary field is moved back from scratch, so no decoded
length or input-dependent replacement prefix is supplied to the program.
`install_runs` verifies exact output, scratch cleanup, arbitrary continuation
suffix preservation, and every intermediate capacity using the initial and
final control-stream bounds.

`MacroPeg.CBV.SequentialQueryEnterPackedMachine` adds the shared-clock
operation and proves a complete positive-clock query transition. The actual
argument environment `W` becomes current, the caller environment `E` becomes
a scope frame, and the rule body starts at exactly the query's input position.
The word stream is unchanged: before entry it contains the task arguments,
current environment, and continuation words; after entry it contains the new
current environment, saved scope environment, and the same continuation.
`other_streams` verifies the word and cursor equalities. `clock_pop` verifies
the direct one-bit clock decrement, and `control_clock_update` identifies the
complete successor representation after both changed streams are updated.

`MacroPeg.CBV.SequentialQueryPackedMachine` supplies the complete query
program. The rule option and body identifier depend only on the fixed source
grammar and rule template. When a rule exists, the program tests the actual
unary clock tape before choosing entry or abort; no clock flag is provided.
A missing rule always selects abort. Abort reads the query's runtime argument
count behind four fixed headers, removes those task-owned words, restores
all control fields, removes the current cursor, and changes the task to an
undefined expression result. The caller environment, continuation stack,
clock, and original input survive. Empty words and an empty argument list are
handled by the same delimiter and unary-count loops.

`actual_step` checks the full source query operation for valid positions;
`reachable_step` obtains that validity from the established reachable cursor
chain. `transition_runs` and `transition_tape` construct the complete successor
for all initialized reachable query states, including zero clock and absent
rules, with every intermediate eight-tape state bounded by

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

All three modules verify their fixed pushed-symbol alphabet requirements.
This completes query execution from a preloaded reachable state. Scope return,
other remaining instructions, captured-word matching, whole-machine instruction
selection, ordinary-input initialization, and the complete recognition
connection remain open. The established complete recognizer bound is still
`O(n log n)`, and general same-input Par/Seq equality or separation remains
unresolved.

### Complete scope return with preserved return-value captures

`MacroPeg.CBV.SequentialScopeControlMachine` restores the saved environment
header while retaining the actual result fields. It removes the callee's
current-environment-length field, saves the positive stack count and the
result fields, removes the scope tag, and moves the saved environment length
into the new current header. The result fields are restored unchanged and
the stack count decreases by one. `restore_runs` covers arbitrary runtime
field values and continuation suffixes, with every intermediate capacity
bounded by the initial control-stream capacity. The program parameter is only
the fixed number of task fields, two or three.

`MacroPeg.CBV.SequentialScopeWordMachine` frees the callee environment without
freeing words owned by a successful argument return. Expression results and
undefined/failure argument results carry no task-owned words, so their current
environment can be deleted directly using its unary header. A successful
argument value first saves its actual word prefix on tape 5. Its current
environment is then saved on tape 7 and released, and the return-word prefix
is restored above the caller's saved environment. `stashReturnWords_runs`
uses an injective register permutation of the already verified streaming
stash; `preserveReturnWords_runs` and `result_words_runs` verify exact word
order, empty-word records, source preservation, scratch cleanup, and all
intermediate capacities.

`MacroPeg.CBV.SequentialTagDispatchMachine` generalizes restored-state unary
dispatch to a fixed finite tag bound. It saves a fixed number of headers and
reads the tag bits directly, transferring each inspected bit temporarily.
Each selected branch receives the complete original source state with empty
scratch. The code bound and branch templates are fixed before execution;
no decoded tag or external selector is provided. `dispatch_runs` verifies
every intermediate state and composes arbitrary bounded branch runs.

`MacroPeg.CBV.SequentialScopePackedMachine` combines these operations into one
fixed scope-return program. It reads the actual task kind (expression or
argument value), then the argument-result tag when needed. All expression and
argument result forms are covered, including undefined, failure, success,
and arbitrary successful return environments. The program frees only the
callee environment, restores the caller environment, preserves the complete
return value and input cursor, removes the scope frame, and directly increases
the unary shared clock by one. `actual_step` checks the original Seq operation;
`transition_runs` and `transition_tape` construct its complete encoded successor
from every initialized reachable scope return. All intermediate eight-tape
states satisfy capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

The fixed pushed-symbol alphabet is verified as well. This completes the
scope-return subroutine without restricting it to expression results or
assuming away argument-valued scope states. These remain subroutines entered
at preloaded reachable states. Other remaining instructions, captured-word
matching, whole-machine instruction selection, ordinary-input initialization,
and the complete recognition connection remain open. The established complete
recognizer bound remains `O(n log n)`, and general same-input Par/Seq equality
or separation is unresolved.


### Complete parameter matching from the actual environment and original input

`MacroPeg.CBV.SequentialParamPackedMachine` implements the complete `.param k`
transition on the same original `List Char` input. The program receives only
the source-fixed parameter index. Its environment, selected captured word,
current position, success flag, and resulting position are read or computed
from the actual tape streams. `actual_step` identifies the full Seq successor;
`transition_runs` and `transition_tape` construct its complete packed encoding
from every initialized reachable parameter task. Missing parameters, empty
words, exhausted input, and mismatching characters are included.

Seven modules supply the executable components:

- `SequentialSymbolDispatchMachine` compares two actual symbols using a fixed
  finite decision tree. Its source alphabet covers all Lean `Char` values via
  the established positive-character encoding and bound `0x110001`. The large
  fixed tree is a space construction; no small-code or efficient-time claim
  is made.
- `SequentialWordMatchMachine` compares a selected word against a prepared
  input suffix. Every matching character moves to a restoration buffer and
  directly decrements the difference-encoded current cursor. Its trace
  semantics agree exactly with `stripPrefix?`.
- `SequentialWordRestoreMachine` retains the successful cursor or removes the
  partially advanced current cursor on failure. Both actual word and input
  streams are restored, including any temporarily skipped environment words.
- `SequentialWordInputMachine` locates the actual suffix by counting the
  current unary cursor block, restores that cursor block, and composes the
  comparison and restoration. No decoded input position or substring is
  provided to its fixed program.
- `SequentialCountGuardMachine` tests a unary count against a source-fixed
  bound and restores the complete count before either branch. The runtime
  count has no fixed upper bound.
- `SequentialParamMatchMachine` uses that guard to check `k < environment
  length` before skipping exactly `k` word records. Delimiters handle empty
  words. The guard prevents a missing parameter from selecting a word owned
  by the continuation. All skipped words are restored after matching.
- `SequentialParamPackedMachine` reads the computed success bit and replaces
  the old task fields with the actual expression return value. The clock,
  current and saved environments, continuation, saved cursors, original
  input, and empty scratch tapes agree with the complete successor encoding.

Every intermediate eight-tape state satisfies capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

The fixed pushed-symbol alphabet and standard-axiom dependencies are audited.
This closes the parameter lookup and captured-word matching subroutine; it
still starts from a preloaded initialized reachable encoded state. Other
remaining instructions, whole-machine instruction selection, ordinary-input
initialization, and the complete recognition connection remain open. The
established complete recognizer bound remains `O(n log n)`. General same-input
Par/Seq equality or separation is unresolved.


### Fixed-source reads, remaining static entries, and the common eight-tape layout

`SequentialTokenMatchMachine` executes a source-fixed list of symbol guards
against the actual input suffix. A successful guard moves one actual character
into the restoration prefix and directly decrements the compressed cursor.
Exhausted input or a false guard removes the current cursor. Both success and
failure restore the complete input. `SequentialTokenInputMachine` prepares the
suffix by reading the actual cursor, composes these tests, and returns the
computed result bit and cursor with the original input and scratch restored.
No literal or decoded input position is provided on a runtime buffer.

`SequentialReadTests` identifies the test programs with the original semantics
of `eps`, `any`, `chr`, `range`, `lit`, `dbg`, and directly evaluated `lam`.
`literal_run` proves exact `stripPrefix?` agreement for every literal and input;
`atom_result` includes empty input, empty literals, and every valid input
position. Unicode characters and inclusive codepoint ranges are unrestricted.
The source-fixed literal is represented by code guards, so its length does not
add a tape-space term. `SequentialReadPackedMachine.transition_runs` and
`transition_tape` construct the complete encoded successor for all these
primitives from initialized reachable states.

`SequentialStaticPackedMachine` supplies complete entries for sequence,
named call, empty argument list, unresolved `callParam`, and `invoke`. The
source grammar determines whether a named rule exists and whether its arity
matches the source argument list. A valid call installs the actual argument
task and its cursor-free call frame. Missing rules and arity mismatches return
failure and remove the current cursor. Empty arguments return the actual empty
capture environment and unchanged position. Higher-order forms keep exactly
the original word machine's failure (`callParam`) or undefined (`invoke`)
behavior. Sequence installs its left expression and cursor-free continuation.
Every branch preserves the original input, captured words, shared clock, and
unaffected continuation and environment fields.

`SequentialEightTapeMachine` injectively renames the existing six-register
programs onto the common eight-register layout. `lift_runs` preserves the
complete endpoints and all intermediate capacity bounds while retaining the
original-input tape and extra scratch tape. `entry_runs` covers the earlier
choice, negation, repetition, and nonempty-argument entries; `return_runs`
covers sequence, choice, and negation returns. These results use the same
capacity as the new primitive and static programs:

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

The pushed-symbol alphabets and 27 new public theorem dependencies are
audited. The remaining compressed instruction gap is repetition return:
its successful branch must inspect the actual difference between current and
saved cursors to decide progress, then either reenter or return undefined.
Whole-machine instruction selection, ordinary-input initialization, and the
complete recognition connection also remain open. The established complete
recognizer still has its `O(n log n)` bound. Neither a reverse same-input
grammar translation nor a genuine Par/Seq language-class separator has been
proved.


### Complete repetition return and runtime selection of every active task

`SequentialCursorProgressMachine` saves the first cursor block, inspects the
actual next difference block, restores the complete original cursor stream,
and enters the progress or nonprogress continuation. The first bit directly
tests whether the saved position exceeds the current position. No decoded
position or externally supplied progress flag is passed to this program.

`SequentialStarPackedMachine` completes repetition return for all three actual
expression result tags and both success-position cases. Undefined removes the
saved position and propagates undefined. Failure returns success at the saved
position. A consuming success removes the saved cursor and reenters the same
star expression at the actual current position. A nonconsuming success removes
both cursors and returns undefined. The reachable cursor chain ensures that
nonprogress is exactly equality, rather than a backwards move. The fixed
program selects the result tag and the cursor comparison from the actual
source tapes. `transition_runs` and `transition_tape` construct the complete
encoded successor, including the continuation count and task fields, while
preserving the environment, captured words, shared clock, original input, and
empty scratch tapes. This closes the remaining individual compressed
repetition-return instruction.

`SequentialExpressionDispatchMachine` enumerates fixed instruction programs
for every source expression constructor. A single fixed selector reads the
actual expression id behind the environment, stack, and task-kind headers.
Reachable syntax-pool membership proves that the id selects the actual
expression, including structural entries, checked calls, higher-order fallback
forms, reading primitives, and captured parameters. Every decision restores
the whole source state before its selected instruction begins.

`SequentialArgumentsDispatchMachine` reads the actual argument-list length and
each expression id before selecting the complete empty or nonempty argument
start program. The length bound is the existing source-fixed program budget;
the stored ids belong to the fixed syntax pool. All decoded list alternatives
are branches of the finite source program. No runtime list is supplied to the
program by its specification. This can produce large source-dependent code;
no compact-code or efficient-time bound is asserted. The selector's workspace
remains bounded by the original control stream.

`SequentialQueryDispatchMachine` reads the actual rule id, whose source-fixed
bound follows from the established reachable-state invariant, and invokes the
complete query program. Its zero-clock and positive-clock behavior therefore
remain actual tape decisions inside the selected program.

`SequentialActiveDispatchMachine` reads the task-kind field and composes these
three selectors. Its single source-fixed eight-tape program performs the
complete original Seq step from every initialized reachable expression,
argument-list, or query task. Selection and execution both satisfy capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

Fixed finite alphabets covering the original Unicode character encoding and
33 new public theorem dependencies are audited.
The active-task theorem explicitly excludes return values. Although individual
return instructions now have complete templates, selection among continuation
frames and their payloads still has to be assembled into a common program.
Ordinary-input initialization, the complete execution loop and halt handling,
and the recognition connection also remain open. The established complete
recognizer bound is still `O(n log n)`. General same-input Par/Seq equality or
separation remains unresolved.


### Complete step selection and the packed evaluation loop

`SequentialSyntaxListDispatchMachine` generalizes inline syntax-list selection
to any fixed number of headers and any source-fixed continuation family. Its
program reads the actual list length and ids, restoring the complete source
before each subsequent selection or continuation. The previous argument-start
dispatch now uses this same decoder. `SequentialArgHeadDispatchMachine` uses
it below five headers to select the actual argument tail retained by a frame.

`SequentialRefReturnDispatchMachine` reads saved syntax ids for sequence,
choice, and repetition returns. Reachable pool certificates identify the exact
saved expression, including the body of a repetition. `SequentialReturnFields`
proves common control layouts for every expression and argument return form
and every continuation tag.

`SequentialExpressionReturnDispatchMachine` selects the actual continuation
for expression results: sequence, choice, negation, repetition, argument-head,
and scope returns all use their complete instruction programs. The source
step equation rules out mismatched return/frame forms. No decoded frame is a
program argument.

`SequentialArgumentsReturnDispatchMachine` first reads the actual result tag.
Undefined and failed argument values have four fields before the frame tag;
successful values have five, including their actual capture count. The
selected frame dispatcher therefore skips the correct header length, retains
all returned words, and chooses argument-cons, named-call, or scope return.
Call return additionally reads the actual rule id behind the frame tag; its
fixed bound follows from the existing reachable-frame invariant.

`SequentialStepDispatchMachine` combines these return selectors with the
active-task selector. Its one source-fixed eight-tape program constructs the
complete encoded successor for **every defined step from every initialized
reachable state**. Task kind, result form, frame kind, rule id, and syntax
payloads are all selected from the actual tapes.

`SequentialFieldPresenceMachine` checks a unary field below a fixed header
prefix and restores the entire control stream before either continuation.
`SequentialRunningMachine` uses this to inspect the stack count and, when the
stack is empty, the task kind. It appends one running flag on tape 7 while
preserving all original fields and other scratch.

`SequentialPackedLoopMachine` checks that flag, removes it before each complete
step, and computes the next flag afterward. Consequently each instruction
still receives precisely its established empty-scratch interface. `loop_runs`
and `run_trace` simulate actual finite source executions without putting their
length in the program or on a tape. `evaluate_runs` uses the existing actual
initial-to-final execution, so the same fixed loop always terminates with the
exact original `SequentialSpanRecompute.run` result from the preloaded packed
initial state. `evaluate_tape` transfers the entire execution to actual tape
programs. The temporary flag is cleared at the end; the original input and the
complete encoded final configuration are retained.

All selection, instruction, and loop intermediates satisfy capacity

```
(linearFactor g e + 1) * (input length + 1) + 3.
```

The fixed finite alphabets cover the original Unicode encoding; 43 new public
theorem dependencies are audited against the standard axioms. Code may depend
strongly on the fixed grammar; no efficient-time or compact-code bound is
claimed here. Ordinary-input initialization and mapping the final encoded
result to a standard accepting/rejecting halt still need to be connected.
Thus this closes linear-workspace **evaluation from a preloaded packed initial
state**, not yet the complete ordinary-input linear-space recognizer. The
previous complete recognizer bound remains `O(n log n)`, and general same-input
Par/Seq equality or separation is unresolved.


### Standard-input linear-space recognition and the language-class consequence

`SequentialPackedInitMachine` generates the real initial packed state from
only the original character word on its input tape. A scan generates the
current unary position and shared clock, installs the fixed initial control
fields, and restores the input. Neither the input length nor a precomputed
initial configuration is supplied. `initial_shape` identifies all eight
streams with the established whole-state codec; `initialize_runs` bounds all
intermediate initialization states by the packed evaluator's same capacity.

`SequentialPackedHaltMachine` reads the actual final result tag and, for a
successful result, tests the actual compressed remaining position. Only
success at position zero accepts. `recognize_halts` composes initialization,
the entire packed evaluation loop, and that accepting/rejecting halt for every
original character list. `answer_iff` identifies the answer with the original
first-order Seq observation. This interface starts with the character word on
tape 6 and empty other lists, so a standard-input bridge is still needed for
a conventional binary-input TM statement.

`SequentialPackedBinaryLoader` supplies that bridge for ordinary a/b words.
The standard input bit list becomes exactly one a/b character per bit, with
all temporary buffers cleared. It does not repeat, pad, or annotate the input.
`SequentialPackedBinaryInputMachine` composes the standard `initP` tape
normalizer, loader, packed initialization, complete evaluation, and final halt.
`machine` constructs a fixed **eight-tape finite-alphabet Turing machine**
which decides the original Seq language on the ordinary a/b word. Its space
bound covers every tape and every intermediate action, including loading and
normalization:

```
space(g,e,n) = (linearFactor g e + 1) * (n + 1) + 3
            <= (linearFactor g e + 4) * (n + 1).
```

Thus the prior standard-input `O(n log n)` bound is improved to `O(n)` for
these binary word languages. The character-list initializer and evaluator
also retain their unrestricted Unicode semantics; this standard TM theorem
specifically uses the ordinary a/b restriction.

`Complexity.SpaceLinear` records deterministic linear space with the standard
binary input convention. `Shallot.PegSeparation.binary_seq_in_linear_space`
connects the complete recognizer to the language class, and
`binary_seq_in_P_and_linear_space` combines it with the established inclusion
in Par and binary `Par = P`:

```
binary first-order CBV-Seq <= P intersect DSPACE(O(n)).
```

`binary_reverse_requires_P_linear_space` and
`original_reverse_requires_P_linear_space` show that a reverse inclusion,
including one on the same original character languages, would put every P
language in deterministic linear space. The conditional theorem
`P_outside_linear_space_separates_original` obtains a genuine original-language
separator if a P language outside that space class is supplied. Its space
lower-bound hypothesis remains explicit and unproved. The new recognizer
therefore strengthens the necessary condition for equality; it does **not**
settle equality or construct an unconditional Par/Seq separator.

The root imports and 27 new public theorem axiom guards include initialization,
all halting cases, the standard-input machine, and the class consequences.
All audited dependencies are standard Lean axioms.

### Recursive reverse compilation with any number of unbounded prefix captures

`PrefixFamilyFusion` removes the two-argument and common-arity restrictions of
`PrefixPairFusion`. Its templates are arbitrary finite rule lists, with a
separate arity for each rule. For a call with chunk parsers `A0,...,Ad-1`,
the generated Par arguments are the cumulative parsers

```
F(A0, A0 A1, ..., A0 ... Ad-1).
```

The Seq target instead calls `F(A0,...,Ad-1)` consecutively. In a source
rule of arity `d>0`, the body begins by replaying parameter `d-1`; in the
Seq target this replay disappears. Each later source parameter `k` is
reconstructed by the target expression `y0 ... yk`. Zero-argument rules
use an empty replay. Nested calls in arguments and bodies undergo the same
transformation. The number of rules and each rule's arity are preserved.

`words` and `parsers` implement the cumulative value and syntax operations.
`arguments_factor` proves that the actual Par evaluation of the cumulative
parsers returns the cumulative words of the actual consecutive argument
run. This covers the first finite failure and undefined evaluation, as well
as successful empty chunks. `arguments_prefix` identifies the concatenation
of the chunks with exactly the consumed original input. `parameters_eq`
proves that all original captured values remain available through their
views, without a finite value palette or a capture-length bound.

`tables_shifted` connects every recursive table approximation at the source
and target body positions. `evaluator_eq`, `decide_eq`, and `observations_iff`
then preserve the complete partial semantics, including finite failure and
absence of a finite result. `language_translation` constructs a fixed
first-order Seq grammar and root for the same original character language.
No input encoding, repetition, padding, or input-length restriction occurs.
Missing rules, mismatched call arities, empty input, predicates, and
repetition are included in the evaluator proof.

`PrefixFamilyTestFusion` also extends the replay-test construction to this
whole variable-arity family. Its source bodies test the longest-prefix
replay followed by their tails. The target moves tests to call sites,
captures all adjacent chunks, and restores the caller's original position
after the test. `render_commute` proves that call-site test movement and
the prefix compiler commute; `observations_iff` and `language_translation`
connect the actual fixed grammars, including recursive calls.

These are reverse translations for **generated prefix-factored source
grammars**. They do not transform arbitrary independent Par argument
expressions into parsers for their successive prefix differences, reorder
arbitrary captures, or normalize arbitrary bodies to a longest-prefix replay.
The earlier value-level representation theorem for arbitrary overlapping
captures does not supply those operational transformations. Thus every
capture in this fragment can now be unbounded, and rule arities can vary,
while general same-original-language Par/Seq equality or separation remains
unresolved. The root imports and 22 new public axiom guards cover both
compilers and their semantic connections.

### Discovering runtime chunks from independent greedy scanner arguments

`NestedScannerArguments` supplies an operational factorization, rather than
assuming already evaluated capture words or syntactically cumulative parser
arguments. `choice A` reads one character from a fixed finite character list
`A`; `scan A` greedily repeats it. For static lists `A` included in `B`,
`scan_absorb` proves the actual evaluator identity

```
(scan A) (scan B) = scan B.
```

The second scan resumes at the first scan's actual endpoint. `scan_eval`
proves its complete semantics on every valid suffix of every original
Unicode character input, by the corresponding `dropWhile` result. Empty
character sets, empty captures, stopping characters outside either set, and
EOF are covered. The inclusion condition concerns only the fixed syntax:
`covers_iff` verifies a finite Boolean check, and `cumulative_nested` constructs
an increasing family from any finite list of character sets by cumulative
union. It requires no input-dependent advice.

For any number of character sets in inclusion order, `parsers_collapse` and
`independent_arguments` prove that independent Par arguments return exactly
the same values as their cumulative-parser expansion. Thus, for example,

```
F(a*, (a/b)*, (a/b/c)*)
```

can use the preceding prefix-family compiler without supplying difference
parsers or capture values. On input `a^n b^m c^k z`, the original argument
values are `a^n`, `a^n b^m`, and `a^n b^m c^k`; consecutive target scans
capture `a^n`, `b^m`, and `c^k`. None of `n,m,k` has a fixed bound.

`NestedScannerFusion` connects this identity to whole recursive grammars.
Its actual source calls retain the independent scanner expressions; source
rule bodies begin with the last parameter's replay and then their template
tail. Rules may have different arities, including zero. The Seq target is
an actual `PrefixFamilyFusion.seqGrammar`, with cumulative parameter views.
`evaluator_of_tables` and `tables_eq` prove the normalization under all
recursive approximations. `observations_iff` and `language_translation`
preserve all finite observations and the whole-input language on unchanged
original strings. No totality assumption is imposed on recursive bodies.

The `Test` namespace also handles source bodies under positive lookahead.
`source_commute` and `wrapped_eq` move these tests to call sites while keeping
scanner arguments intact. `Test.observations_iff` and
`Test.language_translation` connect the corresponding fixed Seq target,
retaining the captured values inside the test and restoring caller positions.
Both compilers include failure, undefined recursive evaluations, missing rules,
and arity mismatches.

This closes argument discovery for independent, inclusion-ordered greedy
scanners. It does not handle arbitrary recursive argument parsers, arbitrary
regular parser residuals, captures forwarded as argument expressions,
non-nested or differently ordered scanner families, or source bodies without
the leading replay (or replay test). These remain mathematical obligations;
the general Par/Seq language-class question is unresolved. Root imports and
20 new public theorem axiom guards cover the operational factorization and
both language-preserving compiler connections.

### Runtime stopping-order selection for arbitrary pairs of greedy scanners

`ScannerFrontier` removes the inclusion-order premise at the operational
argument interface for two independent scanners `scan A` and `scan B`.
Their static character sets may overlap without either containing the other.
First scan their intersection. At its stopping point, test whether `A` can
continue. If it cannot, `A` is the shorter capture (ties take this branch);
otherwise `B` is the shorter one. `guard` implements this as an actual
positive lookahead over the common scan and a negative character test.
`guard_eval` proves its exact Boolean result on every original input and
valid position, including EOF and coincident endpoints.

`sequential_arguments` proves that consecutive scans of the intersection
and the remaining longer scanner produce the actual disjoint runtime chunks
`u,v`. `parallel_arguments` proves that the original independent Par capture
values are `[u,u++v]` or `[u++v,u]` according to the computed stopping order.
The proof imposes no bound on capture lengths and supplies no previously
evaluated capture values or endpoint advice to the generated syntax.

`dispatch A B left right` is a fixed first-order Seq expression which runs
that guard and selects one of two fixed rule slots. Both selected calls
capture the chunks using their ordinary argument expressions. The negative
guard on the second branch prevents failure of the chosen call from falling
through. `dispatch_eval` proves the complete partial result for arbitrary
recursive tables: success, finite failure, and undefinedness all propagate.
`stopping_order_switches` gives one fixed non-nested pair with both stopping
orders after arbitrarily long shared `a` prefixes, so the bit is genuinely
input-dependent rather than a static inclusion choice.

`body true e` and `body false e` are two input-independent body variants
using cumulative parameter views in the original order. `body_eval` preserves
all first-order uses of both values at the advanced position, through the
same grammar, strategy, and recursive table. `dispatch_body_eval` connects
the actual guard, capture, query entry, and installed variants to arbitrary
first-order body evaluation at every table clock.

This closes runtime discovery and finite-control selection for a non-nested
scanner pair. It is **not** yet a whole recursive Par-to-Seq compiler:
`call_of_body_relation` retains an explicit source/target body-table relation,
and `body_eval` itself does not change the strategy or recursive call targets.
A generated grammar must install and route the two rule variants, prove their
recursive table relation, and reconcile the source body entry position.
Arbitrary argument parsers, arbitrary numbers of unordered endpoints, and
source bodies without a suitable replay remain further obligations. General
same-original-language equality or separation is still unresolved. Root
imports and 15 new public axiom guards include the runtime selector, actual
query entry, and the explicit conditional call bridge.

### Closing the recursive compiler for non-nested scanner pairs

`ScannerPairFusion` closes the recursive body-table relation left explicit
by `ScannerFrontier.call_of_body_relation` for a concrete replay-shaped
source family. A finite specification assigns two static character sets and
one template tail to each source rule. The character sets have no inclusion
or ordering requirement. Template `call i []` becomes the source call
`F_i(scan A_i, scan B_i)`; its two arguments are independently evaluated at
the caller's original position. Other nonempty template call argument lists
and higher-order template forms are explicitly mapped to failure.

Each source body uses the actual frontier guard to replay the longer of its
two captured parameters, then evaluates its rendered template tail. The Seq
compiler emits two arity-two rules per source rule. Their bodies use the two
cumulative capture views, while every translated call uses the fixed runtime
dispatch to select the appropriate rule and capture the adjacent chunks.
`par_rule_count`, `seq_rule_count`, `par_rule`, and `seq_rule` verify the actual
finite rule layout: N source rules become exactly 2N target rules, at slots
`2*i` and `2*i+1`. The generator depends only on the finite specification and
root template, not on the input or evaluated capture values.

`Shifted` records both possible original parameter orders and the actual
frontier guard result. `tables_shifted` proves that relation for every
recursive approximation, using the installed source replay and target views.
`evaluator_eq` consequently preserves every three-valued expression result
at every clock, including recursive calls inside sequencing, prioritized
choice, repetition, and predicates. The body-table relation is now a theorem
of the generated grammars, rather than a remaining compiler hypothesis.

The different rule counts give different decision-procedure stabilization
bounds. `stable_result_eq` proves that equal evaluators at every clock have
equal stable results without assuming equal bounds. `decide_eq`,
`observations_iff`, and `language_translation` then connect the actual fixed
first-order grammars on every original character string, including empty
input, finite failure, and absence of a finite observation. Runtime captures
have no length bound and retain both original values for later uses in the
tail, including around further recursive calls.

This is a complete reverse compiler for the **specified scanner-pair source
family**. It does not normalize an arbitrary Par grammar into that family.
In particular, each rule has one fixed scanner pair, all generated source
bodies begin with a dynamically selected longest-prefix replay, and calls
with arbitrary parser arguments or forwarded captures are outside the
interface. General argument residualization and arbitrary source body entry
remain unresolved, as does the main same-original-language Par/Seq comparison.
The root import and 15 new public axiom guards cover actual rule generation,
recursive correspondence, differing stabilization bounds, and language
preservation.

### Finite-state residual discovery beyond one-state character scans

`StatefulScanner` adds a finite-state prefix-scanner model and an actual
first-order PEG generator. A state has an ordered finite list of character
transitions; each transition consumes exactly one character. The scanner
stops at EOF or the first missing transition. Duplicate character entries
use the first matching transition, consistently in the model and generated
syntax. This model is not asserted to cover all regular PEG argument syntax
or arbitrary backtracking argument parsers.

`run_after_prefix` proves the residual law: after consuming a prefix, resume
in the state reached by that prefix. `branches` generates guarded character
transitions and named zero-argument calls. The negative guards ensure that
a failed final-state test in a recursive successor cannot fall back to a
shorter, previously visited stopping state. `query_eval` proves the actual
recursive evaluator in any grammar containing the generated block. A clock
of at least the remaining input length plus one suffices; this is a proof
bound, not fuel or advice added to the input.

`StatefulScannerFamily` installs all stopping-state selectors together in
one fixed grammar. A scanner with N states uses exactly N² generated rules.
`grammar_rule` verifies the real addresses. `entry_eval` and
`entry_observation` prove that each selector consumes the scanner's actual
prefix exactly when its fixed candidate state is the real final state;
otherwise it fails finitely. `probe_eval` and `probe_observation` give the
input-restoring tests. Both CBV strategies and all original character strings
are included. `capture_eval` connects the generated selector to actual Seq
argument evaluation and the original captured prefix.

`StatefulScannerBridge` identifies the existing character-set scanner with
the one-state instance, including actual compiled observations. Its two-state
counterexample `resetting_changes_result` shows why the residual state cannot
simply be discarded: consuming an initial `a` enables an arbitrarily long
following `b` scan, whereas restarting in the initial state stops immediately.

`StatefulScannerProduct` generates a finite synchronized product of two
independent scanners. It consumes their common prefix until either scanner
has no next transition. `next_joint` preserves ordered transition lookup;
`run_product` identifies the generated product with simultaneous scanning.
`common_prefix` proves that one actual consumed word reaches both recorded
states, and `residual_runs` proves that both original scans resume exactly
from those states and the common suffix. `frontier_stops` includes tied
endpoints. The state-pair encoding and all reached states are finite static
control, while the consumed prefix can have unbounded length.

`common_entry`, `common_probe_observation`, and `common_capture` connect this
product to the actual fixed PEG selector grammar. Every candidate pair has
fixed rule slots: the right pair captures the actual common prefix, wrong
pairs finitely fail, and the probe restores the caller position. Neither
reached states nor prefix lengths are supplied as input-dependent advice.
For source scanners with N and M states the product has N*M states, and its
complete selector grammar has (N*M)² rules, all fixed before reading input.

These results provide runtime residual-state discovery and common-prefix
capture for finite-state arguments, beyond the earlier stateless scanners.
They do not yet assemble both residual scans, the finite rule variants, and
recursive body correspondence into a finite-state extension of
`ScannerPairFusion`. General recursive argument parsers and arbitrary source
body entry remain further obligations. General Par/Seq equality or separation
is unresolved. Four root imports and 28 new public axiom guards cover the
actual generators, all-input observations, residual identities, and Seq
capture connections.

### Combining stateful selectors and residual captures in one grammar

`StatefulPairArguments` installs the common-state selector family and both
ordinary residual scanners together, followed by arbitrary user rules.
Its helper prefix has exactly `(N*M)^2 + N + M` rules. `common_rule`,
`left_rule`, and `right_rule` verify the actual addresses, and
`grammar_firstOrder` preserves first-order user tails. The new
`StatefulScanner.block_rule`, `block_firstOrder`, and `entry_of_layout`
connect a generated scanner block to its entry call when other blocks and
user rules are installed in the same grammar.

`common_eval`, `left_eval`, and `right_eval` prove the three real entries
against their exact finite-state results. `arguments_eval` then connects the
common selector and the appropriate residual entry to actual consecutive Seq
argument evaluation in this combined grammar. Empty chunks and tied stopping
positions are included. `first_remainder` proves that the scanner selected
as shorter stops exactly at the common frontier. `capture_reconstruction`
identifies the independently evaluated original Par argument values with
`[u,u++v]` or `[u++v,u]` from the Seq chunks, in the original parameter order.
There is no capture-length bound or precomputed value input.

`caseGuard` is an actual input-restoring PEG test for one candidate residual
state pair and one stopping order. It combines the compiled common-state
selector with a character-transition test at that frontier. `caseGuard_eval`
proves that exactly the actual control passes and every wrong candidate
finitely fails. `controls` enumerates all state pairs and both orders using
only the fixed scanner state counts; `controls_mem` proves exhaustiveness.

`dispatch` checks these candidates and calls the selected arity-two user
rule with the actual two capture parsers. Its negative guards prevent a
chosen user-rule failure from falling through to another candidate.
`dispatch_eval` and `complete_dispatch_eval` prove the complete partial
result for every user-rule result, including failure and undefinedness.
Their user-rule premise is the actual syntactic lookup and arity, not a
semantic simulation hypothesis or input-dependent control advice.

`complete_dispatch_body_eval` also connects query entry to two installed
capture-view body variants. Residual states select the parsers; the user body
needs only the original capture order, so two body variants suffice. The
proof runs the real guard, both captures, and named user query in one grammar,
then preserves every first-order use of the reconstructed values in the body.
It retains the explicit clock bound needed for the lexical helper queries.

This closes the combined operational argument interface and user-body entry
for finite-state scanner pairs. It does **not** yet prove a whole recursive
Par-to-Seq grammar transformation: recursive user-body correspondence and
its interaction with the helper-query clocks remain to be established.
Arbitrary recursive/backtracking argument parsers and arbitrary source body
entry are also outside this interface. The general same-original-language
comparison remains unresolved. Root imports and 26 new public axiom guards
cover installed block layouts, runtime case selection, capture reconstruction,
complete dispatch, and actual body entry.


### Separating scanner rounds from user-rule rounds

`CBV/ClockFreezing.lean` defines a frozen table iteration for any actual
grammar: selected helper rows are fixed at their physical table values at a
finite floor `B`, while all other rule rows iterate their actual bodies.
The grammar itself is unchanged. The construction is an analysis of its
finite evaluation, not an input-dependent grammar or additional advice.
Writing `P_k` for physical tables and `F_k` for frozen tables, the proofs give

```
F_k ≤ P_(B+k)
P_k ≤ F_k           (when the selected physical rows are stable after B)
```

Here the order preserves every defined result, both success and finite
failure. Consequently `defined_iff`, `stable_defined_iff`, and
`observations_iff` transfer finite outcomes between frozen evaluation and
the actual grammar semantics. Undefinedness is not treated as finite failure.
`frozen_user_step` also proves that a non-helper rule spends exactly one
user round evaluating its actual installed body.

`CBV/StatefulScannerStability.lean` discharges the stability condition for
the previously generated combined grammar. Every common-selector and left
or right residual-scanner row is stable after `x.length + 1` physical rounds.
This is equality of entire rows at every capture environment, for arbitrary
recursive user tails; it is not a stability hypothesis on an external
lexical oracle. The proof includes zero-state edge cases where applicable,
all input positions and the selectors' finite failure results.

`CBV/FrozenPairArguments.lean` then proves exact common/left/right entry,
Seq argument, independent Par argument, reconstruction, guard, and complete
dispatch contracts at **every** frozen user stage, including stage zero.
The installed-body dispatch theorem requires both body slots to lie outside
the helper prefix and connects stage `k+1` dispatch directly to stage `k`
evaluation with the original captured values. It has no scanner-depth bound
on `k`; the physical/frozen comparison supplies the required physical rounds
when returning to the real grammar.

This removes the helper-query clock obstruction from the finite-state
argument/body interface. It still does not establish the recursive user-rule
correspondence of a full finite-state Par-to-Seq compiler. That correspondence,
normalization of general recursive/backtracking arguments, and arbitrary
source body entry remain open. In particular, the general same-original-
language equality or separation has not been proved. Root imports and 29
new axiom guards cover this clock transfer and its actual dispatch application.


### A complete recursive finite-state replay compiler

`CBV/StatefulPairFusion.lean` closes the recursive user-rule correspondence
left open above. A specification chooses initial states in two fixed finite
machines and a first-order template tail; different rules may choose different
states and may call each other recursively. The generated Par rule captures
the two independent scans from the original caller position, uses real PEG
state/order guards to select the longer capture, replays it from that position,
and evaluates the rendered tail. The generated Seq grammar has two user-body
variants per specification, alongside the same actual scanner-helper prefix.
Its input-driven dispatch captures the common prefix and residual segment,
then reconstructs the original ordered values for the selected tail.

The construction is a fixed grammar translation. `render`, `parTail`,
`seqTail`, `parGrammar`, and `seqGrammar` depend only on the machines and
specifications, not on the input, its length, the stopping states, or capture
values. The captured strings may have arbitrary length. Nested recursive
calls, sequence, prioritized choice, star, and lookahead in template tails
are preserved. As in the earlier stateless compiler, template calls `call i []`
refer to a specification; nonempty template argument lists and higher-order
forms render to failure. This explicitly specifies the supported source family.

`replay_eval` identifies the actual runtime-selected source replay without a
semantic oracle. `evaluator_of_shift` reduces all template expressions to the
capture/table relation. `tables_shifted` proves that relation for **every**
frozen user stage, starting from undefined user rows, by evaluating the real
installed bodies on both sides. `evaluator_eq` consequently has no external
user-call simulation premise. `observations_iff` eliminates the frozen
iterations via the already proved physical/frozen cofinality. It preserves
all finite successes and failures on each original `List Char` input, including
empty input and equal scan endpoints. Undefined evaluation is not identified
with finite failure. Finally `language_translation` gives an actual fixed
first-order Seq grammar recognizing the same full-consumption language.

This completes the reverse compiler for this finite-state **replay-shaped**
family. It does not normalize arbitrary recursive/backtracking arguments or
an arbitrary source body starting at the original call position. In particular,
it does not establish the general CBV-Par/CBV-Seq reverse inclusion or a
language-class separator. Those remain the full objective. Root imports and
14 new public theorem axiom guards cover the complete compiler connection.


### Restoring the caller for a capture-independent fallback

`CBV/ReplayFallbackFusion.lean` addresses body entry through retained caller
continuation rather than a residual body entered after all captures. Source
rules have arity one and the form

```
F(x) <- (x B) / C
```

`B` is any first-order expression, including recursive calls and reuse of
`x`. `C` has no reference to the outer captured environment (`Closed`); it
may consume input, recurse, and invoke other rules with their own captures.
The head argument is an arbitrary first-order expression. It is not restricted
to a finite-state scan, finite palette, or bounded-length capture.

The target generates an arity-one rule for translated `B` and an arity-zero
rule for translated `C`. A translated call with argument `A` has the form

```
&translated(A) (F_main(translated(A)) / F_fallback())
```

The initial test preserves the source argument's failure and undefinedness
before either body branch can run. Successful argument evaluation is repeated
deterministically by the actual Seq call to `F_main`, which starts `B` at the
capture endpoint with the captured value available. If that call finitely
fails, ordinary caller-side PEG choice restores the original position before
calling `F_fallback`. An undefined first branch never selects the fallback.
`closed_env` and `render_closed` justify removing the outer capture from this
fallback's environment, including through its argument expressions.

`Shifted` relates a source row to an ordered choice between the target's
advanced main row and its original-position fallback row. `evaluator_of_shift`
proves the complete argument/call interface, including unknown, failed, and
successful arguments. `tables_shifted` proves this relation at every physical
table round for the actual generated rules. `evaluator_eq`, `decide_eq`,
`observations_iff`, and `language_translation` then close the fixed recursive
compiler without a user-table simulation hypothesis or totality assumption.
All finite original-string observations are preserved.

Unlike an unconditional replay source, the whole call need not advance past
its argument capture. The kernel-checked `fallback_returns_before_capture`
example captures all of `ab` but returns with `b` remaining after the first
branch fails, under both actual grammars. This arrangement lies outside the
single advanced-position interface ruled out by the earlier residual-control
obstructions: it retains the original caller and its choice continuation.

The restriction is substantive: the fallback cannot use the outer capture.
Bodies whose non-replay branch accesses that value at arbitrary positions,
multiple independent arbitrary arguments, and a general Par normal form
remain unresolved. This is a direct extension of the reverse compiler, not
a proof of general equality or a language-class separator. Root imports and
18 new public axiom guards cover the compiler and the earlier-return example.


### Capture-dependent choice and predicates at the original body position

`CBV/ReplayControlFusion.lean` generalizes caller-position fallback into a
finite body-control tree. A fixed part table contains arbitrary first-order
expressions. A replay part denotes `x B`, where `B` may use the unbounded
captured word and make recursive calls. A local part is independent of the
outer environment and may itself consume input or recurse. Each arity-one
source rule chooses a finite `Plan` assembled from these parts by prioritized
choice, negative predicate, and guarded sequencing `&P Q`. Guard operands
and nested predicates may themselves contain any such control tree. All part
references are syntactically valid; `ValidPlan` imposes no semantic oracle.

Unlike the preceding two-branch compiler, a fallback may now depend on the
captured word, and there may be any fixed number of capture-dependent branches
and tests. For example the generated source can implement

```
F(x) <- (x fail) / (&(!(x 'z')) 'a')
```

Both alternatives inspect the capture. On a successful negative test, the
second alternative reads `a` from the original caller position, not from the
capture endpoint. `capture_dependent_fallback` kernel-checks the actual Par
and Seq table evaluations: capturing `ab` on input `ab` leaves `b`, whereas
the same capture on input `abz` makes the second branch finitely fail.

The Seq grammar has one actual rule per fixed part: arity one for a replay
tail and arity zero for a local part. Call translation checks the arbitrary
head argument first, then executes the finite body-control tree at the caller.
Each replay leaf performs a real Seq call with that head parser, which
reconstructs the same deterministic runtime capture before entering its tail.
Choice and predicates retain the original caller position and their usual
partial-result behavior. No input-dependent grammar, capture palette, bounded
capture length, or finite-state head assumption is used.

`Plan.exp_eval` gives exact semantics for the control tree, including failure
and undefinedness of guards and predicates. `callLeaf_eval` connects its real
Seq calls to captured and original-position rows. `evaluator_of_shift` handles
arbitrary recursive first-order head arguments, and `tables_shifted` proves the
entire source-to-target table relation at every physical round. The resulting
`observations_iff` and `language_translation` preserve every finite observation
and the original full-consumption language with no recursive user simulation
premise. Root imports and 21 public axiom guards cover the connection.

The remaining boundary is structural: a consuming local part cannot be
followed by a new outer-capture-dependent part at that advanced position.
Such sequential reuse must already lie inside a replay tail. The control tree
therefore does not cover arbitrary capture-dependent bodies or several
independent arbitrary captures. General CBV-Par/CBV-Seq equality and separation
remain unresolved; this is an extension toward the body-entry obligation,
not a redefinition of that objective.


### Consuming body control with position-independent word arguments

`CBV/WordArguments.lean` and `CBV/WordControlFusion.lean` address the remaining
consuming-prefix boundary for another explicitly delimited source family.
Actual arguments are literals, parameter references, or concatenations of
such expressions. `value` computes their word from the current environment;
`word_eval` proves that each argument matches precisely that same word at
every position, or finitely fails everywhere if a referenced value is missing.
`value_of_success` connects this static expression value to the actual runtime
capture. There is no finite palette or bound on the word length. In particular,
`duplication` proves that `param(0) param(0)` denotes `w ++ w` for arbitrary `w`.

Body control now supports **arbitrary consuming sequence and repetition**,
as well as prioritized choice and negative predicates, between replay and
local parts. A replay part is `x B`; its tail `B` may use the capture and make
recursive calls with word-valued arguments. A local part is independent of
the outer environment and may consume input or recurse. Calls retain their
argument expression in the original caller environment. Each later replay
leaf can therefore match the same word from its current position, even after
a preceding local part or previous iterations have consumed input. The
successful Seq call captures that word at its new position and passes it to
the actual target tail rule.

This is complementary to `ReplayControlFusion`: it permits consuming control
between parts, while imposing word-valued arguments instead of arbitrary
recursive head parsers. An arbitrary parser can choose different captured
words at different positions; the position-independent value proof cannot
be applied to such a parser.

The target has one fixed zero-argument entry rule `eps` followed by one rule
per part (arity one or zero). `enter_word` transfers the caller's argument
expression to an equal literal word throughout the complete body control.
The table invariant relates a source row at **any** environment word and
input position to the actual target entry and expanded control at that
position. The entry rule keeps this strong invariant undefined at stage zero,
even for unmatched environment words or missing part references; a source
rule has not yet been unfolded at that stage. It is an ordinary installed
rule, not a semantic advice mechanism.

`Plan.eval_congr` covers consuming sequence and repetition with all intermediate
position bounds. `tables_shifted` proves the relation at every physical table
round, including empty captures, missing values, failed later replays, and
non-consuming loops. `evaluator_eq`, `observations_iff`, and
`language_translation` then preserve all finite successes and failures and
the original full-consumption language, without assuming a recursive user
simulation. The kernel-checked `consuming_prefix_and_repetition` example
captures `aa`, consumes an `a` before replaying that original value, accepts
`aaa`, rejects `aab`, and repeats the pattern twice on six `a` characters
under both actual grammars.

The construction still requires unary word-valued arguments and body
factorization into replay/local parts. It does not establish a normal form
for arbitrary source bodies, cover independently evaluated arbitrary argument
parsers, or prove general Par/Seq equality or separation. The complete original
objective remains open. Root imports and 24 new public axiom guards cover the
word-value foundation and its full recursive compiler application.


### Mixing arbitrary parsers and consuming word control in one recursive grammar

`CBV/MixedControlFusion.lean` connects the preceding complementary fragments
inside the **same actual generated grammars**, using the existing `parGrammar`,
`seqGrammar`, and `render` from `WordControlFusion`. No additional grammar or
input-dependent mode selection is introduced.

`AtOrigin` certifies control trees built from leaves, prioritized choice,
negative predicates, and guarded sequencing `&P Q` whose leaves all execute
from the original caller position. `origin_congr` proves that agreeing leaf
results at that single position suffice for their complete evaluation. At a
call to such a rule, an arbitrary supported first-order argument parser can
be evaluated again at that original position and recapture its same word.
For a call into general consuming control, the argument must instead be a
word expression (literal, parameter, or concatenation), so its captured value
remains position-independent throughout later sequence and repetition.

`Supported` expresses these alternatives **per call**. Argument expressions
are recursively checked, so fresh parsers may themselves call either kind
of rule according to the same discipline. Replay and local part bodies may
likewise cross between kinds recursively. `word_fragment_supported` embeds
the prior word-only fragment into this predicate. The restriction to unary
source rules and replay/local body parts is retained.

`GateOK` is established directly for every physical target table by
`physical_gate_ok`; it says that the installed entry rule's successes restore
the original position. `callLeaf_congr` and `enter_origin` require equal
argument results only where origin control will actually run them. The
arbitrary-parser case obtains this equality and the captured word from real
source semantics, not a global position-independence premise. The word case
uses the earlier `enter_word` theorem. These cases close
`evaluator_of_shift`, and `tables_shifted` proves the entire mixed recursive
user-table correspondence at every physical round. `observations_iff` and
`language_translation` preserve all finite observations and the original
full-consumption language. No gate correctness, user simulation, or semantic
argument oracle remains as an external premise of those final theorems.

The kernel-checked `fresh_parser_then_consuming_call` example combines

```
F(x) <- x G(x)
G(x) <- 'a' x !F('')
```

It calls `F` with a fresh two-character parser, passes its captured `aa` to
consuming `G`, and calls back into `F` under negation. Both actual grammars
consume five `a` characters after four table rounds. The example also checks
the mixed syntax conditions for its root and every part.

This removes the need to select one argument/control convention for the
whole source grammar. It does not allow an arbitrary position-dependent
parser at a consuming-control call, normalize all capture-dependent bodies
into these parts, or handle multiple independent general arguments. The
unrestricted equality/separation objective remains unresolved. Root imports
and 15 new public axiom guards cover the mixed connection.


### Committing composite argument choices before consuming body control

`CBV/SymbolicWordSelection.lean` builds a selector from argument **syntax**
alone. Its supported arguments contain literals, current parameters,
concatenation, and prioritized choice. The selector chooses a word expression
made only from literals, parameters, and concatenation. It does not enumerate
runtime character strings or require a finite palette for the parameter values.
Thus choices between a current word and its duplication remain supported at
arbitrary captured lengths.

`selectAt` retains a word expression for the already selected prefix and uses
input-restoring PEG probes to inspect the next subargument at its actual
position. Concatenation selects its right operand after the left operand's
consumed prefix; a failed later operand does not retry the left operand's
choice. Prioritized choice uses guarded dispatch, so failure or undefinedness
of the selected continuation cannot change the selected argument alternative.
`selectAt_eval` and `select_eval` prove the full partial result and the value of
the selected word expression for arbitrary continuations respecting that value.
The construction depends on source expressions and their finite branch structure,
not on an environment, input, table, capture length, or captured characters.

`CBV/SelectedControlFusion.lean` discharges that continuation interface using
actual installed target part rules. A call with such a composite argument
selects its word expression at the original position, then enters the body
control with that fixed expression. Later replay leaves evaluate the selected
word expression, not the original choice-containing parser. Arbitrary consuming
sequence, repetition, choice, and predicates in the body therefore preserve
the original captured value even if another alternative would match at a later
position. `growing_argument_supported` checks choices involving `x x` and `x`
without a palette-closure condition.

This new compiler also retains arbitrary supported argument parsers at
`AtOrigin` callees. `mixed_fragment_supported` embeds the preceding mixed
fragment into its syntax predicate. Such calls may recursively cross into
composite-argument consuming calls and back. The source grammar constructor
is unchanged; the target is a fixed entry rule and a fixed rule per part,
with the syntax selectors generated at call sites.

`evaluator_of_shift` connects actual selection, actual captures, and actual
part queries. `tables_shifted` proves the recursive relation at every physical
round; no user-call simulation or argument-value oracle is retained in
`observations_iff` or `language_translation`. They preserve all finite results
and the same original full-consumption language.

The kernel-checked `chosen_word_stays_committed` example uses a consuming
source body `F(x) <- 'a' x` and a composite argument `(aa / a) eps`. Input
`aaa` succeeds, while `aab` finitely fails under both actual grammars. On the
second input the initial choice committed to `aa`; retrying `a` after the
body fails, or re-evaluating the original choice at the advanced position,
would incorrectly produce a success. The example also checks the syntax
conditions for the root and every part.

Consuming-control arguments still exclude repetition, predicates, and recursive
calls; those remain allowed only under the separate origin-control discipline.
The unary source restriction and replay/local body factorization also remain.
General Par/Seq equality or a language-class separator is still unresolved.
Root imports and 28 new public axiom guards cover the selector and its complete
recursive compiler application.


### Recursive predicates within consuming-call arguments

`CBV/GuardedWordSelection.lean` extends syntax-selected arguments with negative
predicates. A successful predicate contributes the empty word; its failure and
undefinedness are retained distinctly. Its body may be any supported
first-order computation, including repetition and recursive queries obeying
the same call discipline. Positive lookahead follows from double negation.
Literals, current parameters, concatenation, and prioritized choice remain
available around these tests, with no finite capture palette.

`argRender` translates predicate bodies. `Checks` records the subexpressions
whose query semantics must correspond. `arg_eval` and `probe_eval` evaluate
the translated predicates at the actual current argument position, after the
already selected prefix. `selectAt_eval` then selects the complete captured
word expression without letting a failed continuation retry an argument choice.
For a successful predicate it passes `lit []` to the continuation. Its generic
predicate correspondence premise is explicit at this interface layer.

`CBV/GuardedControlFusion.lean` discharges that premise for the actual recursive
compiler. `render`, `scanArg`, and `chooseAt` are mutually defined on decreasing
source syntax, so predicate translation and selector construction produce one
fixed finite grammar. `scanArg_eq` and `chooseAt_eq` connect that code to the
generic selector. Target first-order syntax is proved mutually with the
first-order property of translated predicate subexpressions.

Crucially, `evaluator_of_shift` is proved mutually with `predicate_checks`.
The expression proof supplies recursive predicate correspondence, and the
selector uses it at each actual argument position. `tables_shifted` closes
the recursive user-table relation at every physical round. Consequently
`observations_iff` and `language_translation` retain no external hypothesis
that predicates, gates, arguments, or recursive user rules simulate correctly.
They preserve every finite success/failure and the original full-consumption
language, including empty captures and predicate queries with no finite result.
`selected_fragment_supported` embeds the preceding composite-argument fragment.

`predicate_at_argument_position` checks a query after an initial captured `a`.
The query tests for `z`; the root succeeds on `aaa` and finitely fails on `aza`
under both actual grammars. Testing at the original position instead would
miss the `z`, and the body's consuming fallback would incorrectly accept.
`undefined_predicate_stays_undefined` proves, for **every** physical table stage,
that a self-recursive query in a negated argument leaves both complete calls
undefined. It never becomes finite failure and cannot select the next argument
alternative. This result is by induction and recursive compiler correspondence,
not just a finite execution sample.

The remaining argument restriction concerns forms producing captured characters:
consuming repetition and direct recursive calls are still outside consuming-call
argument selection. Such computations are allowed inside predicates and at
origin-control callees. Unary source rules and replay/local body factorization
also remain. Thus the general CBV-Par/CBV-Seq equality or separation is still
unresolved. Root imports and 34 new public axiom guards cover the selector,
mutual recursive compiler, shifted-position example, and unbounded unknown case.


### Boundary of finite Word selection for fresh consuming repetition

`CBV/WordSelectionBoundary.lean` identifies a limitation of the latest reverse
compiler's capture-selection interface. It does **not** separate Par and Seq
language classes.

`candidates` enumerates the finite Word expressions a guarded argument can
offer to its continuation: literal and parameter leaves, empty words for
successful predicates, union for choice, and concatenated pairs for sequencing.
`candidates_word` verifies their syntax. `selectAt_congr` proves that agreeing
on just this list makes two continuations produce identical selector syntax,
for every predicate translator, prefix, and continuation. Recursive predicates
do not introduce additional captured characters.

`success_candidate` ties the list to actual successful source evaluations,
including sequenced argument positions and predicate results. For a fixed
current environment, `capture_le_budget` bounds all these captures by a
finite input-independent sum of candidate value lengths. This does not impose
a universal bound across environments: existing parameters may be arbitrarily
long, and the earlier duplication construction remains valid. The distinction
is between selecting combinations of existing values and discovering an
arbitrarily long **new** capture while that environment stays fixed.

`no_finite_word_family` quantifies over **any** finite family of expressions,
not just the particular enumeration, and any fixed environment. Choosing a
repeated-character word longer than the sum of all their values gives a value
outside the family. `scanner_replicate` and `scanner_exceeds_family` connect
this length argument to an actual successful greedy source scanner for every
repetition length, under either evaluation strategy. It is not an assumed
or externally supplied capture. `no_shape_scanner_equivalent` applies the
bound to real physical grammar tables: no guarded-selection-shaped argument,
even with arbitrary first-order recursive predicate bodies, agrees with this
consuming scanner on all original strings at any fixed table round.

Crucially, `scanner_observations` proves the scanner itself has identical
Par and Seq finite observations on **every** original string, including all
remaining suffixes and finite failure observations. Thus the obstruction
excludes this finite-candidate capture interface, rather than recognition
by a different Seq grammar. Merely adding recursive predicates or more finite
Word alternatives cannot remove the general consuming-repetition gap. A full
reverse compiler needs a way to introduce fresh dynamic captures with the
required body position, a richer runtime representation, or a construction
that preserves observations without reconstructing the capture this way.
The general equality/separation goal remains unresolved. Root imports and
ten standard-axiom guards cover the new boundary results.


### Fresh parser captures by fusing a repeated body prefix

`CBV/ParserPrefixFusion.lean` gives a complementary reverse compiler that
actually introduces fresh unbounded captures, beyond the finite Word-selector
interface. It uses a specific source body/call relationship rather than
trying to reconstruct every possible captured word at the original position.

A specification supplies one closed call-free PEG `A_i` and a tail `B_i`
for each unary rule. Raw zero-argument calls to `i` are expanded to actual
calls `F_i(A_i)`; all calls to a given rule use that same fixed argument
parser. The generated Par rule is `F_i(x) <- A_i B_i`, and the Seq rule is
`F_i(x) <- B_i`. Both actual grammars use the same expanded root expression.
Thus Par evaluates the parser once as its argument and again as the body
prefix, whereas Seq retains that fresh capture and enters the tail at the
end of the first evaluation. The captured value is never inserted as a
compile-time literal or selected from a finite family.

`Pure` permits arbitrary nesting of literals, character/range/any atoms,
sequencing, ordered choice, predicates, and consuming repetition in `A_i`.
It excludes parameters and calls. `pure_eval` proves the **whole partial**
parser result is independent of grammar tables, strategy, and environment;
nullable repetitions are allowed and remain undefined. Tails and the root
may use parameters, consuming sequence/repetition, choice/predicates, and
recursive calls to any supplied rule, under the fixed-argument calling
convention. Calls with arbitrary user-supplied arguments are not part of
this raw syntax. Existing captures remain in caller environments across
recursive calls, as usual.

`tables_shifted` proves the actual physical row correspondence at **every**
round. `evaluator_eq` discharges expression simulation from that proof, and
`observations_iff`/`language_translation` preserve all finite success/failure
observations and full-consumption languages on the same original strings.
Only the syntactic `Pure` check is assumed; there is no argument oracle,
external user-table correspondence, helper stabilization premise, or totality
assumption.

`copy_word` proves for **every** a/b word `w` that the source really captures
`[w]` and both fixed grammars accept `w#w` at their actual physical first
round. The tail consumes `#` **before** replaying the retained capture.
`beyond_finite_word_selection` connects this positive construction to the
preceding impossibility theorem: for any fixed environment and finite
Word-expression family, these same grammars realize a capture outside that
family and subsequently replay it. This is an unbounded theorem, not a
bounded execution sample.

`nested_captures` kernel-checks three recursive calls retaining `ab`, `ba`,
and the empty word in one run. It accepts `ab#ba##baab` and rejects
`ab#ba##bbab` under both actual grammars. `nullable_repetition_keeps_undefined`
proves, for every input and physical round, that `eps*` as the argument never
becomes failure or an empty successful capture in either grammar.

The remaining restrictions matter: a call uses the callee's fixed closed
call-free parser, and the Par body must reparse that parser as its first
action. No normalization of arbitrary Par bodies or argument computations
into this form is proved. This complements the selected-Word compiler; it
does not replace the general original-string equality/separation goal.
Root imports and nineteen new public axiom guards cover the construction.


### Independent recursive argument parsers

`CBV/RecursiveParserStability.lean` removes the call-free restriction on the
argument-parser component. `Lexical n` permits arbitrary ordinary PEG control,
including calls to any of the first `n` arity-zero helper rules. The component
is closed: it cannot refer to captured parameters or user rules. Helpers may
be mutually recursive or have no finite result; totality and a bound on the
recursive derivation depth are not assumed.

`Installed` specifies the actual helper prefix of a combined grammar.
`helper_rows_eq` proves complete physical helper rows agree between arbitrary
installed extensions, strategies, and environments at every round. The
standalone component's finite-table stabilization theorem supplies the floor
`iterBoundV (grammar bodies) x + 1`. `helpers_stable` transfers stabilization
to the actual installed combined grammar for **all** capture environments.
`frozen_lexical_eval` therefore agrees at all frozen user stages, without
external parser results or a supplied helper-stability premise. The floor is
a proof device depending on the input; no such number or advice is added to
the generated grammar or its input.

`CBV/RecursivePrefixFusion.lean` installs the same independent recursive
helper component in source and target, followed by unary user rules. A user's
head `A_i` may query that recursive component. Every call to the user captures
its fixed `A_i`; its Par body is `A_i B_i`, and its Seq body is `B_i`. The
recursive user tails still retain their captures through arbitrary consuming
control and later replay. `tables_shifted` and `evaluator_eq` prove all frozen
user rounds correspond. `observations_iff` invokes physical/frozen cofinality
on both **actual** grammars, preserving every finite success/failure on the
original character input. `language_translation` has only the syntactic
closed-component conditions; generic lexical correspondence and shifted
user-table relations are discharged internally.

`lexical_zero_iff_pure`, `valid_without_helpers`, `render_without_helpers`,
and `without_helpers` prove that supplying no recursive helper rules gives
exactly the preceding call-free compiler's syntax and eligibility condition.
This extends that construction, rather than requiring a new external oracle
for the newly admitted arguments.

`balanced_prefix_observation` proves that an installed recursive rule
`A <- a A b / eps` captures `a^n b^n` for **every** `n`, with any non-a
starting suffix. `balanced_copy` uses this actual argument derivation to
prove one fixed source/target pair accepts `w#w` for every
`w = a^n b^n`, replaying the capture after consuming `#`. The proof builds a
real Par call derivation and applies the complete original-string reverse
compiler; it does not sample a bounded set of depths.
`balanced_physical_execution` additionally kernel-checks acceptance of
`aabb#aabb` and finite failure on `aabb#aab` using actual physical tables.
`cycle_undefined` and `recursive_argument_undefined` prove that an unproductive
recursive helper leaves the complete argument call undefined under both
strategies, on every input and at every physical stage.

The remaining restrictions are fixed per-callee closed arguments, an independent
arity-zero argument component, and the Par body's initial reparse of the same
argument parser. User-dependent recursive arguments, general body-entry
normalization, and arbitrary independent captures are still outside this
construction. General Par/Seq language-class equality or separation remains
unresolved. Thirty-one new public axiom guards and root imports cover this
extension.


### Fresh captures and capture-dependent recursive arguments in one grammar

`CBV/MixedPrefixFusion.lean` combines the independent-recursive-parser entry
with the earlier leading-replay calling convention in one actual source/target
grammar. A user specification has either a closed recursive parser head `A`,
or no parser head. The corresponding Par bodies are `A B` and `x B`; both
Seq bodies are `B`. All actual user rules have arity one.

The raw shorthand `F()` calls a parser-headed rule with its fixed `A`.
`R(a)` calls a replay-headed rule with the recursively translated argument
`a`. Such arguments may use current captures, concatenation, ordered choice,
consuming repetition, predicates, and user calls of either kind. They are
not limited to Word expressions, a finite value palette, independent parser
queries, or an origin-control-only body discipline. Both kinds of rules may
call each other recursively, including inside an argument predicate. The
parser-headed rules themselves still use their fixed closed arguments.

`Ready` records the actual entry relationship: replay rules need the captured
word's prefix split, while parser-headed rules need the real recursive parser
result. `tables_shifted` derives both row relationships simultaneously at
every frozen user stage. `ClockFreezing.frozen_sound` proves every defined
frozen row has an actual derivation, using its information-order embedding
into a physical table; it does not need a helper-stability assumption. This
supplies the successful-prefix fact for arbitrary recursive replay arguments.
The final `evaluator_eq`, `observations_iff`, and `language_translation`
discharge the argument, helper, and user-table correspondence internally,
preserving all finite observations and languages on the original strings.

`lift`, `render_lift`, `grammars_lift`, and `valid_lift` embed the preceding
independent-recursive-parser compiler exactly, including its eligibility,
source/target grammars, and expanded expressions.

`mixed_recursive_capture_execution` kernel-checks a run in which a new
recursive capture `ab` feeds an argument containing `!Probe(x)` and
`(x x / x)`. The replay rule consumes the selected argument, then recursively
re-enters the parser-headed rule and obtains another fresh capture `aabb`.
The two strategies accept `ab#abab!aabb#aabbaabb` and finitely reject
`ab#abab!aabb#babbaabb` under their actual physical tables. The probe itself
is a user-rule call, so argument evaluation crosses the recursive rule
interface while using the caller's retained capture.

`recursive_argument_choice_undefined` proves a separate user-recursive
argument query stays undefined on **every** input and at **every** physical
round. Negating it does not produce failure or success, and its following
empty-word argument alternative cannot be selected.

The remaining body restriction is an initial replay or an initial reparse of
the fixed closed argument parser. No arbitrary body-entry normalization is
proved. Parser-headed argument computations are still independent of user
rules and current captures; unrestricted recursive/capture-dependent
arguments enter through replay-headed rules. Multiple independent general
arguments and general Par/Seq equality or separation remain unresolved.
Twenty new public axiom guards cover the mixed compiler and frozen soundness.


### Caller-position control around fresh captures and arbitrary replay calls

`CBV/OriginPrefixControl.lean` lifts the previous two entry conventions into
finite body control, removing their unconditional initial-replay/reparse
requirement. A rule has a caller-position `ReplayControlFusion.Plan`: a
finite combination of prioritized alternatives, negation, and guarded
sequencing (`&P Q`). Each referenced part either enters an arbitrary tail
after replaying/reparsing the capture, or is a closed local expression that
runs directly at the original caller position. A body can therefore inspect
the capture under predicates, consume and fail in one branch, restore the
caller position, and select a local branch that returns before the argument's
endpoint. No initial consuming capture read is required of the whole body.

As before, rules are either fixed-parser rules, using a closed expression
that may query the independent mutually recursive PEG helper component, or
replay rules, accepting arbitrary recursively translated arguments. Those
arguments may use retained values, consuming repetition, choice, predicates,
and user calls of either kind. Part tails may themselves call either kind
of user recursively. A successful continuation does not reevaluate the
argument at an advanced position: every caller-side control leaf starts at
the same original position, so repeated argument evaluation in a leaf retains
its exact original captured value.

The source expands each rule's plan with its parser/replay entries and its
local parts. The target expands control at the call site and installs one
advanced arity-one rule per replay part and one arity-zero rule per local
part. `render_closed` proves raw local parts remain capture-independent
through the full recursive translation. `call_eval` explicitly performs the
argument check before **all** body control, including a fully local body.
Finite failure and undefinedness of the argument therefore cannot be
bypassed by a local alternative.

`tables_shifted` derives the actual source-user/target-part relation at every
frozen user round. The syntactic plan-index check ensures even stage-zero
control remains undefined until a real user row is reached. `evaluator_eq`
then covers arbitrary raw expressions and recursive arguments.
`observations_iff` uses the already-proved actual helper stabilization and
physical/frozen cofinality, yielding all original-string finite observations;
`language_translation` has only syntactic component, head, local-closure, and
plan-index premises. No continuation, argument, user-table, or helper oracle
remains in the final theorem.

`origin_fallback_execution` kernel-checks the actual physical tables. On
`aabbaabb`, the fresh recursive parser captures the first `aabb`; the first
branch forwards that value recursively and fails. A capture-dependent
negative lookahead then selects local `a` at the original position, leaving
seven characters. The same grammars finitely reject `aabb#aabb`, where the
probe successfully replays the captured value after `#`. This is a return
**before** the fresh argument's endpoint, not a forced advance.
`undefined_argument_before_local_branch` proves that an unproductive
recursive argument stays undefined before a local body branch on every
input and at every physical stage, even though that branch ignores the
capture and could otherwise succeed immediately.

The remaining control restriction is substantive: no consuming sequence or
iteration of different capture-dependent parts is allowed at the caller
control level. Consuming computation is allowed inside an entered tail or
local part. The caller-level control must keep every parameter-sensitive
entry at the original position. Fixed-parser arguments remain independent
of user rules and captures, whereas unrestricted dependent arguments enter
through replay rules. General body decomposition, multiple independent
general captures, and general Par/Seq equality or separation remain
unresolved. Twenty-eight new public axiom guards cover this construction.


### Consuming control and fresh origin captures in one recursive grammar

`CBV/ConsumingPrefixControl.lean` combines the fresh recursive-parser
construction with consuming body control, using one installed source/target
grammar pair. Its `WordControlFusion.Plan` permits arbitrary consuming
sequence and repetition, as well as choice and predicates, between parts.
The old caller-position plan embeds through `originPlan`: restoring guards
become double-negated left sides of sequencing. `originPlan_atOrigin` and
`originPlan_exp` verify the control discipline and exact expression equality.

Calling conventions can change within recursive computation. A fixed-parser
rule obtains a fresh unbounded capture from the independent recursive PEG
component and uses caller-position control. A replay rule may consume between
capture uses if its actual argument is a position-independent Word expression
(literals, existing parameters, and concatenation). These Word values may be
arbitrarily long and may duplicate existing captures. If the replay callee
uses caller-position control, its argument may instead be any supported
recursive computation. Thus new captures can be passed as retained values
into consuming rules, and those rules can recursively re-enter fixed-parser
rules for further fresh captures. This does not require a finite value palette.

`enter_word` preserves the argument's value at every later body position;
`enter_origin` permits arbitrary parsers when all capture-sensitive entries
stay at the call origin. The `Supported` check chooses one of those two
conditions per call. Fixed-parser heads themselves must use `AtOrigin`
control. This restriction is explicit: directly using an arbitrary fresh
parser as the argument of a consuming-control rule remains outside the proof.
Composite choices or predicates inside consuming-call arguments are not
Word expressions in this combined compiler; the earlier guarded-selector
compiler still handles its own separate fragment.

A fixed zero-argument entry rule retains the physical user-round boundary,
including stage zero. `leaf_step` connects actual source entries to target
part rows. The source/target plan proof uses all-position congruence for
replay-headed consuming rules and origin-only congruence for fresh-parser
rules. `tables_shifted` closes that mixed correspondence at every frozen
user round. Actual helper stabilization and physical/frozen cofinality then
yield `observations_iff` and `language_translation` on the same original
strings. No capture, recursive-call, continuation, or lexical oracle remains
in the final result.

`fresh_capture_consuming_execution` kernel-checks a real physical-table run.
The recursive parser first captures `ab`; the consuming rule reads a local
`ab!` prefix before repeatedly replaying the held `ab` and consuming `;`.
It then recursively captures `aabb` and enters consuming control again.
Both strategies accept `ab#ab!ab;ab;?aabb#aabb!aabb;` and finitely reject
`ab#ab!ab;ab;?aabb#aabb!ab;`, where the later replay is shorter than the
held capture. The theorem is checked against actual physical tables, not
frozen helper values. General language/observation preservation is the
unbounded theorem; this example exercises both mode changes and the loop.

The central remaining gap is arbitrary argument evaluation at advanced
capture-sensitive body positions. General consuming-call argument capture,
general body decomposition, multiple independent general arguments, and
general Par/Seq equality or separation remain unresolved. The existing
`original_reverse_requires_P_linear_space` bridge was also rechecked in
`Shallot/Peg/Separation/CBVSeqLinearSpace.lean`; its conditional separator
still requires an unproved P language outside linear space. No new class
conclusion is drawn here. Thirty-eight new public axiom guards cover the
combined consuming-control compiler.


### Guarded selection in the fresh/consuming recursive compiler

`CBV/GuardedPrefixControl.lean` closes the previously separate guarded-argument
and fresh-capture/consuming-control constructions. Replay calls may now use
arguments built from literals, parameters, concatenation, prioritized choice,
and negation. Predicate bodies may contain arbitrary supported recursive
calls, including fresh-parser rules and consuming rules. If the callee uses
caller-position control, arbitrary supported arguments remain permitted.
Independent recursive-parser heads still require caller-position control.

The source-side predicate calls have already been rewritten to installed
user addresses; they are not the raw predicate syntax. The new
`CBV/MappedGuardedWordSelection.lean` proves selection with two independently
transformed predicate bodies. `Agrees` compares the actual source rendering
with the actual target rendering at every valid argument position.
`selectAt_eval` preserves undefined results, finite failure, captured words,
and continuation results through sequential argument components. Successful
negation contributes the empty Word expression. The continuation is invoked
at the original caller position, with the selected Word expression fixed.
Later consuming failure cannot change that selection.

The compiler uses mutual `render`/`scanArg`/`chooseAt` definitions. Its semantic
proof mutually establishes evaluator correspondence and predicate agreement;
no recursive predicate oracle is assumed by the final theorem. A target gate
preserves the user-round boundary, and the existing physically stabilized
helper component connects all frozen rounds to actual observations.
`observations_iff` covers every finite success/failure observation on the same
original character strings. `language_translation` supplies one fixed Seq
grammar and start expression.

This is an extension of the actual prior source, not a different source
execution convention. `Spec` is the previous spec type; `source_render_eq`
and `source_grammar_eq` prove exact equality with the previously installed
Par expressions and grammar. `consuming_supported` and `consuming_valid`
embed the previous Word fragment. `original_observations_iff` and
`original_language_translation` state the preservation theorem directly for
that prior source grammar, with the enlarged syntactic support condition.

`fresh_selected_consuming_execution` kernel-checks physical tables for three
inputs. Both strategies accept
`ab#abab!abab;?aabb#aabbaabb!aabbaabb;`: a fresh `ab` is duplicated by a selected
argument after a recursive negative query; consuming control replays `abab`,
then recursion obtains fresh `aabb` and replays its selected duplication.
Both also accept `ab#ab!ab;`, where the doubled argument fails before entry
and the short arm is selected. Both finitely reject `ab#abab!ab;`, where the
doubled argument succeeds before entry but its later replay fails. This last
input would accept if the continuation incorrectly reselected the short arm.
These examples supplement the unbounded observation theorem.

The remaining gap is still arbitrary argument capture for consuming rules:
non-finite fresh parser results cannot in general be selected from these
finite Word-expression candidates. General body decomposition and multiple
independent general captures also remain outside this compiler. General
Par/Seq equality or language-class separation is not established.
Fifty-four new public axiom guards cover this extension.


### Fresh recursive arguments without a source-side head replay

`CBV/ScannerAbsorption.lean` provides a syntactic absorption condition for
an independent recursive argument component. `Safe n A e` allows empty
expressions, accepted characters, accepted literal words, sequencing, choice,
repetition, zero-argument component calls, and arbitrary negative queries.
Negation's query need not consume only accepted characters: successful
negation itself consumes nothing. Lexical validity is checked separately.

`evaluator_safe` proves that every successful evaluation leaves the greedy
`A` scanner's final suffix unchanged. The proof uses a table invariant for
component calls and structural control reasoning, including decreasing
repetition. `physical_rows_safe` establishes the invariant on actual helper
tables at every round; `frozen_rows_safe` transfers it to physically frozen
helpers. `scan_after_success` states the resulting absorption law for a real
successful recursive argument. No captured-word length bound is imposed.

`CBV/ScannerPrefixFusion.lean` uses this law in a whole recursive grammar.
Each rule has a fixed independent recursive head `H`, a scanner alphabet
`A`, and an arbitrary recursively rendered tail `B`. The actual arity-one
source rule body is `scan(A) B`; its caller supplies argument `H`. In
particular the source body does not begin by reparsing `H` or replaying its
captured parameter. Under Par, the scanner begins at the caller position;
under Seq, argument capture advances to the end of `H` before the scanner
begins. The syntactic absorption condition makes both scanners reach the
same final position, with exactly the same original capture in their
environments. The recursive tails can then use that capture after further
consumption, in repetitions, predicates, choices, and nested fresh calls.
Different rules may use different scanner alphabets.

`tables_shifted` proves the actual user-row correspondence, using helper
stability rather than assumed argument outcomes. `observations_iff` and
`language_translation` preserve all finite observations and recognized
languages on the same original character strings. `same_grammar` records
that this particular fragment even uses identical installed source and
target syntax; the theorem quantifies over all valid components, tails,
inputs, and finite observations, rather than comparing a few executions.

`scanner_before_capture_execution` kernel-checks physical tables for
`aabbab#aabb;aabb?ababb#ab;ab`. The first recursive argument captures `aabb`,
then the source body consumes the longer prefix `aabbab` before the first
capture use. The recursive call later captures `ab` and scans the longer
prefix `ababb`. Both captures are replayed repeatedly after consumption.
`aabbab#aabbab` is rejected: the whole scanned prefix cannot replace the
original shorter capture. `recursive_argument_undefined` proves on every
input and every physical round that a looping argument remains undefined;
the scanner cannot bypass it.

This removes mandatory head replay for a syntactically verified consuming
prefix. It does not normalize arbitrary consuming body control. The argument
component remains closed and independent, and every helper body is checked
against the applicable scanner alphabet. This is a separate fresh/scanner
construction; it has not yet been combined with the guarded mixed-mode
compiler. Arbitrary capture-dependent arguments and general Par/Seq equality
or separation remain unresolved. Twenty-three new public axiom guards cover
this construction.


### Absorbing scanners and arbitrary replay arguments in one grammar

`CBV/MixedScannerPrefixFusion.lean` connects the preceding scanner compiler
with replay-headed rules in one actual fixed source/target grammar pair.
A rule with a fixed closed recursive head uses `scan(A) B` at source body
entry and the same scanner at target body entry. A rule without a fixed
head instead accepts one arbitrary recursively rendered argument: the source
replays its captured value before `B`, and the target enters `B` after Seq
argument capture. Calls may recursively change modes. Neither the arbitrary
arguments nor the replay-rule tails need satisfy the scanner-alphabet check;
that condition applies only to independent fixed-parser heads and helpers.

`Ready` distinguishes an actual fixed-head capture from a captured arbitrary
argument prefix. `tables_shifted` closes both cases. In scanner mode, the
syntactic absorption theorem makes the two body entries reach the same
position. In replay mode, actual argument success supplies the prefix fact
and the source replay reaches the Seq body position. `evaluator_of_shift`
handles arbitrary recursively rendered argument computations, including
choice, predicates, repetition, parameters, and nested calls. Physically
stabilized helpers and frozen/physical cofinality eliminate semantic oracle
assumptions from `observations_iff` and `language_translation`.

This combines the two calling conventions operationally. The existing
scanner-only grammar embeds exactly: `render_liftScanner` and
`grammars_liftScanner` prove syntactic equality, and `valid_liftScanner`
transfers its conditions. Fresh-mode source bodies still do not begin with a
head reparse or a capture replay.

`scanner_to_recursive_argument_execution` kernel-checks actual physical
tables on `aabbab#aabbaabb;aabbaabb!ababb#abccc;abccc`. The first independent
recursive argument captures `aabb`, then its body scans the longer prefix
`aabbab`. A parameter-dependent argument runs a recursive negative query and
captures the selected duplication `aabbaabb`. The replay rule uses that new
capture repeatedly, then recurses into fresh mode. There the head captures
`ab`, its body scans `ababb`, and a new argument captures `abccc`, adding
fresh `c` characters to the retained value before further repeated replay.
An altered final copy is finitely rejected by both actual grammars.

`unbounded_suffix_capture` separately proves for all retained words `w`, all
`n`, all tails, and all tables/strategies that the parameter followed by the
`c` scanner really captures `w ++ c^n` before `#`. Both argument evaluators
return that actual value; the Seq evaluator also returns the correct ending
position. Thus this mode is not restricted to finite choices of existing
Word expressions. `recursive_argument_choice_undefined` proves on every
input and every physical round that an undefined recursive negative query
inside an argument never falls through to the empty alternative.

The fresh component is still closed and independently recursive, and its
body entry must be the absorbing scanner. Replay mode retains its own
leading-replay condition. This compiler has not been combined with arbitrary
caller-position body plans. General body decomposition, multiple independent
general captures, and the full Par/Seq equality or separation remain
unresolved. Twenty additional public axiom guards cover the mixed compiler.


### Short prefixes and overlapping fresh-capture replay

`CBV/CaptureCommutation.lean` extracts a captured-word alphabet from the
syntactic recursive-parser absorption condition. The earlier scanner endpoint
invariant, combined with actual successful-prefix semantics, implies that
all characters of the consumed prefix belong to the declared alphabet.
`captured_alphabet` proves this using actual sound tables. For a singleton
alphabet, `unary_word` identifies every captured value as a repetition of that
character. `unary_commutes` then permits a fixed repetition prefix to commute
with captures of every length. `prefix_swap` proves equality of the two Word
parsers for any commuting words, including finite failure, without any
assumption about disjoint input spans.

`CBV/UnaryOverlapFusion.lean` applies this to a full recursive compiler.
Each fixed-parser rule declares a symbol `c`, a shift `d`, and an arbitrary
recursively rendered tail `B`. The Par rule body is `(c^d param(0)) B`;
the Seq rule body is `c^d B`. The caller supplies a closed independent
recursive argument `H`. Syntactic validity requires the component and head
to satisfy the singleton-alphabet condition, alongside ordinary lexical
validity. The source body does not begin with a head reparse or a capture
replay: it first consumes its short prefix, then replays the held capture.

When the prefix is shorter than the capture, the source's first replay starts
strictly inside the original argument capture interval. The transformation
does not move that original body unchanged to the capture endpoint. It
commutes the short prefix with the capture replay, which makes the source
reach the same tail position as Seq argument consumption followed by the
short prefix. Both tails retain the same original capture. `tables_shifted`
closes this correspondence through the actual recursive grammar, including
failing prefixes and arbitrary consuming recursive tails. Helper stabilization
and physical/frozen cofinality yield `observations_iff` and
`language_translation` on all original character strings. Final premises are
syntactic; no runtime commutation oracle is assumed.

`overlapping_capture_execution` checks actual physical tables for the closed
recursive helper `A <- 'a' A 'a' / 'a'`. On a first block of fourteen `a`
characters, the argument really captures thirteen: the theorem checks the
actual Par argument list, not an assumed capture. The source body consumes
one `a` before replaying those thirteen, so the intervals overlap by twelve
characters. It uses the same capture again after `#`, then recursively obtains
a new five-character capture from a six-character block. Both transformed
grammars accept that input. A thirteen-character first block lacks the extra
shift character and is finitely rejected by both strategies.

This treats overlap that the preceding absorbing-scanner entry did not
cover: the initial one-character source consumption has not reached the end
of the thirteen-character capture. The result remains a singleton-alphabet
fragment with a fixed repetition prefix and one independent head per rule.
General noncommuting overlap, arbitrary body decomposition, multiple
independent general arguments, and full Par/Seq equality or separation remain
unresolved. Twenty additional public axiom guards cover the construction.


### Noncommuting overlap through periodic capture phases

`CBV/BlockCapture.lean` replaces the singleton alphabet with a fixed word
block `u`. `Safe n u` describes recursive expressions that consume whole
numbers of these blocks: block-power literals, empty expressions, component
calls, sequencing, choice, repetition, and unrestricted negative queries.
Ordinary lexical validity remains a separate requirement. `evaluator_safe`
proves an actual suffix relation with a block-power prefix;
`physical_rows_safe` and `frozen_rows_safe` derive it for every helper round.
`head_capture` then identifies the value captured by a block-safe recursive
core followed by a fixed phase suffix `left` as `u^n ++ left`.

If `u = left ++ right`, the appropriate word equation is
`u ++ (u^n ++ left) = (u^n ++ left) ++ (right ++ left)`.
`rotate` proves this for every block count. `prefix_rotate` turns the equation
into exact parser equality, including finite failure, using a rotated residual
rather than assuming that the source prefix and capture commute.
`ab_noncommuting` proves for every `n` that `ab` and `(ab)^n a` do not commute.
Thus this construction covers genuinely noncommuting shifted replay.

`CBV/PeriodicOverlapFusion.lean` closes the corresponding fixed recursive
grammar transformation. A rule specifies a closed recursive core, static
`left` and `right`, and an arbitrary recursively rendered tail `B`. Its caller
captures `core left`; the Par body is `(u param(0)) B`, while the Seq body is
`(right left) B`. The target still holds the exact original capture for later
uses. The syntactic block condition on the core and helper component derives
the phase equation during the user-row induction. No runtime phase or word
commutation oracle is assumed by `observations_iff` or
`language_translation`; both concern the same original character strings and
all finite observations. Undefined and finitely failing arguments retain their
strict call semantics.

`rotated_overlap_execution` kernel-checks actual physical tables for the
recursive core `A <- 'ab' A 'ab' / 'ab'`. On `(ab)^14 a`, the argument
`A 'a'` actually captures `(ab)^13 a`, a 27-character word. The source then
consumes `ab` before its first replay, starting that replay 2 characters into
the original capture and overlapping it by 25 characters. Seq captures the
same word first and consumes the rotated residual `ba`. The theorem checks
that using unrotated `ab` at this position fails. Both proper grammars also
reuse the 27-character capture after `#`, recursively obtain an 11-character
capture from `(ab)^6 a`, and accept. Replacing the first block's final `a`
with `b` is finitely rejected by both strategies.

The block and phase suffix remain static per rule; the captured block count
and the input are unbounded. General nonperiodic overlap, runtime-dependent
phase selection, arbitrary body decomposition, multiple independent general
captures, and full Par/Seq equality or separation remain unresolved. This is
an additional restricted compiler, not yet a unification with the guarded
body-plan and absorbing-scanner compilers. Twenty-six new public axiom guards
cover the construction.


### Successful shifted replay forces periodicity of arbitrary captures

`CBV/OverlapNecessity.lean` moves periodicity from a syntactic head condition
to a necessary consequence of successful replay. `prefix_periodic` proves
for every nonempty word `u` and every word `w` that if `w` is a prefix of
`u ++ w`, then `u = left ++ right` and `w = u^n ++ left`, with a proper phase
prefix `left`. The proof peels whole copies of `u` until the remaining word
is shorter than `u`; it does not restrict the parser that produced `w`.

`rotations u` enumerates `drop i u ++ take i u` for `i = 0..length u`.
The final candidate duplicates the initial one for nonempty words and also
handles the empty shift uniformly. `prefix_iff_rotation` gives the exact
word-level equivalence between `w` being a prefix of `u ++ w` and existence
of a candidate `v` satisfying `u ++ w = w ++ v`. `rotation_unique` proves
uniqueness of the residual word, even when several candidate indices coincide;
`rotation_length` fixes its length to the shift length.

`actual_capture_rotation` connects that result to actual first-order Par
evaluation. An arbitrary first-order argument `a` successfully captures
`w = pre x p q`; if the source expression `lit(u) param(0)` succeeds from
the original position `p`, then the residual belongs to `rotations u`.
The argument may be capture-dependent, recursive, and part of the user
grammar: no closedness, independent-component, singleton-alphabet, or
block-safety condition is assumed. Actual sound-table semantics supplies
the two prefixes of the same input; length comparability derives the word
premise. `actual_capture_periodic` obtains the complete periodic normal form
for every nonempty shift. `rotated_execution` proves that some such residual
literal succeeds after capture at exactly the original replay's final
position, in any target grammar/table.

This corrects the direction of the remaining fixed-literal overlap problem:
for this body shape, a nonperiodic captured word cannot be part of a successful
shifted replay. The missing step is an effective grammar construction that
filters the *actual selected capture* by its periodic phase, while preserving
source priority, failure, and undefined recursion. The finite candidates and
post-capture literal success alone do not supply that filter.

`rotation_choice_false_positive` proves the failure of that tempting shortcut
with actual physical tables. The argument captures `abac` on `abacab`; an
origin lookahead first verifies `ab`. The original Par body `ab param(0) !.`
finitely fails. A Seq replacement trying the rotation literals after capture
accepts the whole input, since the remaining `ab` matches a candidate.
The theorem also verifies that `abac` lacks the necessary periodic-prefix
property. This is a counterexample to that local compiler, not a language-class
separation.

No new unrestricted translation is claimed. A general phase filter and the
arbitrary consuming-body/multiple-capture cases remain open, as does the full
Par/Seq language-class comparison. Twelve new public axiom guards cover the
normal form, operational consequences, and counterexample.


### A generated recursive capture/state product

`CBV/RegularCaptureProduct.lean` constructs actual arity-zero PEG rules for
filtering consumed words by a finite-state machine. The source is a finite
graph with literal, sequence, ordered-choice, repetition, and negation nodes;
node references may be recursive. Each graph node remains an original query
rule. Additional rules are indexed by node, starting state, and ending state.
The finite state count and graph fix the generated grammar independently of
the input. Literal transitions use the actual literal word; sequence enumerates
intermediate states; repetition recurses through product rules; predicates
preserve the starting state.

This is executable construction and local semantic groundwork, not yet a
proved general product translation. `filter_rule` verifies the concrete
address/decode scheme and rule lookup. `grammar_firstOrder`, `helper_valid`,
and `original_installed` verify syntax and the independent original component.
Every product rule first queries its original node through an actual grammar
call. `filter_body_eval` and `filter_step` establish this guard at evaluator
and physical-round level: unknown queries remain unknown, failed queries
remain failed, and only a successful original query enters the state product.

Ordered choice branches on the original left query, not its state-filtered
version. `choice_commit` proves that a successful original left parse remains
chosen when its filtered continuation fails. `choice_eval_unique` proves the
intermediate-state enumeration law for success, finite failure, and undefined
continuations. `filtered` records the intended full result specification;
`literal_correct` verifies it for literal nodes when the original query has
its actual literal result. Closing the recursive table correspondence for
all graph nodes remains required.

Some nontermination properties are already unbounded theorems of the actual
construction. `left_cycle_undefined` covers a left-recursive graph on every
input, valid position, and physical round, for every in-range state pair.
`nullable_star_undefined` does the same for repetition of an empty successful
operand. A final-state mismatch cannot change these undefined computations
into finite rejection.

Kernel-checked physical tables additionally exercise:

- A recursive a/b/c scanner that captures both `ababa` and `abac` before `#`.
  The generated alternating-a/b filter retains `ababa` at the original
  endpoint and finitely rejects `abac`; the source graph is not block-safe.
- `ab / a`: requesting the state reached by `a` rejects the winning `ab`
  parse. Naively choosing between independently filtered alternatives would
  incorrectly select the shorter `a`.
- Greedy `a*`: a final-state request cannot stop repetition early. The whole
  greedy capture reaches the sink state rather than the state after one `a`.
- Negation: success retains the input position and starting automaton state;
  requesting a different ending state finitely fails.
- Prototype shift-`ab` caller wiring with an original `abac / aba` head.
  Generated state guards reject the prior `abacab` false positive without
  falling back to a different head capture. On `ababa`, the actual `aba`
  capture selects residual `ba`, and both source and target accept.

These executions validate concrete generated grammars at finite physical
rounds. They do not prove correctness for all graph/input/state combinations.
Outstanding work includes that global soundness/completeness correspondence,
normalization of general ordinary PEG syntax (including any/range atoms) to
the graph, and the unbounded caller-level observation theorem. The current
product has no parameter-bearing source nodes, and the shift caller wiring
is a prototype for `ab` with an EOF tail. General capture-dependent argument
filtering, arbitrary body decomposition, multiple independent captures, and
the full Par/Seq language-class goal remain unresolved. Twenty-six new public
axiom guards cover the established local and physical results.


## 2026-10-24: Recursive capture product correctness on every input

`RegularCaptureCorrectness` closes the global table correspondence left open
in the preceding section. For every valid finite literal/control graph,
valid finite-state machine, input string, node, position, and state pair,
`product_correct` equates the generated filter's canonical Seq result with
`filtered` applied to the original parser's canonical result. In particular,
undefined stays undefined, finite failure stays finite failure, a matching
successful capture retains its exact endpoint, and a successful capture with
the wrong final state becomes finite failure. There is no stopping,
nonnullable-star, acyclicity, or capture-length hypothesis.

The proof uses actual physical tables. `defined_at_fixed` transports any
finite source result to a physical fixed point, including source rounds
after the chosen fixed point. `row_at_fixed` establishes the installed PEG
body equations. `finite_success` inducts on the source approximation round,
with an inner strong induction on the remaining input position for star.
Every successful star iteration strictly decreases that position; nullable
iterations cannot yield a finite source success. `select_success` proves
that the intermediate-state enumeration follows only the actual first
capture's state, so later failure never selects another capture. Guards
handle failed and undefined source results directly.

`bound_fixed` eliminates a supplied fixed-point premise from the public
correctness theorem by proving that the evaluator's standard bound is itself
a fixed point. `canonical_helpers_eq` relates independent helper components
across grammar extensions and both CBV strategies. Consequently,
`product_source_correct` compares the generated Seq filter with the original
standalone Par grammar, rather than only with queries inside the generated
grammar. `product_observations` gives the corresponding unbounded successful
finite-observation theorem on the unchanged original strings and preserves
the exact remaining suffix.

This proves the generated regular capture filter, not a general Par-to-Seq
compiler. The graph still has no parameter-bearing source nodes and no
any/range atoms. Ordinary syntax normalization, phase-machine construction
for arbitrary shift words, and an unbounded theorem for the shifted caller
that consumes the filtered argument remain to be connected. General
capture-dependent filtering, arbitrary body decomposition, multiple
independent captures, and full language-class equality/separation remain
unresolved.

Validation: full `lake build` succeeds (825 jobs), including `Audit`. All
fourteen new public theorem guards use only standard Lean axioms. No bounded
execution or new semantic axiom is used to justify the global correspondence.


## 2026-10-24: Actual filtered arguments select arbitrary shift phases

`PeriodicCaptureMachine` constructs a concrete machine for any nonempty
fixed shift word `u`. Its states are the positions of `u` plus one sink.
`prefix_iff_nonsink` proves that its run on `w` is nonsink exactly when
`w` is a prefix of `u ++ w`. `run_rotation` proves the actual word equation
`u ++ w = w ++ phase u r` at the reached nonsink state. No primitive-period,
block-safe syntax, or capture-length hypothesis is imposed. The empty shift
already belongs to the earlier direct replay-fusion case; this machine and
the new caller theorem assume a nonempty shift.

`CaptureProductExtension` proves that every original and generated product
reference stays inside the zero-arity component. `component_valid` and
`component_installed` allow ordinary parameter-bearing rows to be appended.
`extension_call_eq` preserves canonical helper queries across these extensions
and strategies; `extension_product_correct` installs the complete filter
specification in the real caller grammar, without supplied semantic advice.

`FilteredOverlapCaller` then constructs an actual Par/Seq grammar pair.
The Par unary body is `(u param(0)) B`; the Seq grammar has one unary body
`(phase u r) B` for each nonsink state. Its caller enumerates these rows with
the corresponding generated state-filtered capture parser as the actual
argument. Thus the selected Seq call consumes and retains the original full
capture; the later continuation can replay or inspect that same value.
A failed continuation cannot make another state use a different winning
source capture. A sink capture makes source replay finitely fail and every
Seq candidate fail. An undefined capture remains undefined because the
nonempty phase list first queries the original undefined parse.

`evaluator_eq` proves equality of complete partial results at every input and
valid position. `observations_iff` includes finite failure and every successful
remaining suffix. `language_translation` supplies one fixed first-order
target grammar and start expression for all unchanged original strings.
The continuation `B` may contain parameters, literals, any/range atoms,
sequence, choice, repetition, predicates, and zero-argument calls into the
independent helper component. The capture parser itself is any valid original
literal/control graph, including mutual recursion, empty captures, cycles,
and nullable repetition; it need not have periodic capture syntax.

A kernel-checked physical execution uses shift `abc`, actual `abca` capture,
residual `bca`, and reuse of the complete `abca` after `#`. A nonperiodic
winning `abcx` capture is rejected by both real grammars.

This connects the previous global product theorem to actual unary caller
arguments and removes the old block-safe-head restriction for this entry
shape. It does not yet compile parameter-dependent general capture parsers,
recursive calls that replace the capture inside `B`, arbitrary body entry
shapes, or multiple independent captures. Any/range source-graph normalization
also remains open. Full Par/Seq equality or separation is still unresolved.

Validation: full `lake build` succeeds (828 jobs). All 35 new public theorem
axiom guards pass in `Audit` (34 use only standard Lean axioms, one needs no
axioms); the updated Audit build also succeeds. No new Lean warnings or
proof placeholders occur in these modules.


## 2026-10-24: Recursive user recapture with prefix-failure seeding

`RecursiveFilteredOverlap` extends filtered shifted replay to a recursively
called user body. One fixed nonempty shift `u`, one fixed original capture
node, and one fixed user-body template determine the source and target
first-order grammars. Raw call zero recaptures at the current input position;
raw call `j+1` invokes independent helper `j`. Parameters, ordinary atoms,
sequence, ordered choice, predicates, and repetition are recursively rendered.
Captures can have different unbounded lengths on successive calls. The
caller's old capture remains available after the child returns.

The ordinary bottom user tables cannot be compared round for round. A
nonperiodic successful head is rejected by the Seq argument filter before
entering a user rule, whereas Par needs a user step to reject its shifted
replay. `SeededClock` resolves this proof issue without changing either
installed grammar. `prefixSeed` initially records only a finite failure of
an installed sequence body's leading expression, evaluated with actual
frozen helper rows and bottom user rows. `prefixSeed_lower` and
`prefixSeed_upper` place it between ordinary frozen stages zero and one.
The resulting `frozen_le`, `le_frozen`, and `defined_iff` prove that seeded
iteration has exactly the original physical evaluator's finite results.
It cannot turn genuine undefinedness into a failed observation.

`rounds_lexical` connects all seeded helper queries to the canonical physical
evaluator. `rounds_failed_prefix` proves that a genuinely failed Word prefix
is failed from seeded stage zero onwards, independently of its continuation.
These are proof devices; no supplied capture oracle, seed table, or input
length appears in the final generated grammar or language theorem.

`entry_eq` compares actual phase-filtered unary calls from corresponding
user rows. `evaluator_of_rows` extends that comparison through the rendered
body's control and parameter uses. `tables_shifted` closes the recursive row
correspondence by user-stage induction: the initial probes agree by the word
rotation equation, and each subsequent stage uses the previous stage for
its recursively rendered continuation. `evaluator_eq` preserves the full
partial result at every seeded stage, environment, and valid position.
`observations_iff` removes seeding using physical cofinality and preserves
all finite failures and successful suffixes of the real source/target
grammars. `language_translation` supplies one fixed target grammar and
start expression for all unchanged original strings.

A kernel execution checks actual capture endpoints: the parent captures
five-character `ababa`, and a child call later captures three-character `aba`.
The complete input `abababa#ababa!ababa#aba?ababa` is accepted by both actual
physical grammars. Replacing the final parent copy by the child's shorter
`aba` is rejected by both. Thus the parent value is retained across return
from recursive fresh capture.

This closes recursive capture replacement for one fixed independent capture
parser, shift, and user-body template. It does not yet unify several such
user families with different heads/shifts, compile capture parsers depending
on incoming parameter values, support arbitrary body entry positions, or
handle multiple independent general arguments. Ordinary graph normalization
of any/range source atoms remains open. General Par/Seq language-class
equality or separation is still unresolved.

Validation: full `lake build` succeeds (830 jobs), including `Audit`. All
34 new public theorem axiom guards use only standard Lean axioms. Both new
modules compile without new warnings or proof placeholders.


## 2026-10-24: Full transition profiles for parameter-dependent arguments

A final state from one start state is insufficient metadata for a retained
capture reused inside a later argument. `single_phase_insufficient` checks
this with shift machine `aab`: `a` and `aaba` both take state zero to state
one, but from state one they end at states two and three respectively.
The same retained value can be replayed after another argument prefix, so
its behavior from other start states matters.

`CaptureTransitionProfile` represents a word by the array of its resulting
states from every start state. `profile_mem` places every unbounded captured
word's array in the fixed enumeration `profiles D`; `profiles_length` gives
its size `width^width`. `compose_correct` computes the profile of a
concatenation from the two finite arrays alone, without inspecting either
retained word. None of this restricts actual capture lengths or replaces
retained strings with a finite word palette.

The profile is executable information, not a supplied semantic answer.
`guard` uses lookaheads of the actual generated state-filtered capture calls
for every starting state. `guard_correct` proves exact profile discrimination
on the original committed capture, preserves undefined and failed original
queries, and leaves the caller position unchanged. `select_correct` chooses
a continuation from the finite profile list at the origin; a later failure
cannot choose another capture or a different profile. These are unbounded
canonical evaluator theorems on the generated helper grammar.

`DependentCaptureFilter.Expr` then adds retained parameters to finite parser
control: literals, parameters, independent recursive helper calls, sequence,
ordered choice, and negation. An inline generated filter uses finite incoming
profiles for parameter replay, the existing product for fresh helper captures,
and real source queries for ordered-choice commitment. `correct` preserves
the complete filtered result for every valid expression, input, environment,
and state pair with accurate incoming metadata. Fresh helper calls can
capture new arbitrarily long words, so these arguments are not merely Word
expressions over a fixed environment.

`render_eq` relates original Par and Seq argument evaluation for this syntax;
`correct_par` gives the filtered Seq result against the original Par query.
`guard_accurate` derives the incoming metadata condition from an actual
successful profile guard on the previous capture. `guarded_argument_correct`
therefore justifies the parameter-dependent filter after the previous capture
has advanced the input position, using the retained original string and its
actual generated guard instead of a semantic profile premise.

A bounded kernel execution additionally constructs real profile-specialized
unary Seq rows. It captures `a` or `b`, selects the complete profile through
lookaheads, retains that character as the actual argument, and parses
`c + param(0) + fresh b*`. `a#cabb#` succeeds and `b#cbbb#` fails for requested
state zero. Both old words have state zero from zero. Deliberately supplying
the `a` profile with retained `b` would wrongly pass the inner filter; the
actual profile selector prevents that inconsistency in the execution.

This closes finite-control parameter-dependent argument filtering, not the
complete recursive parameter-dependent call translation. Selecting the new
argument's full profile and threading it through specialized recursive user
rows still need an unbounded caller correspondence. Parameter-dependent
repetition and general parameter-bearing recursive parsers are outside this
inline syntax (independent helpers may already recurse and repeat). Multiple
user families, general body entry and independent arguments, ordinary graph
normalization, and full Par/Seq language-class equality/separation remain
unresolved.

Validation: full `lake build` succeeds (832 jobs), including `Audit`. All
29 new public theorem axiom guards use only standard Lean axioms. The new
modules have no proof placeholders or Lean warnings.

## Retained-value-dependent fresh captures through recursive specialized rows

`ParametricHelperControl` transports helper-only control with retained
parameters between arbitrary appended caller grammars and arbitrary seeded
user stages. Closing parameters by literals reduces it to the existing
independent-helper theorem. This also moves the dependent argument filters
into real callers without a semantic helper-table assumption.

`DependentProfileCall` selects the complete transition profile of the actual
new argument by generated product-query lookaheads. Its continuation is an
actual unary call to the corresponding appended profile-specialized rule.
`entry_par_correct` proves that the value, endpoint, and profile address are
those of the original Par argument, including undefined and failed queries.
The incoming profile condition remains explicit here and is discharged by
the recursive compiler below.

`ProfiledDependentRecursion` extends the earlier recursive shifted-replay
compiler: call zero now evaluates a fixed argument expression A in the
current retained environment. A may combine retained parameters with fresh
captures from an independent recursive helper graph, literals, sequence,
ordered choice, and negation. Every new value's entire transition profile
chooses the target row, whose recursive calls use that new profile.
The body template allows literals, parameter replay, helper calls, recursive
call zero, sequence, choice, star, and negation in arbitrary combinations.
The source row has prefix `(u param(0))` for a fixed nonempty u; the target
row has the corresponding rotation prefix followed by the translated body.

All profiles, including ones whose transition from zero is the sink, are
installed. Sink rows have a failing prefix, so the same physically bounded
prefix seed works at the bottom stage. `tables_shifted` proves the complete
recursive row correspondence by induction; `evaluator_eq` carries it through
body control. `observations_iff` removes seeded stages using physical-table
cofinality, preserving every finite success/failure observation on unchanged
original strings. `language_translation` produces one fixed first-order Seq
grammar and entry for every member of this source family. No incoming
semantic profile premise remains in that language theorem.

The physical-table kernel execution initializes a parent capture `aba`, then
captures `aba + fresh ba = ababa` in its child. After return the parent must
still replay `aba`; replacing the parent's final copy by the child's longer
`ababa` is rejected by both generated grammars.

This extends the earlier independent-capture recursion theorem to arguments
that depend on the retained value. It still assumes a single fixed unary
user body/argument family and the explicit shifted-replay entry shape.
Parameter-dependent star and recursive user calls inside A, multiple user
families and independent arguments, and normalization of arbitrary original
source grammars are not covered. Unsupported raw higher-order or
parameter-bearing-call syntax is rendered as failure, not claimed to be
preserved. General Par/Seq class equality or separation remains unresolved.

Validation: full `lake build` succeeds (835 jobs), including `Audit`. All
36 added public theorem axiom guards use only standard Lean axioms or no
axioms. The three new modules have no Lean warnings or proof placeholders.

## Mutual user families with distinct arguments and bodies

`MutualProfiledRecursion` removes the single-user-family restriction of the
preceding compiler. A finite list of unary users each supplies its own
retained-value-dependent argument expression and its own body template.
A body may call any other member, including itself, under sequence,
choice, repetition, and predicates. Every member uses the same fixed
nonempty shifted prefix `(u param(0))` before its distinct body.

The target user address is selected from a finite enumeration of pairs
`(callee index, complete capture profile)`. `selected_call` connects actual
generated profile queries to the installed unary row and the original Par
argument value/endpoint. `tables_shifted` proves the simultaneous row
correspondence for all members and stages. `evaluator_eq` extends it through
body control, and `observations_iff` removes the seeded clocks to preserve
finite observations on unchanged input. `language_translation` builds one
fixed first-order Seq grammar for the entire mutually recursive family;
its hypotheses are syntactic argument/helper validity and a nonempty shift.

The kernel execution uses two different rules and both directions of their
call cycle. The first independently captures `aa`; the second captures the
retained `aa` followed by a fresh `a`, giving `aaa`, and then calls the first
again. Both grammars retain `aaa` and `aa` across the nested returns, and
reject a shortened `aa` substituted for the middle rule's retained `aaa`.

The common shift is still a restriction: different shifts would require
joint metadata for their phase machines or a corresponding combined
filter. Argument expressions still exclude retained-parameter-dependent
star and user calls. Multiple independent arguments, arbitrary body entry
shapes, and normalization of arbitrary original source grammars are still
open; this is not a general language-class equality or separation result.

Validation: full `lake build` succeeds (836 jobs), including `Audit`. The
17 additional public theorem guards use only standard Lean axioms. The new
module has no proof placeholders or Lean warnings.

## Different fixed replay prefixes within one recursive family

`CaptureMachineFamily` forms a disjoint union of any finite list of word
transition machines. Embedded component runs remain in their own component;
`profile_component` recovers any component's transition from the union word
profile. `phase_profile` specializes this construction to a list of distinct
fixed replay shifts, including an arbitrary number of user rules. The
transition metadata is still finite and depends only on the fixed grammar.

`HeterogeneousProfiledRecursion` gives each unary user its own argument,
nonempty literal shift, and body. It generates filters for the union machine
and specializes target rules by `(callee index, union capture profile)`.
The callee's actual shift selects its embedded start state; the target
rotation is obtained by subtracting the component offset from that profile
entry. `tailPrefix_actual` proves this is the original phase machine's
rotation for the actual captured word. Thus a profile for one shift is never
silently reused as the phase of a different shift.

The simultaneous recursive row theorem, body evaluator equality, all finite
observations, and fixed-grammar language translation now hold for finite
mutually recursive families with different shifts. These language theorems
have no semantic metadata premise: helper/argument validity and nonempty
literal shifts are the stated conditions. The input remains the original
character string throughout.

`HeterogeneousReplayExamples` computes the joint profile of `aaba` for shifts
`ab` and `aab`: it is a sink from the first start and phase one from the
second. A distinct-shift mutual example uses prefixes `a` and `aa` with
captures `aa → aaa → aa`, retaining each ancestor value after nested return.
The original grammar's success and bad-copy failure are checked on physical
finite tables. The generated Seq grammar's corresponding finite observations
are derived from the unbounded compiler theorem, rather than a separate
bounded evaluation of the larger generated profile grammar.

Fixed shifts may now differ between users. The shifted-replay body-entry
shape itself is still required. Retained-parameter-dependent repetition or
user calls inside arguments, multiple independent arguments, and normalizing
arbitrary original source grammars remain open. General Par/Seq equality or
separation remains unresolved.

Validation: full `lake build` succeeds (839 jobs), including `Audit`. All
34 additional public theorem guards use only standard Lean axioms or no
axioms. The three added modules have no proof placeholders or Lean warnings.

## Retained Word repetition inside capture arguments

The dependent argument syntax now includes `star a` when `render a` is a
Word expression: retained parameters, literals, and their concatenation.
These new stars compose with the existing fresh independent helper captures,
sequence, choice, and predicates. Their iteration counts and captured word
lengths are unbounded. Star over an arbitrary helper-dependent or recursive
argument is not included in this extension.

`CaptureOrbit` proves that every count n of a bounded deterministic state
transition has a finite descriptor `(k,l)`: either exactly k steps (l=0), or
k steps followed by any number of l-step cycles. Prefix and cycle lengths
are bounded by the machine width. The proof covers transient states and
cycles, not just permutations or idempotent word profiles.

`InlineRepeat` renders a descriptor as a fixed number of inline copies,
optionally a star of an l-copy block, and the original parser's stopping
test. On a successful source repetition, its exact count specification is
proved using strictly decreasing traces and grouped greedy evaluation.
A candidate either consumes the entire original greedy capture or fails;
it cannot accept by shortening the original repetition.

`WordStarFilter` computes the repeated Word's transition from finite incoming
profiles and literal profiles. Its actual PEG filter begins with a lookahead
of the original star to preserve undefined empty iteration, and then chooses
among the finite descriptor expressions. `correct` proves complete filtered
partial results for every valid finite machine, accurate incoming metadata,
sound CBV table, and input position. There are no parameter-bearing helper
calls: every repeated parameter remains in the current environment.
Missing parameters still yield zero iterations; empty successful Word values
still make star undefined.

This filter is installed in `DependentCaptureFilter` and transported through
`ParametricHelperControl`. Consequently the existing complete single-user,
mutual-user, and heterogeneous-shift language theorems now also admit these
retained-Word stars inside new capture arguments.

Kernel executions check greedy `aba` repetition on `abaaba#`: the full
six-character capture reaches the sink of the `ab` machine, and a phase-one
filter rejects rather than stopping after the first copy. Empty retained
values remain undefined and missing parameters permit zero iterations.
A real source user retains `abab`, passes its greedy two-copy repetition
`abababab` to another user, and then reuses the parent's original `abab`.
The shortened child copy fails. The corresponding generated Seq observations
are derived from the unbounded language compiler theorem.

General capture-dependent star bodies, user recursion inside arguments,
multiple independent arguments, arbitrary body entry shapes, and general
original-grammar normalization remain unresolved. No general Par/Seq
language-class equality or separation is claimed.

Validation: full `lake build` succeeds (843 jobs), including all existing
and 45 added public theorem axiom guards in `Audit`. They use only standard
Lean axioms or no axioms. The four added modules and modified argument/filter
modules have no proof placeholders or Lean warnings.

## General retained-dependent argument repetition by first returns

`FirstReturn` constructs inline state-constrained paths by eliminating the
current state from a finite allowed-state list. At state q, a star consumes
first-return loops to q which avoid the final target and eliminated states;
a final exit reaches the target without visiting q again. Removing q reduces
the allowed-state list, so this is a finite PEG expression generator, not a
parameter-bearing recursive helper. `hit_correct` proves the first-target
semantics on every real finite iteration path. `returns_correct` then
consumes all complete target-return loops and applies the original stopping
test. This prevents accepting a shorter source-repetition prefix.

`GeneralStarFilter` lifts every successful original greedy repetition to
such a state-annotated path using the correctness of its one-step filters.
It preserves complete filtered partial results, with an initial lookahead of
the original star retaining undefined or empty-iteration behavior. No
uniform-word, fixed iteration-profile, or non-nullability premise is used.
Different iterations may consume different strings and take different state
transitions.

The `DependentCaptureFilter.Expr.star` validity condition is now recursive
argument validity, replacing the earlier Word-only condition. Its filter
uses this general inline construction. The first-order, safe-helper-control,
Par/Seq argument equality, and full filter specifications have been extended
accordingly. Thus nested stars, ordered choices, predicates, retained values,
and fresh independent recursive helper captures may be mixed inside new
arguments to every existing recursive language compiler.

The kernel example repeats an argument producing `a`, `ab`, `abb`, and
`acac`, with the final token itself using retained-dependent nested star.
The odd-b state filter accepts the complete capture; the even-b filter
rejects. A nested empty iteration remains undefined. A second actual source
example retains `abab` and captures a new child value by a fresh six-character
helper iteration followed by a retained four-character iteration, then uses
the original parent value after return. The source physical tables verify
success and a shortened-child failure; the generated Seq observations follow
from the unbounded recursive compiler theorem.

Repetition inside the supported argument syntax no longer has a Word-only
restriction. Parameter-bearing user calls inside arguments, multiple
independent arguments, the required shifted-replay body-entry shape, and
normalization of arbitrary original source grammars remain unresolved.
General Par/Seq language-class equality or separation remains unproved.

Validation: full `lake build` succeeds (846 jobs), including `Audit` and
30 additional public theorem guards. Fifteen existing guard expectations
were updated to include the actual standard `Classical.choice` dependency
from the new well-founded state-elimination definitions. All dependencies
remain standard Lean axioms or none; the new/modified modules have no proof
placeholders or Lean warnings.
