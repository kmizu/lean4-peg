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

## 任意の一階Seq文法の全域化と、元文字列上の補集合閉包

`SequentialTotalSyntax/FirstOrder/Arguments/Routes/Calls/Layout/Atoms/Expression/Stages/
Correctness/Compiler/Language` は、**任意の一階 Seq 文法・開始式の全域化**を証明した。
入力・入力長・保持語を引数に取らず、元の N 規則から厳密に `4*N*(N+2)` 規則を生成する。
各元規則に arity を保持する success/zero/positive/failure の四規則と、段階 0..N の
空環境用 nullary 四規則を置く。source の停止性、有限 word palette、alphabet、
call graph、delimiter/anchor、actual の構文について追加条件を置かない。
相互 parameterized recursion、actual 内の call、任意 incoming 環境、不正 index/
arity/parameter の有限失敗も扱う。

`SequentialTotalCorrectness.position/expression` は、任意入力の任意の有効位置と
任意保持環境で、四 mode の実 target canonical 表を元の実 source 結果へ同定する。
元の成功残余は保持し、元の有限失敗と未定義は success flag の有限失敗へ移す。
failure flag は**元が有限失敗した場合だけ**空成功し、元が未定義なら有限失敗する。
そのため source の undefined choice/not/star を誤った正常制御へ変えない。
`total_at` は target の実 physical clock
`(4*N*(N+2)+1)*(x.length+1)` で、全 mode が必ず `some result` を返すことを示す。
`total_observation` はこれを元の実 `SObs` の有限観測へ接続する。
これは既存の Seq clock 上界を用いた全域性で、時間・空間計算量を改善した主張ではない。

一般 call の実引数は最初の正の消費箇所ごとに経路を作る。そこまでの actual は zero、
その一つは positive、その後は full-stage success で評価する。
`full_success/routes_correct` は**各捕捉文字列の全リストと最後の残余位置**を保存し、
callee continuation が失敗・未定義でも別のタプルを選ばないことを証明する。
全 actual が空なら empty helper を使い、段階 0 では全 flag が有限失敗する。
段階 j+1 の helper は元本体へ空語を代入して段階 j で変換する。
正の消費後は小さい残余長へ移るため full-stage に戻せる。
`position` は残余長の強帰納と段階の帰納で、Calls/Expression の全 row 仮定を外す。
source の位置ごとの `rounds_j` と、生成文法の実 row を接続した証明である。

連接・優先選択・否定・反復の制御法則は `SequentialTotalControl` にある。
反復は positive parser の star の後に元の finite-failure flag を要求する。
これにより nullable/undefined な停止点が反復の正常終了に化けない。
`successes_iff/recognizes/language_translation` は、全入力の成功残余と、
**同じ元文字列の全入力消費言語**を固定 Seq 文法で保存する。

`SequentialTotalLanguage.complementStart` は
`!(start(g,e); !any); any*` を生成する。EOF を含む全入力受理を否定するので、元の
途中までの消費成功も補集合へ入る。`complement_recognizes` は任意 `List Char` で
この固定 target の受理が元の非受理と同値であることを証明する。
`Shallot.PegSeparation.firstOrder_seq_complement` は
`IsFirstOrderCBVPEL .callByValueSeq L → IsFirstOrderCBVPEL .callByValueSeq (¬L)`
を、実文法生成と実 `SObs` によって示す。元の無限未定義による非受理も含む。

15 個の example 定理では、空呼出し鎖、fallback/否定を含む循環、nullable 反復、
複数 actual の個別捕捉、正消費後の引数有限失敗と未定義、保持値を使う再帰と親への
backtracking、相互 parameterized call、不正 call preflight、補集合の EOF 判定を
kernel 検証した。さらに、実循環の補集合が全元文字列を認識することと、既存の
fresh doubled tuple/parent-return 文法について**全初期長・全再帰深さ**で新 target が
全入力を受理することを記号的に証明した。一般定理はこれらの具体例に依存しない。

今回の追加は 10 modules・56 guard。全 1,378 jobs/Audit と関連 3,634 公開定理の
依存検査を通過（標準 Lean 公理 3,553、無公理 81）。PR69 全体は新規 Lean
68 modules・559 guard。新しい axiom/sorry/native_decide は置いていない。

この結果は Seq→Seq の全域化と補集合閉包であり、**一般 Par→Seq の文法変換や、
Par/Seq 言語クラスの一致・分離を証明したものではない**。元の同じ位置から評価した
一般 Par actual の live な捕捉値を Seq へ移す問題が残る。

## 入力位置の再帰と有限な空呼出し閉包で、元のSeq評価を再構成する

`FiniteResultClosure` と `SequentialLocalClosure/Order/Correctness` は、厳密に
小さい残余長の行を固定し、現在位置の空引数環境の結果だけを反復する。
状態は元規則ごとの `Res` 一つで、規則数 N なら N 回で最小固定点へ到達する。
`None` は未定義、`some none` は既知の有限失敗であり、両者を同一視しない。
保持文字列の候補集合や引数タプルの列挙は不要で、arity に依存した状態数を置かない。

`saturated_eq_source` はこの局所閉包と元の実規則行との完全一致を証明する。
`expression_eq_source` は任意の incoming 環境と式へ持ち上げる。小さい残余長では
任意の実保持値の組を扱い、現在位置の空環境と混同しない。局所単調性と行一致は
実際に到達可能な有効 arity の行だけを比較する。

`SequentialPositionEvaluator.column/run/decide` は、小さい残余長を自分自身の
再帰で計算する実行可能な評価器である。定義中に元の `tblV` や canonical 表を
oracle として呼ばず、式評価エンジンに自身の下位行と局所閉包を渡す。
`decide_eq_standard`、`observations_iff`、`undefined_iff` は任意の一階 Seq
文法・開始式・元文字列で、元の成功残余・有限失敗・全 clock 未定義を保存する。
規則数回が必要な鎖、fallback/否定を含む真の循環、nullable star、正の実引数、
25 引数で一規則の例、不正 call/arity/parameter を kernel 検証した。
新しい倍長値と親復帰を含む任意初期長・任意再帰深さの既存文法にも接続した。

これは Lean の停止する評価器であり、未定義は返り値 `None` として表す。
この評価器単独では固定 Seq 文法を生成しない。上の全域化・補集合閉包の文法生成と
区別する。一般 Par→Seq 翻訳は未解決。密な入力位置のリストと再計算を含むため、既存の
時間・空間上界を改善したとも主張しない。既存の stationary/clock 定理を再利用し、
凍結下位行の局所最小固定点の同定と、自前の位置再帰評価器を接続した結果である。

検証は全 1,364 jobs/Audit 成功、関連公開定理 3,542 件の依存は標準 Lean 公理
3,464 件または無公理 78 件。今回の追加は 6 modules・49 guard。
PR69 全体は新規 Lean 54 modules・467 guard。一般の言語クラス比較は未解決。

## 任意の一階Seq文法を、通常評価・ゼロ結果・正の消費へ分ける

`SequentialResultSyntax/Normal/Zero/Compiler` は、**任意の一階 Seq 文法**から
通常規則とゼロ結果観測規則を生成する。前者は元 arity を保持し、後者は全て nullary。
規則数は厳密に元の二倍で、変換は入力や runtime の保持値に依存しない。
source declaration/root の特殊な DSL、一つの self call、covering anchor、有限 word
palette、alphabet 条件、正規表現引数、停止性の制約は付けていない。
範囲外の call、arity mismatch、範囲外 parameter の元の有限失敗も保存する。

根拠となる Seq の stationarity と empty-configuration の固定点は、既存の
`SequentialCaptures` / `SequentialClock` にある。今回の新しい接続は、これらを使い、
引数つきの一般再帰規則について、実引数評価・実表・本体のゼロ結果観測を同じ
physical clock で構成する部分である。同じ入力位置で成功した Seq call の実引数は
全て空語なので、ゼロ結果用 callee は元の全 parameter を空語へ代入した nullary
規則としてよい。一方、fresh actual の評価は各入れ子の通常/ゼロ observer で扱う。
元の呼出しが有限成功しなければ先へ進まない full gate を置き、観測しない経路の
未定義を落とさない。

`SequentialResultCompiler.physical` は任意 E・任意一階式・全入力位置・全 clock で、
通常評価の完全一致と、ゼロ結果の `EmptyResultObservation.project` 一致を証明する。
`positive_physical` はゼロ成功だけを落として正の消費の残余を保持し、
`positive_success_strict` はその成功が必ず入力を進めることを示す。
`failure_physical` は有限失敗だけで空成功し、元の未定義は未定義のままにする。
`zero_success_language` は、元の式が元入力を残して成功する文字列集合を、
`zero(e); any*` による固定 Seq 文法で**同じ元文字列上の全入力消費言語**へ変換する。
通常 clone は元の受理言語をそのまま保持する。

例では all-empty actual の nullary observer、正の actual を持つ空成功 callee、
committed choice、無効 call/arity/parameter、nullable star、skip される経路の真の
再帰未定義を検証。既存の tuple 再捕捉文法についても、任意の初期長と再帰 depth
で、新しい倍長の値と親復帰を含む全入力の通常/ゼロ/positive 観測を記号的に接続した。

この観測変換は **Seq→Seq** で、一般の Par→Seq 変換そのものではない。未定義を
有限失敗へ変えていないため、任意プログラムの totalization や、任意の Seq 言語の
補集合閉包をこの観測変換単独から主張しない。別の `SequentialTotal*` が上記の一般
全域化・補集合閉包を証明する。既にある有限
stationary-state の議論と、ゼロ/positive/failure の実際の文法生成を分けて接続した。

関連研究として、[2019年の原記事](https://kmizu.hatenablog.com/entry/2019/10/24/145039)
で両 CBV のタグ照合例を再確認した。また Chida–Terauchi の
[FSCD 2022論文](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.15)
は、後方参照付き正規表現に先読みを加えた場合の分離を示す。ただし、これはここでの
再帰 PEG の二つの CBV クラスの同定・分離を与えない。論文自身の Remark 11 でも、
先読み境界を越える後方参照を許す/許さない場合の比較は別の課題とされている。
その結果を Par/Seq の分離として流用しない。

全体 `lake build`/Audit は 1,358 jobs を通過。関連 3,493 public 依存報告は標準公理
3,417 または無公理 76。この追加は五新モジュール・36 guard、PR69 全体は 48 新
Lean モジュール・418 guard。一般 Par/Seq 言語クラスの一致・分離は未解決。

## 現在位置以降だけに必要な保持値を残す

`FutureCaptureViews` は既存の global な `CaptureViews.evV_rebind` と異なり、
現在の残余長 bound 以下の位置で parameter view が一致すればよいとする。
任意の一階式・入れ子の Par/Seq actual・任意の sound な再帰表で成立し、
実 physical table では文法の一階性から soundness を自動的に得る。
成功した評価は残余長を増やせないため、継続は切断点より前の入力へ戻らない。
元/変換後はこの補題では同じ文法・同じ戦略を使う。

`FutureCapturePruning.mask` は bound より長い保持語の payload を空にし、
対応する parameter view を必ず `failAlways` にする。他の index と空の元捕捉は
保存する。単に空語へ置き換えるだけでは失敗が空成功になるため不正である。
全 payload 長が bound 以下になり、変換した任意の本体・新 actual 評価は、
元の保持値を使った評価と全 physical clock で一致する。
`after_prefix` は任意の一階 prefix が実際に進めた位置へこの操作を接続する。
prefix や本体に covering anchor の構文条件はない。

`forget_iff` はさらに、**任意の一階継続と全 future 位置について一括して**
全環境を忘れてよい必要十分条件を与える。それは、どの保持語も、その残余の
どの suffix とも一致できないこと (`DeadAfter`) である。`deadCheck` は現入力と
保持値からこの条件を有限判定し、長さだけでは見落とす内容依存の死活も扱う。
特定の一つの本体で値を忘れられる必要条件、と主張しているわけではない。
元の空語は常に照合できるので、nullable star の未定義を保つためにも残す。

忘却はこの継続の内部に限る。外側の選択フレームが切断点より前へ backtrack
する可能性があれば、親側の元 binding は依然必要である。実入力 `aaaa!aaa` で、
枝内で死んだ `aaaa` を親まで消すと、外側 fallback の成功が失敗になることも証明した。

例では同じ原点の任意長 `a^(n+4)`、短い `a`、空語の tuple を扱い、長い prefix
の後の `aaa` 上では最初の payload だけを消す固定 view が、任意の一階本体・
再帰・全 clock で正しいことを証明した。再帰 actual、空語による反復未定義、
view を付けない空置換の誤り、切断点より前へ pruning を適用する誤りも kernel
検証した。

これは現在の保持値と bound に依存する**評価上の表現・忘却定理**であり、入力に
依存しない固定 Seq 文法を生成する新 compiler ではない。既存の anchor 条件を
compiler から除けたとは主張しない。値を忘れられる条件を明確にし、残す必要のある
live な値を anchor なしで扱う問題と分けた。一般の Par/Seq 一致・分離は未解決。

全体 `lake build`/Audit は 1,353 jobs を通過。関連 3,457 public 依存報告は標準公理
3,381 または無公理 76。この追加は三新モジュール・26 guard、PR69 全体は 43 新
Lean モジュール・382 guard。

## 個別の保持値を渡す、多引数の自己再帰まで

`RecursiveFieldSyntax/Correspondence/Compiler` は、個別 field 再捕捉を
parameterized self call の本体まで接続する。元文法は独立 nullary helper prefix と、
任意正 arity の一つの自己再帰 header `H(W) <- P(W); body(W)` を持つ。
`body` は raw 一階 `MExp` の通常制御、各 parameter の個別使用、helper 呼出し、
新 actual を持つ `H` 呼出しを組み合わせられる。開始式も一般の検査済み raw 式である。

各呼出しは元順序の actual preflight と先頭 `P` の検証を行い、その呼出しで新しく
得た各値を実 Seq 引数へ捕捉する。`TupleFieldTransfer.physical_of_body` は異なる
元/変換後本体を許す局所 interface に一般化した。
`RecursiveFieldCorrespondence.physical` はこれを実 physical clock の帰納法で
閉じる。再帰先本体の同値や eventual table の一致を外部仮定として残さず、全ての
新 tuple と入力位置で、同じ clock の元/変換後式の評価一致を証明する。

`DelimitedValueSafety` は fresh actual が separator を含まないことを証明する。
正に消費する actual は保持 parameter、separator-free literal、通常の選択/反復/
連接を用いる。否定 query 内には任意の構文検査済み再帰 call を許し、その部分的
計算を保持する。正に消費する actual 内の call はこの検査ではまだ拒否する。
各 call の arity/scope、pattern の非空・全成分 coverage、helper 閉包、本体と開始式、
実 source declaration/root 全体を有限検査し、元文字列言語・残余・失敗・全 clock
未定義の保存へ接続した。

`RecursiveFieldProofs.source_and_target_all_trees` は任意の n と再帰 depth で、
元の二保持語 `aⁿ`, `aⁿb` から child の `a^(2n)`, `a^(2n)b` を実際に新捕捉し、child から
戻ったら親の long/short を個別に再利用する入力族を認識する。`row_all_trees` は
任意の外側入力・残余でも成立する。Seq 文法は常に arities `[1,1,6]` の三規則で、
元の一規則 `[2]` と同じ `depth+1` clock で動く。静的な有限 word palette や
子の値を親へ漏らす代入ではない。初期捕捉と fresh doubled capture も記号的に証明。

kernel 実行では初期長 0/1/2 と depth 0/1/2/3、誤った親復帰の拒否、source declaration
改変・coverage・actual separator・未検証の正の producer call の拒否を確認した。
部分的な actual は全入力・全 clock で両戦略とも未定義になり、空の保持語が生む
nullable star の未定義も伝播する。

全体 `lake build`/Audit は 1,350 jobs を通過。関連 3,431 public 依存報告は標準公理
3,355 または無公理 76。六新モジュールと局所 interface の追加で 44 guard、PR69
全体は 40 新 Lean モジュール・356 guard。必須 covering anchor、separator-free
actual、単一 parameterized self-recursive header という条件は残る。任意の複数
parameterized callee 間の相互再帰、正の actual 内の一般 producer call、anchor-free
文法の一般変換、Par/Seq 全言語クラスの一致・分離は未解決である。

## 検証した先頭ブロックから、元の各保持語を個別に捕捉し直す

`CopyFieldCapture` と `TupleFieldControl/Transfer/Compiler` は、必須の先頭
`P(W) = W[j₀];d;W[j₁];d;…` が全成分を含む場合、その実入力上の各語と
区切り文字を別々の Seq 引数へ捕捉する。生成する引数は各出現につき
`[gap(d), chr(d)]` の二つで、実捕捉値は `[W[j₀], [d], W[j₁], [d], …]`。
元の Par 引数の捕捉範囲が重なっていても、先頭ブロック中のコピーを実際に
消費して取り直す。語の値を生成構文へ埋め込まず、仮想入力も使わない。

`CopyFieldCapture.expression_view` は、元の各 parameter を対応する偶数位置へ
代入すると、任意の一階式・任意の戦略/再帰表・任意の後続位置で評価が一致すると
証明する。この値の表現定理は引数つき呼出しも含む。範囲外の元 parameter は
失敗のままで、追加の区切り文字用/重複用引数が漏れ出さない。
`scan_encoded` と `entry` が、この環境を実 Seq 引数評価で生成して実規則へ
入ることを証明する。

戦略間の変換は別に検証する。`TupleFieldControl` の本体は各成分を個別に使う
raw `MExp` で、任意の通常の選択・否定・反復を許す。内部の呼出しは独立した
nullary 再帰 helper に限る。`TupleFieldTransfer.physical` は任意の caller 環境と
元/変換後 actual の局所対応を仮定し、元 actual の preflight、先頭一致確認、
各語の再捕捉、本体評価を同じ physical clock で接続する。先頭が不一致のときは
有限失敗し、actual や本体の未定義も保存する。

`TupleFieldCompiler.check` は helper 閉包、原 actual の通常構文とアルファベット
効果、区切り文字不在、先頭 pattern の scope/全成分 coverage、本体 scope を
有限検査する。helper prefix と一つの parameterized header からなる実文法を
生成し、閉じた actual を持つ開始呼出しについて、全入力の残余・失敗・元文字列
言語・全 clock 未定義の保存を証明した。以前の parameterized recursive client
frontend への接続は、この追加ではまだ行っていない。

`TupleFieldExamples` は任意の n で、同じ位置から重ねて捕捉した `aⁿ` と `aⁿb`
を `[1,0,1]` の先頭ブロックから六つの実引数へ取り直し、後続の `aⁿ!aⁿb` を
個別再照合で受理することを証明する。後続は常に先頭ブロック全体より短く、
その位置で opaque なブロック全体の再照合は失敗する。元一規則 `[2]` から
固定三規則 `[1,1,6]` を生成する。先頭一致確認の省略による実誤受理、coverage/
区切り文字/parameter scope 検査、個別語の反復と否定、再帰 helper の正確な
clock、nullable star の全 clock 未定義も kernel 検証した。

全体 `lake build` と Audit は 1,344 jobs を通過。関連 3,387 public 依存報告は
標準公理 3,312 または無公理 75。この追加は五モジュール・52 guard、PR69 全体は
34 新 Lean モジュール・312 guard。必須で全成分を含む先頭ブロックなしの変換、
本体内の任意の parameterized call、既存再帰 client との接続、一般 Par/Seq
一致または分離は未解決。一般の値表現定理と、この制限つき戦略変換を区別する。

## 固定ブロック後の一般制御で、一周ごとに消費語が変わる反復へ

`CopyPeriodControl` と `ControlledPeriodTransfer/Syntax/Correspondence/Compiler` は、
固定の非空 delimited parameter 列 `P(W)` の後に制御 `T` を持つ本体

```
H(W) <- (P(W); T[P(W)])*
```

を元文字列上の Seq へ翻訳する。`T` は block atom、空成功、any/chr/range/literal、
独立 nullary helper 呼出し、連接、優先選択、否定、反復からなる有限構文である。
block atom は常に元の `P(W)` 全体を再照合する。helper は prefix 内で再帰してよく、
一周の後半が消費する文字数・語・選択経路は入力に応じて変わる。
後半には消費する `star` も許し、有限個の反復回数や出力語を列挙しない。
元捕捉の区切り自由性は捕捉値に対する条件であり、入力全体の文字集合は制限しない。

元順の actual preflight と初回の `P(W)` 検査の後、最初の固定ブロックを実入力から `B` として捕捉する。
別の unary probe 規則がその捕捉値で `T[B]` を評価する。
後半が失敗すれば、既に照合した最初のブロックも含めて一周全体を取り消し、元位置で零周成功する。
後半が未定義なら未定義のまま伝播する。成功時は実行用 unary 規則

```
Run(B) <- T[B]; (param_0; T[B])*
```

へ同じブロックを捕捉し直して入る。Seq actual が先頭 `P(W)` を消費済みなので、
この本体はその後半と後続の各周を正しい位置から実行する。
初回ブロックが失敗した場合には後半を評価しない。
probe と実行規則は同じ physical clock の sibling call であり、後半の helper 行は
元の source 本体と同じ一段前の実表を使う。停止性の oracle や追加 clock の余裕を仮定しない。

`CopyPeriodControl.physical/iteration` は元 tuple での `T[P(W)]` と新しい単語環境 `[B]` での `T[B]` を対応させる。
helper prefix の閉じた有限構文検査から実 recursive row の一致を導き、各制御文脈へ持ち上げる。
先頭ブロックが非空で、後半の実成功は suffix を返すことから、外側反復の成功は常に厳密に消費する。
nullable な内側反復の未定義を拒否・空成功へ置き換えない。
`ControlledPeriodTransfer.physical` は任意の caller 環境・元/変換後 actual・全 clock の実呼出し一致を示す。
raw 宣言/root、period scope、後半の helper scope、元 actual の捕捉効果、親条件と戻り値効果閉包を有限検査し、
client 実表の同時帰納へ接続する。元文字列言語、残余、有限失敗、定義性、全 clock 未定義性を保存する。

例の後半は `(+;block) / ~`。各周は `B+B` または `B~` を入力で選ぶ。
`source_and_target_all_trees n flags depth` は任意の親語長、任意の非空 Bool 選択列、任意の再帰深さでの
source/target 受理を証明する。子語を倍化して捕捉し、帰還後の親語を復帰させる。
source 5 規則 `[0,0,1,1,4]` は固定 Seq 10 規則 `[0,0,1,1,1,1,1,1,1,1]` となる。
消費する内側反復 `( +;block )*;~`、保持値の否定による周全体の rollback、
committed choice 後半の失敗、probe を省いた誤失敗も kernel で確認した。
独立 helper の実再帰が異なる長さの balanced word を消費した後にも元ブロックを再照合できる。
helper の clock 1 未定義/clock 2 成功と、後半 `eps*` の全 clock 未定義を保存する。

残る制約は、各周が同じ固定ブロックで始まること、後半の保持値利用がそのブロック全体であること、
後半の呼出しが独立 nullary helper であること。後半からの parameterized client 呼出しや
元 tuple の各成分の独立利用、先頭 anchor のない任意の反復はまだ扱えていない。
既存の unary client の先頭再照合・共通 arity/pattern/後半・元捕捉の区切り自由性も残る。
一般 Par/Seq 言語クラスの一致・分離は引き続き未解決である。

## 一周分の実入力を再捕捉し、消費反復の任意の停止位置を保存する

`RecapturedCopyBlock/Transfer` と `RecapturedCopySyntax/Correspondence/Compiler` は、
非空の固定 parameter index 列 `js` の消費反復

```
H(w_0,...,w_(n-1)) <- ((param_js[0];d); ...; (param_js[last];d))*
```

を EOF なしで固定 Seq 文法へ翻訳する。各元保持語は区切り `d` を含まず、空語でもよい。
引数個数・出現順・重複、実捕捉語の長さ、反復回数、停止後の入力と後続は一般である。
一周の消費語は実 tuple が決まれば `B=encode d W js` という一つの語に固定される。

まず元順の全 actual preflight を行い、元位置から従来の有限 pattern projections で最初の一周を照合する。
一周目が失敗すれば、元の `star` と同じく元位置で空成功する。一周目が成功すれば、
区切りだけを読む固定 skeleton scanner でその**一周分の実入力区間を丸ごと新しい一語として捕捉**し、
新しい unary Seq 規則 `Loop(B) <- (param_0)*` を呼ぶ。
Seq 引数が一周目を既に消費しているため、本体では残りの周回だけ照合する。
`B` は区切りを含み、元の個々の捕捉値より大きくてもよい。値を連結して作った架空の入力ではなく、
`evSeqArgs` が元文字列上で実際に捕捉した値である。

`source_run/star_literal` は元の一周とその反復が `B` の literal 照合と等しいことを証明し、
`skeleton_run` は元保持語の区切り自由性から scanner の実終点が同じ一周末尾になることを証明する。
`recapture_call` が scanner から得られる実 capture を `pre_eq` で `B` に同定し、
新しい Seq 呼出しと元反復の**任意の停止残余**を対応させる。非空 pattern は `B≠[]` を保証する。
独立した各投影の停止位置を比較する演算も、最大値を返す PEG primitive も必要ない。

`RecapturedCopyTransfer.physical` は元 actual と変換後 actual を任意 caller 環境で評価し、
全 clock の実呼出し一致を示す。先頭 pattern query が clock 0 で未定義なので、空入力や零周の場合も
元の user-call 境界を保ち、この backend に別の nullary 初期化 gate は不要である。
outer preflight が、actual 自体の失敗を零周成功と混同することを防ぐ。
全 raw 宣言/root、scope、元捕捉の alphabet 条件、親条件と実再帰の戻り値効果を有限検査し、
既存の client 実表対応と同時帰納して、任意の seq/choice/not/star 文脈と recursive actual を翻訳する。
元文字列言語、残余、有限失敗、定義性と全 clock 未定義性を保存する。

以前の停止位置反例 `ab#a#ab#b#` と `ab#a#x#a#` は、新しい実 Seq 文法で残余5文字・4文字を正しく返し、
それぞれの後続を消費して成功する。Seq が実捕捉する語は `ab#a#` である。
零周入力 `ab#b#` でも元位置を返す。先頭照合を省くと全消費へ誤り、outer preflight を省くと
actual 失敗を空成功へ誤る実反例を検証した。

親を持つ例は source 5 規則 `[0,0,1,1,4]` から Seq 9 規則 `[0,0,1,1,1,1,1,1,1]` となる。
`source_and_target_all_trees n count depth` は任意の親語長、任意の正の一階層ごとの反復回数、
任意の再帰深さを扱い、子語の倍化捕捉と帰還後の親語の復帰を証明する。
空親を持つ producer の実再帰、空 actual での区切り消費と途中停止、真の cycle の全入力・全 clock 未定義も確認した。

**一周ごとに消費語が変わる任意の PEG 反復は、まだ対象外である。**
この backend は固定された `param_i;d` の有限列を一周とする。独立 nullary helper、
親を先頭で再照合する unary client と共通 arity/pattern/d、元保持語の区切り自由性は残る。
任意の本体・消費 prefix・複数親・先頭再照合なし、および一般 Par/Seq 言語クラスの一致・分離は未解決である。

## 反復全体の成功判定だけでは停止位置を選べない

`FrontierStatusSelector` は、二つの実 unary projection を probe とする有限 selector を定義し、
実 `MExp` へコンパイルする。guard は probe 全体への先読み、空成功・失敗、連接、優先選択、否定、
零幅反復を任意に組み合わせられる。selector はこれらの guard で分岐し、最後に一方の projection を
消費するか、失敗・未定義となる。判定木の深さや query の反復回数に構文上の固定上限は置かない。
追加の再帰 selector 規則や、元入力の文字を直接調べる guard はこの構文の対象外である。

`guard_physical` と `render_physical` は、すべての probe が成功する入力では、
guard が返せる情報が成功/失敗/未定義のどれかだけで、個別の返す残余位置を区別しないことを示す。
nullable な guard 反復の未定義も保存し、単純な二値モデルへ落としていない。
有限の選択制御全体は `selected tree` という、入力に依存しない同じ最終選択へ帰着する。

`FrontierSelectorObstruction.no_status_selector` は、保持語 `a/ab` と周期 `[1,0]` の実 Seq projection
について、**すべてのこの形の有限 selector** が `ab#a#ab#b#` または `ab#a#x#a#` の
どちらかで、元 Par の残余位置を保存できないことを証明する。
両入力ですべての probe が成功するのに、最早停止の側が逆になるためである。
`positive_clock` は、実 probe の有限結果の単調性から selector の全ての正 clock の結果が一致することを示す。
`no_status_selector_any_clock` は、同じ反例入力で**全 clock** が元の正しい残余を返せないことを導く。
`no_status_selector_observation` は、実 first-order Seq grammar と root の有限導出による
残余観測そのものが存在しないことまで接続する。評価 clock を増やす回避には依存していない。

これは、固定 projection 一つの不適切さから、成功判定を組み合わせる有限制御全体へ広げた
**特定の翻訳方法の限界**である。任意の Seq grammar を排除する定理ではなく、
元文字列言語クラスの分離でもない。入力内容に依存する新しい検査、停止残余を比較する構成、
別の捕捉表現、追加の再帰規則を使う翻訳は排除していない。
一般の最大残余を選ぶ Seq 文法と、Par/Seq のクラス一致・分離は引き続き未解決である。

## 末尾確認なしの反復：停止位置の一般式と残る文法操作

`SynchronizedStarFrontier.star_maximum` は、同期する有限個の検査の conjunction と、
それぞれを独立に反復したときの停止位置の関係を示す。
各検査は有限に成功または失敗し、成功すれば厳密に入力を消費する。
同時検査は、すべての検査が同じ終点で成功したとき、その終点で成功し、
一つでも失敗すれば失敗する。この一周の条件だけから、非有界の実 `evStar` について

```
evStar simultaneous p = maximum (component evaluators' evStar results at p)
```

を導く。位置は残り文字数なので、`maximum` は**最も早く止まった位置**に対応する。
反復回数、残余文字列の内容、停止する component は固定しない。
`maximum` は実評価結果を受け取る Lean の計算であり、PEG の新しい primitive でも、
Seq 文法の閉包性として仮定した操作でもない。

`RepeatedWordFrontier.source_failure_iff/step_success/step_failure` は、
元の全捕捉語と各 unary view の一周の実結果を対応させる。
区切り自由性と delimiter 境界の一意性から条件を証明するため、上の同期条件を
別名の仮定として残していない。`physical` は任意の非空 parameter pattern・正の引数個数・
区切り自由な実保持語・任意の元入力と開始位置に対して、実 bare `star` の返り値を計算する。
元側と view 側の grammar・strategy・有限評価表は別々でもよい。
`followed_by` は任意の後続を元の保持環境のまま、その停止位置で実行する評価式を示す。
EOF、末尾 marker、有限 suffix 辞書、反復の展開上限は要求しない。

`RepeatedFrontierTransfer.positive_iterations` は、元の引数が実際にすべて成功し、
一周目も成功する場合に、**実 Par 規則呼出し**の残余位置が、各 actual を
自分の終点から実行した **実 unary Seq 呼出し**の返す残余位置の最大値になることを証明する。
caller の親環境を保ち、元 actual と変換後 actual の局所対応と捕捉の区切り自由性を明示する。
Seq 呼出しの本体は、初回の `afterParts` に続いて通常の view 周期を bare `star` で反復する。
`zero_iterations` は一周目の失敗時に元位置を返す別の場合を導く。
初回の調整自体が失敗する view があるため、この零周の場合を成功時の最大値計算へ混ぜられない。

実例は保持語 `a` と `ab`、周期 `[1,0]` である。
`ab#a#ab#b#` では元の反復は残余5文字で止まり、短語の実 Seq 呼出しも5文字、長語の呼出しは0文字を返す。
`ab#a#x#a#` では元は残余4文字、短語の呼出しは0文字、長語の呼出しは4文字を返す。
`no_fixed_projection` は固定したどちらか一方を全入力で使う方法を否定する。
両例の実捕捉値、正しい残余で成功する元の後続、誤った投影で消失する後続、
零周の場合、先行 actual 失敗、clock 0 未定義を kernel で確認した。

**この投影選択法では、停止位置を返す Seq 文法は構成できていない。** 固定周期では、上記の一周分再捕捉がこの不足を解消した。
この投影法を完成するには、各呼出しの残余位置を実際の入力上で比較・選択する手段が必要である。
今回の `maximum` を文法操作として使う翻訳は提示していない。
以下の完成済み文法翻訳は引き続き EOF 付きの範囲であり、一般 Par/Seq の一致・分離も未解決である。

## 入力末尾までの消費反復を、固定個数の unary 検査へ

`RepeatedWordPattern` と `DelimitedRepeatEvaluation/RepeatedWordEvaluation/RepeatedWordTransfer` は、
非空の有限 index 列 `js` を用いたコピー規則の本体

```
((param_js[0];d); ...; (param_js[last];d))*; !any
```

を、固定個数の unary Seq 検査へ翻訳する。引数個数、出現順、重複、捕捉語の長さ、
反復回数はいずれも一般である。捕捉語は区切り `d` を含まず、空語でもよい。
従来の `ControlledCopy` の構文上零幅の反復とは異なり、ここでは各周回が区切りを含む実入力を消費する。
反復回数を展開した文法や捕捉語の有限辞書は生成しない。

検査 `i` は実際に捕捉した一語 `w_i` を保持し、`js` の各位置で、index が `i` なら
`w_i;d`、それ以外なら「区切りまでの任意語;d」を読む。この有限の周期をそのまま反復する。
Seq 引数が既に消費した先頭部分は初回だけ `afterParts` で調整し、二周目以後は周期全体を検査する。
各検査が入力末尾で成功すれば、実入力の区切り数は必ず `反復回数 * js.length` になる。
`iteration_unique` が、別々に計算された検査の周回数の一致を導き、`source_iff_after` が
元の全保持語 tuple による全体照合へ戻す。`js` の非空性はこの同期と各周回の厳密な消費に必要である。

`DelimitedRepeatEvaluation.physical` は任意の進行する template の実 `evStar` を有限周回の照合へ接続する。
これは反復回数の oracle を仮定する定理ではなく、実際の評価の trace と停止条件を使う証明である。
`RepeatedWordTransfer.physical` は、実際の元引数と変換後引数を同じ caller 環境・同じ clock で評価し、
新しく捕捉した実文字列と各 Seq 引数の異なる終点から、コピー呼出し全体の実評価一致を導く。
元順の preflight の後に nullary 初期化 gate を呼び、空入力も clock 0 の未定義を保存する。
空入力の分岐は元位置で判断し、引数を評価した後の位置が空であるだけでは成功させない。

`RepeatedCopySyntax/Correspondence/Compiler` は、この本体を既存の parent/client の制御構文へ統合する。
helper は独立 nullary prefix、client は親語を先頭で再照合する unary source 規則であり、
コピー actual は親を正に消費し、parameterized recursive producer を呼べる。
client ごとの親 alphabet 条件・戻り値効果の再帰閉包・全 actual の捕捉効果、全 raw 宣言と root、
非空 pattern と全 index の範囲を有限検査する。
client 実表の同時帰納で、任意の root 文脈・実再帰・actual 内の変換も同じ physical clock に接続し、
元文字列言語・残余・有限失敗・定義性・全 clock 未定義性を保存する。

例は source 5 規則 `[0,0,1,1,4]` から、Seq 9 規則 `[0,0,1,1,0,1,1,1,1]` への固定翻訳である。
実捕捉は `[a^(2n)b c^(2n), a^n, a^(2n), a^(2n)b]`、周期は `[0,2,1,0,3,2,1]`。
`source_and_target_all_repetitions` は任意の `n` と任意の正の周回数で両文法の受理を証明する。
さらに空の親を持つ producer が実際に再帰して `aaaa` を捕捉し、三周消費する両文法の kernel 実行を確認した。
全 actual が空でも `#` を 0/7/21 個消費できる。後続余剰文字、範囲外 index、空 pattern は拒否される。
真の actual/client cycle は全入力・全 clock で未定義となり、preflight を除くと空入力で誤成功する。
初期化省略の clock 0 誤成功と、初期化より先の actual 失敗も確認した。

**この独立投影法では末尾確認が必要である。** 上記の再捕捉法はこの制限を外す。 `js=[1,0]`、保持語 `a` と `ab`、
実入力 `ab#a#ab#b#` では、末尾確認を外した二つの unary loop はそれぞれ一周・二周で止まり、
残余が 5 文字と 0 文字になる。この kernel 反例は、停止位置を任意の後続へ返す翻訳には別の同期が
必要なことを示す。これは特定の投影法の制限であり、言語クラス分離ではない。
一般の消費反復と後続・任意の本体・複数親・先頭再照合なしの client・無制限の Par/Seq 一致または分離は未解決。

## 保持語を読み進めた後の選択・否定を含むコピー本体

`CopyBodyControl/Evaluation/Projections/Emission` と
`ControlledCopySyntax/Correspondence/Compiler` は、従来の平坦な parameter 列から、
`param_i;d` を原子とする有限本体へ拡張する。空成功・失敗・連接・優先選択・否定と、
構造上零幅の operand の反復を許す。元の捕捉 tuple は保ったまま、消費後の位置で別の
保持語を否定したり、選択したりできる。消費する反復と本体内の一般再帰は対象外である。

本体を有限の構文履歴へ正規化し、元のコピー呼出し位置から履歴の語列を検査する unary Seq
規則を生成する。有限なのは parameter index の履歴で、捕捉文字列の辞書ではない。
CPS の成功・失敗継続を分け、選択肢が成功した後の継続の失敗で別の選択肢へ戻らない性質を保存する。
全 actual を元の順に評価する preflight と nullary 初期化 gate を置き、空本体でも
clock 0 の未定義と、gate より先に起こる actual の失敗・未定義を保存する。

`ControlledCaptureEffects` は実 source grammar に対する条件付き alphabet 保存を一般化し、
親を正に消費する actual、parameterized recursive producer、子での新捕捉、帰還後の親語の復帰を
この本体翻訳と接続する。全 raw 宣言・root の一致、参照 scope、actual の捕捉効果、client ごとの親条件、
実 tail の戻り値効果の閉包を有限検査する。`ControlledCopyCompiler.physical` は全入力・全 clock の
実評価一致を示し、元文字列言語、残余、有限失敗、定義性、全 clock 未定義性を導く。

具体例は 5 規則 `[0,0,1,1,4]` から 97 規則（独立 helper 2、unary client 2、初期化 1、
unary projection 92）への固定翻訳である。実捕捉 tuple は
`[a^(2n)b c^(2n), a^n, a^(2n), a^(2n)b]`。
先頭の語を消費後、否定・選択が異なる経路を通る入力を両方の実評価で確認した。
任意の `n` と再帰深さについて、子が親語を倍にして捕捉し、帰還後に親の語を復帰させる
source/target の受理を証明した。

選択へ継続を誤って分配する書換えの反例、空本体で初期化 gate を除く clock 0 の誤成功、
preflight を除くと未定義 actual を飛ばす反例、初期化前の actual 失敗を検証した。
零幅反復は保持値との照合結果によって空成功または全 clock 未定義になる。
範囲外 parameter・消費する反復・元宣言不一致を checker が拒否する。

この拡張でも、独立 nullary helper、先頭で親語を再照合する unary client、共通の arity・区切り・本体、
区切りを含まない新捕捉語という制約は残る。一般の複数親、任意 PEG 本体、消費する反復、
先頭再照合なしの client、無制限の Par/Seq クラス一致・分離は未解決である。
以下の平坦な本体に関する記述は、この拡張前の frontend の範囲を記録している。

## 親を正に消費する actual と、実再帰 producer の消費効果

`RetainedCaptureEffects` と `ConsumingPatternChecks/Correspondence/Compiler` は、コピー actual の
正の消費経路へ `parent` と parameterized client 呼出しを許す。
client ごとの「親語が alphabet 内である必要がある」有限 Bool 列を検査し、その client への全呼出しで
実引数の捕捉語が条件を満たすことを構文から確認する。
root は親を持たず、その client に入る初回捕捉も検査する。親を必要としない client は任意の親語を保持できる。
この Bool 列は実行時の文字列・終点・停止性を教える oracle ではなく、元の全呼出しと照合される有限条件である。

戻り値効果は、**新しい引数語が alphabet 内なら、先頭再照合と tail が消費する語も alphabet 内**という条件付きの性質である。
client tail から候補 Bool 列を計算し、有効な候補すべての閉包を有限検査する。
`RetainedCaptureEffects.evaluator_safe` と `physical_rows` は、実際の source 行を clock で帰納し、この性質を導出する。
`captured_alpha` が実捕捉語の alphabet 条件を与えるため、実引数内の client 呼出しも正の producer として使える。
コピー規則の本体は区切りを消費するので、この戻り値効果を持つとは判定せず、正の actual に入れると拒否する。
成功時の消費だけを述べ、停止・成功・非空出力を要求しない。

`ConsumingPatternCorrespondence.Rows` は client の親条件を伴う実表対応で、条件が必要な呼出しの実捕捉からその条件を証明する。
新しい検査から全元入力の同 clock 観測・言語・残余・有限失敗・有限実行存在・全 clock 未定義を保存する。
既存の元/生成 grammar 構成を再利用し、親の実語や新捕捉を有限 view へ縮めない。
独立 nullary helper 群、unary client の先頭再照合、任意 arity の共有 param+d コピー本体は引き続き使う。
入力自体を alphabet 内へ制限したり、最大 scanner frontier や語長上限を要求したりはしない。

主例は親 `w=a^n` に対して、正の actual 列
`[balanced, parent, producer(parent), short]` が実際に
`[a^(2n)b c^(2n), a^n, a^(2n), a^(2n)b]` を捕捉する。
producer の source 本体は `z; ((z; !"a") / ("a"; producer(z)))` という実再帰で、生成側は先頭 z を除いた本体。
n の例では2番目の z が残る親語を消費して `ww` を返し、空引数なら任意長の a-run を再帰で返す。
計算した戻り値効果は `[false,true]`、親条件は `[true,false]`。
source arity `[0,0,1,1,4]` から固定 Seq `[0,0,1,1,1,1,1,1]` を生成する。

`ConsumingPatternProofs.actual_captures` は任意 n・任意後続についてこの実 actual 捕捉列を導出する。
`source_and_target_all_trees` は任意親長・任意再帰深さで子の実捕捉 `w→ww` と帰還後の親復帰を含む双方受理を証明する。
`four_unbounded` は任意の固定上限を4つの捕捉長が同時に超えることを示す。
`recursive_producer_source/capture/target` は空引数から返る任意長 a^m の実再帰消費・実捕捉を証明する。
直接 kernel 実行では親の正消費・producer の返却語・深さ0/1/2・空親・短子/子値漏出の拒否を確認した。
旧 query-only 検査はこの実宣言を拒否する。親条件の削除、不正な初回 `a#` 捕捉、区切りを消費する client の positive actual 化を拒否し、
条件を要求しない producer を通常呼出しする場合には `a#` 親を許すことも確認した。

戻り値効果 true の停止不能 client を正の actual に置いても検査は受理し、元・生成側は全入力・全 clock で未定義のまま対応する。
全実引数の元順 preflight を省くと、先のコピー不一致で有限失敗へ変わる反例も検証した。
複数の親保持語、先頭再照合なしの任意 client、区切り付き parameter 列以外の任意複数値本体、
および Par/Seq 言語クラス全体の一致・分離は引き続き未解決である。

## 一つの実保持語に依存する実引数と、子の捕捉後の親復帰

`ParentPatternTransfer` と `RetainedPatternSyntax/Correspondence/Compiler` は、一つの親保持語を
**長さ無制限の実文字列のまま**持つ再帰 client と、任意 arity の区切り付きコピー規則を統合する。
source client の実本体は `param_0;tail`、生成 unary Seq client の本体は変換した `tail`。
client の呼出し引数では親の語を消費・連接・再捕捉でき、子から戻った継続では元の親の語を再照合できる。
コピー actual は closed でなくてもよく、親の語や unary client 呼出しを先読みで調べ、実際に捕捉する語を選べる。

`ParentPatternTransfer.captured_free` は任意の caller 保持環境で capture alphabet の有限検査を正当化し、
`physical` は source/target で異なる actual 式列をその**同じ親環境**のまま評価する。
生成 unary copy 規則の実環境は新しい捕捉語へ切り替わるが、actual 評価時の親環境と混同しない。
`RetainedPatternCorrespondence.Rows` は、元の共通原点から親語を再照合した位置と Seq 引数終点を対応させる。
実際の source/target 表を physical clock で一斉に帰納し、再帰 actual・子の新捕捉・親の継続を接続する。
独立 nullary helpers の表対応も実際の両文法から導く。
元の全宣言・開始式、helper/client 参照、親 parameter の scope、コピー arity/添字、capture alphabet を有限検査し、
全元文字列の観測・受理言語・残余・有限失敗・有限実行存在・全 clock 未定義を同じ clock で保存する。

`RetainedPatternExamples` の source arity `[0,0,1,1,4]` は固定 Seq `[0,0,1,1,1,1,1,1]` へ。
実際の親が `a` か `aaa` かによって、同じ現在入力から第2 actual が `ab` か `abc` を捕捉する。
この判定は actual 内で、親の語を引数にする実 unary client 呼出しを先読みする。
親に `#` を含む語 `a#` を保持したままコピー規則を動かす例も双方で成功し、親の値を alphabet 内へ制限しない。
copy の捕捉語にだけ、区切りを含まない条件を課す。

主再帰例は親 `w=a^n` を保持して4つの新語 `[a^n b c^n,a^n b,a^n,ε]` をコピー照合し、
子の実引数 `param_0;param_0` で `ww` を新しく捕捉する。帰還後は `":";param_0` で元の親 `w` を使う。
`RetainedPatternProofs.actual_captures` は任意 n と任意後続について、親を実 literal として代入した実 actual の捕捉列を導出する。
`source_and_target_all_trees` は任意 n・任意再帰深さについて元/生成双方の受理を証明する。
実語が `w→ww→wwww` と伸びても、各継続では自分の親の値へ戻る。
直接 kernel 実行では深さ0/1/2、長さ1/2、空親、短い子捕捉の拒否、子値が漏れた場合の余分な照合語の拒否を確認した。
親依存コピー actual の真の循環と、空親を再照合する nullable star は全入力・全 clock で未定義である。
親環境での preflight 省略の有限失敗反例、root の未束縛 parent・範囲外 user・不正元宣言の拒否も検証した。

残る条件は、独立した nullary helper 群、先頭で自分の新捕捉を再照合する unary clients、
一つの選択した arity/区切り/添字列を共有する param+d 列のコピー本体である。
旧 RetainedPattern のコピー actual の正の消費経路では親語や unary client を許さず、
先読み・その結果による producer 選択を扱う。上記 ConsumingPattern は有限検査で親の条件と戻り値効果を接続してこの制限を緩める。client の通常の本体・呼出し引数では親語を直接消費できる。
複数の親保持語を任意本体へ同時に渡す一般変換、先頭再照合なしの任意 client、任意の複数保持値本体と、
Par/Seq 言語クラス全体の一致・分離は引き続き未解決である。

## 任意 arity のコピー本体と、実引数を通る相互再帰の統合

`DelimitedPatternCallTransfer` と `RecursivePatternSyntax/Correspondence/Compiler` は、任意 arity の
区切り付き本体を、コピー規則へ戻る nullary client の相互再帰と統合する。
元の client 本体と開始式のコピー呼出しをすべて Seq 用へ変換し、その任意個の actual も再帰的に変換する。
actual の先読みへコピー式を直接入れることも、client → コピー規則 → actual 内の client → コピー規則
という循環も扱う。独立 helper library、凍結した共通表、停止性の仮定は使わない。
コピー本体の添字列は任意の非空列で、同じ保持語の任意順・任意回数の再照合、未使用引数、空捕捉を許す。

`DelimitedPatternCallTransfer.physical` は source と target で**異なる actual 式列**を対応させる。
各 actual の対応から実捕捉列と評価順序を接続し、任意個の unary projection の同一 clock 対応へ持ち上げる。
`RecursivePatternCorrespondence.expression_physical/arguments_physical` は入れ子の式列を相互に帰納し、
`tables_related` が全 client の実際の source/target 行を一斉に physical clock で閉じる。
seq/優先選択/not/star の任意文脈、全元入力・全残余の成功、有限失敗、実行存在、全 clock 未定義を保存する。
元の全宣言・開始式、全 client 参照、各コピーの arity、添字範囲と source actual の区切り除外を有限検査する。
入力を alphabet 内へ制限する条件や、有限候補語辞書はない。

`RecursivePatternExamples` の source arity `[0,0,0,0,0,0,0,4]` は固定 Seq
`[0,0,0,0,0,0,0,1,1,1,1]` へ。
実捕捉は `[a^n b c^n,a^n b,a^n,ε]`、コピー本体の添字列は `[0,2,1,0,3,2,1]`。
4つの actual は現在の7区間を先読みで飛ばし、後続ブロックを同じコピー client へ問い合わせてから捕捉する。
後続が不正なら現在の actual も失敗し、旧独立 library 検査はこの実宣言を拒否する。
`RecursivePatternStreamProofs.source_block_and_actuals` は任意 n・任意の後続ブロック長リストについて、
実 Par 捕捉列と現在ブロック後の残余を導出する。
`source_and_target_all_streams` は任意長・任意個のブロック列の双方受理を証明する。
3つの消費する捕捉長は、既存の `DelimitedPatternCaptureProofs.three_unbounded` の語列そのものである。

直接 kernel 実行でも異なるブロック長、空捕捉、後続不正検出、残余、actual 内の直接コピーを検証した。
同位置へ戻る本物の copy/actual 循環と後の actual の循環は全入力・全 clock で未定義のまま対応する。
元順の preflight を省くと先のコピー不一致で有限失敗へ変わる反例、誤 arity・範囲外参照・区切り捕捉・不正元宣言の拒否も確認した。

残る構文条件は nullary clients、closed actuals、一つの選択した arity/区切り/添字列を共有するコピー規則、
区切りを含まない実捕捉、parameter と区切りを並べたコピー本体である。
同じ区切りを消費する内側コピーの正の出力を外側 actual として捕捉することはこの検査では許さず、
先読み内部のコピー照合を扱う。親依存 actual は上記 RetainedPattern が一つの実保持語について扱う。任意の複数保持値本体と、
Par/Seq 言語クラス全体の一致・分離は引き続き未解決である。

## 任意個の保持語を任意順・任意回数で使う区切り付き本体

`DelimitedWordPattern/DelimitedPatternPasses/Evaluation/Compiler` は、固定の二語本体
`v#u#v#` を、任意の正 arity と任意の非空 parameter 添字列へ一般化する。
元の本体は添字列 `[j₀,…,jₘ]` から生成する
`param_j₀;d;…;param_jₘ;d`。同じ保持語の出現回数・順序、使わない引数、空の実捕捉も扱う。
arity・出現回数・捕捉長に固定上限はない。Seq 側は保持語ごとに unary 規則を一つ生成し、
最後の検査以外を元の原点からの先読みとする。先に全実引数を元の順で preflight する。

各実捕捉が区切りを含まないため、成功時はどの捕捉終点も最初の区切りより手前にある。
自分の語を先頭で再照合する検査は、実引数が既に消費したその語の直後から区切りを照合する。
それ以外は終点から最初の区切りまで進み、後の区間で自分の語だけを再照合する。
`source_iff_views` と `source_iff_after` は任意個のこの検査の同時成立を証明する。
`matches_endpoint_unique` は別々の検査が異なる区切り境界・異なる最終残余を選べないことを示す。
`DelimitedPatternPasses.run_eq` は成功だけでなく有限失敗も含む元の suffix 変換との等式である。

`DelimitedPatternEvaluation.physical` は実際の source Par 呼出しと生成 Seq 呼出しを同 physical clock で対応させる。
引数が先に失敗・未定義になる場合と、引数成功後の header 行が clock 0 で未確定な場合も含む。
`DelimitedPatternCompiler` は元の全宣言・開始式、非空 arity/本体、参照範囲、closed lexical actual と
実捕捉 alphabet の区切り除外を有限検査する。入力の符号化、停止性の仮定、語長上限、最大 scanner frontier は使わない。
全元文字列の受理言語、任意残余の成功、有限失敗、実行存在、全 clock 未定義を保存する。

`DelimitedPatternExamples` の source arity `[0,0,4]` は固定 Seq `[0,0,1,1,1,1]` へ。
実捕捉列は `[a^n b c^n, a^n b, a^n, ε]`、本体の添字列は `[0,2,1,0,3,2,1]` である。
`DelimitedPatternCaptureProofs.actual_captures` は任意 n・任意後続についてこの実 Par 捕捉列を導出する。
`all_lengths` は任意 n の双方受理、`three_unbounded` は任意の固定上限を三つの捕捉長が同時に超えることを証明する。
n=0/1/2/4 の直接 kernel 実行、コピー違いの拒否、残余 `!X` の保存、別のコピー順序、
後の実引数の循環が全入力・全 clock で未定義であることと、preflight を省くと有限失敗になる反例も検証した。
空 arity/本体、範囲外添字、区切りを捕捉する actual、不正な元宣言を拒否する。

この任意 arity frontend の actual library は**独立した nullary 規則群**であり、元 root はコピー規則への一呼出しである。
この独立 library 版の上に、上記 RecursivePattern が任意 arity と相互再帰・式文脈を統合する。
区切り付き parameter 列以外の任意本体、親の保持 parameter に依存する actual、区切りを含む捕捉の一般処理と、
Par/Seq 言語クラス全体の一致・分離は未解決である。

## コピー検査へ戻る相互再帰と、実引数内部のコピー呼出し

`DelimitedCopyCallTransfer` と `RecursiveCopySyntax/Correspondence/Compiler` は、下記の区切り付き
二語コピー変換から、**nullary library の独立性条件を外す**。元の client 本体も Seq 用へ変換し、
client → コピー規則 → 実引数内の client → コピー規則という相互再帰を許す。
閉じた実引数の先読みへコピー呼出しを直接入れることもできる。
実際の元・生成表の client 行を一斉に physical clock で帰納し、停止性や固定された helper 表を仮定せず、
全入力・全残余の成功、有限失敗、実行存在、全 clock 未定義と元文字列言語を保存する。
元の全宣言・開始式の AST 一致、参照範囲、各コピー実引数の消費 alphabet を有限検査する。

`RecursiveCopyExamples` は source arity `[0,0,0,0,0,2]` から固定 Seq
`[0,0,0,0,0,1,1]` を生成する。`u=a^n b`, `v=a^n b c^n` の捕捉前に、現在の
`v#u#v#` を先読みで飛ばし、その次のブロックへ同じコピー client を再帰呼出しする。
後続が不正なら現在の実引数も失敗するため、独立した実引数 library への変形では扱えない。
旧独立性検査がこの実宣言を拒否し、新検査が受理することも kernel で確認した。
`RecursiveCopyStreamProofs.source_block_and_actuals` は任意の n と任意の後続ブロック長リストについて、
実捕捉列 `[u,v]` と現在ブロック消費後の残余を導出する。
`source_and_target_all_streams` は任意個・任意長のこのブロック列の双方での受理を証明する。
長さやブロック数に固定上限は置かない。

成功する前進再帰に加え、同じ位置へ戻るコピー client/actual の循環は任意入力・全 clock で未定義のまま対応する。
後の実引数が循環する場合も、元の実引数順の preflight を省くと有限失敗へ変わる反例を検証した。
実引数内コピーの直接実行、後続不正ブロックの拒否、不正参照・実宣言の拒否も確認した。

残る条件は nullary clients、closed actuals、区切りを消費しない実捕捉、固定の二保持値本体
`param_1;d;param_0;d;param_1;d` である。先読み内部は区切りを読めるが、
区切りを含む内側コピーの正の出力を、同じ区切りを使う外側コピーの実捕捉にはできない。
親の保持 parameter に依存する actual、任意の二保持値本体、および一般の Par/Seq 一致・分離は未解決である。

## 二つの無制限捕捉を原点からの独立検査へ分ける

`DelimitedCopyProjection/DelimiterTemplate/DelimitedCopyTemplates/CaptureDelimiterSafety/DelimitedCopySyntax/Evaluation/Compiler`は、
二つの元のPar実捕捉`u`/`v`を有限viewに縮めず、コピー検査を別々のSeq呼出しへ分ける。
元の二引数規則の実本体は`param_1;d;param_0;d;param_1;d`という形、すなわち
入力の`v d u d v d`部分を消費する。双方の参照は無guardで、捕捉長の上限や候補語辞書は使わない。
二つのactualは独立したnullary再帰PEG libraryを呼ぶ任意のclosed式で、元の成功終端をscanner frontierへ
合わせたり、長いactualを短いactualと差分parserへ構文分解したりする条件はない。

Seq側は二つのunary規則を作る。第1の呼出しは実語`u`を捕捉し、残る最初の区間を区切りまで読み飛ばして
`u`のコピーを検査し、その後の区間も区切りまで読む。第2の呼出しは元の入力位置から実語`v`を捕捉し、
中間区間を読み飛ばして`v`のコピーを検査する。第1検査は先読みなので、両方とも元の入力位置でactualを評価する。
実actualの左から右の先読みを先行させ、後のactualが未定義のときに第1コピー検査の有限失敗で短絡しない。
各検査は一つの無制限実語だけを保持し、同時に二つの重なった語をSeqへ渡す差分parserは作らない。

境界を一意にするため、**実捕捉語に区切り`d`を含めない**条件を有限検査する。
`MaskedScannerAbsorption`の候補mask生成と閉包検査を再利用し、actualの消費経路が`d`を含まない有限alphabet内であることを確認する。
これは最大run終端の条件ではない。負の先読み内部は消費経路へ含めず、未定義の再帰helperも停止仮定なしで扱う。
libraryの全宣言はnullaryで参照範囲を有限検査し、コピー規則へcallbackしない。
元の全宣言と開始式も有限AST一致で確認する。入力全体をそのalphabetへ制限したり、入力を符号化したりしない。

`block_run_eq`は、両actualの物理的な共通原点とdelimiter freedomから、実際の後続suffix変換そのものの一致を証明する。
第1・第2検査が異なるコピー境界を選ばないことも、区切りの一意性から導く。
実Par/Seq表は同physical clockで対応し、clock0の未確定行も保存する。
`DelimitedCopyCompiler.Term`はコピー区間・通常helper・文字・seq/alt/not/starの任意の組合せを許し、
その全入力・全残余・有限失敗・有限実行存在・全clock未定義と、元文字列受理言語を保存する。
語の意味、停止性、差分parserの存在をコンパイラへの仮定として渡さない。

主例は`A=a* b`、`B ← a B c / b`の二つの独立parserで、元arity`[0,0,0,0,2]`から
固定Seq `[0,0,0,0,1,1]`へ。実捕捉は`u=a^n b`と`v=a^n b c^n`で、
任意n・任意後続suffixについてその`DerivesArgsPar`を証明した。
任意の固定上限を両方の実捕捉長が超えることと、任意nの`v#u#v#`を元・生成双方が受理することも証明した。
n=0/1/2/4の双方clock12直接実行、二種類のコピー違いと初回balance違いの拒否、
残余`!X`の保存、異なる長さのblockをstarで反復する例、選択・否定・後続literalの文脈をkernel検証した。
`A`の実終端はalphabet最大runの途中にあり、従来のfrontier条件を満たさない。
後のactualの循環は全入力・全clock未定義、逆順の有限失敗も保存する。
先読みpreflight省略で未定義が有限失敗になる反例、区切りを捕捉した場合の誤変換と検査拒否、
不正な実本体の拒否、pure actualのclock0/1対応も検証した。

`FiniteResidualControl.no_finite_summary`は、残り入力が`c^m`だけで、opaqueな`a^n b`と
prefixだけから選んだ有限状態を渡すインターフェースの不可能性である。
今回のコピー言語は後で元の語が再出現し、上記の検査は入力原点からparserを実行する。
その不可能性定理を破ったとも、今回の言語がSeqを分離するとも主張しない。
旧独立library版に対して、上記 RecursiveCopy は nullary callback を扱う。一般の独立actualの差分生成、
任意の二保持値本体・parameter依存actualへの一般化と、
Par/Seq言語クラス全体の一致・分離は引き続き未解決である。

## 一つの無制限保持語と他の有限viewを同時に運ぶ全体変換

`SubstringCaptureView`と`RetainedViewFusionSyntax/Declarations/Atoms/Dispatch/Evaluation/Correspondence/Compiler`は、
有限viewへの値消去だけでなく、**長さに上限のない最初の保持語を実文字列としてSeq側へ運ぶ**。
この語の直接再照合`param_0`には有限suffix guardを要求しない。実引数内の再照合・否定・反復、
parameterized user呼出しにも使え、子が新しい語を捕捉しても親の語は復帰後に残る。
他の保持語は引き続き有限suffix領域でのみ参照し、有限viewへ消去する。

入力は有限のseed語列、arityと残余本体からなる規則列、開始式である。
seedのsuffix閉包を`R`、そのprefix集合（seedの全連続部分語）を観測辞書とする。
元の正arity規則は実宣言が`param_0;残余本体`であることを要求する。
nullary規則は`eps;残余本体`で、混在・相互再帰を許す。
残余本体・実引数はseq/alt/not/star/文字/range/any/literal、無guardの最初の保持語参照、
`guard(R);param_i`、任意arity user呼出しからなる。実引数は親依存・actual内userを含め任意で、
最初の捕捉が最長、scanner frontier、共通producer、捕捉長やアルファベットの上限は要求しない。
この規則頭の形は一般Par文法の正規形だとは主張しない。

通常結果と候補語DFA出力を同時に生成し、各実引数のviewを元の順序で観測する。
観測後も最初のactualは実parserとして残し、実捕捉語を単一引数へ渡す。
途中のPar文法はすべて`param_0;生成残余本体`というunary規則で、
既存`ReplayFusion`を合成して、Seq側のactual消費と元の先頭再照合を合わせる。
最終Seqも固定unary文法で、元のparameterized表や入力符号化は使わない。
原開始式は空環境の特殊化を通常のliteral代入で閉じ、規則追加やclockの追加をしない。
実Par/生成Seqの同physical clock対応、全残余・有限失敗・有限実行存在・全clock未定義と
同じ元文字列言語を、全宣言・開始式の有限AST検査から保存する。

`SubstringCaptureView.advance_observe`は、任意の実保持語を候補DFAの任意状態から読んだ結果を
部分語viewだけで復元する。候補外の語はsinkへ着くが、**実payloadは消さない**。
prefixだけの観測では候補`ab`に対する`b`/`c`を同じOtherにしてしまい、
中間状態1からは`b`だけが受理状態2へ進む。この実反例と生成フィルタの直接実行で部分語閉包の必要性を確認した。

主例の元arityは`[2,0,1]`、生成Seqは固定182規則・全arity1。
親の`a^n`から、actual内のunary userを通して`a^(n+1)`を新捕捉し、
別の同原点actualはnullary userの後で`a`を捕捉する。親子はともにOther viewでも実payloadが異なる。
`(n,深さ)=(1,0),(2,1),(4,2)`を元・生成ともclock8でkernel直接実行し、
親`aa`→子`aaa`の実捕捉、復帰後の親コピー、子payload漏出・空payload置換の誤りも検証した。
有限`R`の外で長さ2/4/7の実保持語を消費する例が通る。
最初の捕捉が長さ1、別の捕捉が長さ2/4という元・生成双方の受理も確認し、最長条件は使っていない。
任意n・任意clockで、同原点の実捕捉`[a^(n+1),a]`を証明した。
無guardの空payload反復は全入力・全clock未定義を保存し、先頭再照合を欠く実宣言は有限検査が拒否する。

一般の逆包含・分離は引き続き未解決である。
このbackendで残る制限は、正arity規則の先頭再照合と、最初以外の保持語の有限suffix参照である。
任意位置で複数の独立した無制限保持語を再照合する一般のPar文法はまだ変換できていない。

## 親依存actualの出力観測を含む有限suffix文法の全体変換

`FiniteSuffixObservedSyntax/Declarations/Atoms/Dispatch/Evaluation/Correspondence/Compiler`は、
保持値の直接参照が`guard(R);param_k`である一般の一階Par文法を、固定の全nullary Seq文法へ変換する。
userの個数・arityは任意で混在でき、規則本体と実引数はともに任意のseq/alt/not/star、
文字・範囲・any・literal、同じguard付き保持値参照、相互再帰user呼出しで組み立てる。
**実引数の独立helper条件を外し、親依存actualとactual内のparameterized user呼出しを含めた。**
元のparameterized callee表は生成文法に残さない。
入力の符号化、入力・捕捉長やアルファベットの制限、scanner frontier、停止性仮定は使わない。

各規則のarityに応じた候補語／その他viewと、通常結果または候補語ごとのDFA状態対をキーとして
固定nullary規則を列挙する。候補語ごとのstrict exact-word機械は、候補を読み終えた後の余分な文字を
sinkへ送る。各実引数について、まず元の通常結果を先読みし、その実捕捉語の等値queryから新しい
viewを選んでから次の実引数へ進む。選んだ継続が失敗・未定義でも別のviewへ落ちない。
すべての生成callは引数なしで、bodyは元のPar呼出し位置から始まる。
親のviewは継続に構文的に残るので、子から戻っても失われない。

通常行と全DFA出力行を同時に帰納し、**実際のPar/Seq表を同じphysical clockで対応**させる。
前のhelper固定backendと異なり、helperの安定化を待つ段数変換は不要。
seqは全DFA中間状態（sinkを含む）を扱い、選択は元の優先順位を維持し、starは既存の
`GeneralStarFilter`へ接続する。`any`/rangeの出力行は次の実文字による機械遷移を生成し、
候補語にない文字も扱う。有限アルファベットの列挙や全Unicode文字の展開はしない。
実引数の失敗・未定義の順序、不正arity/範囲外callで実引数を評価しない動作も保存する。

`FiniteSuffixObservedCompiler.check`は元の全宣言と開始式を有限AST一致で確認する。
全入力・全残余・有限失敗・有限実行存在・全clock未定義と、同じ元文字列上の受理言語を保存する。
外部から実引数の意味、出力profile、文法変換の正しさを仮定として渡さない。

主例の元文法は5規則・arity `[2,2,1,1,0]`、生成Seqは固定1,230規則・全nullary。
親の`a`/`ab`を調べる実引数内でparameterized wrapperを呼び、wrapperが実再帰balanced parserから
新たに`ab`を捕捉する。子は逆順`ab`/`a`を保持し、親子相互再帰から戻ったouterは自身の`ab`を実消費する。
深さ0/1/2を元・生成とも同じclock8で直接kernel実行し、実依存引数の捕捉列、
子のview漏出の拒否、balanced捕捉n=1/2/4も確認した。
候補外`X`のany/star・range/star実引数の受理、親の空保持値を非空suffix `ab`上で反復する
依存actualの全clock未定義、actual内user循環の全入力全clock未定義、
引数の失敗と未定義の順序、不正callの評価省略、guard欠落の検査拒否も検証した。

このbackendは**有限の残りsuffix guardを引き続き要求する**。
その条件なしで任意の保持語を任意位置で再照合する全体変換、または一般の言語クラス分離は未解決。
以下の共有表による有限view同一視と独立helper版はこの全体変換の前段である。

## 親依存actualを含む有限view同一視

`FiniteSuffixDependentView`は、有限suffix guardを残した一般の式構文で、
実引数を任意の式列へ広げる。実引数内で親の保持値を参照し、さらにuserを呼び出してよい。
`specialize`は任意の実表`T`（通常の位置範囲不変条件のみ）について、
現在の親の保持値を有限viewのliteral/失敗へ代入しても評価結果が変わらないことを証明する。
Par実引数列の**実捕捉語列全体**と、Seq実引数列の実捕捉語列・終点も一致する。
呼出し先には元と同じ実捕捉語を渡し、同じ`T i W`を参照する。

したがって`environment_congr`は、同じviewを持つ任意の二つの親環境を同一視できる。
`physical_environment_congr`は実際の`tblV`の各clockへ、`rows_factor`は
この構文で書いた任意の相互再帰sourceの実user行へ接続する。
どちらも親依存actualやactual内callを独立helperへ制限していない。
直接例では、長い親`aabb`の否定再照合を含むactual内userが実語`a`を捕捉し、
外側userがその`a`を再照合する。親参照を特殊化した式も直接実行で同じ結果になる。
親`bbaa`とは全clock一致し、親を候補語`ab`へ変えると実引数の否定が失敗する。

**これはcallee表を共有する式とsource行の同一視であり、生成Seq文法の定理ではない。**
新たに捕捉した語のviewを、独立helper以外の実引数についても固定の生成規則で観測し、
共有したparameterized表への依存を消す部分は、上記`FiniteSuffixObserved`で接続した。
この補題単独はその全体変換とは区別する。下記の旧backendは独立helperに限られ、一般のPar/Seq一致・分離は未解決。

## 有限suffix再照合を持つ異なるarityのuser相互再帰

`FiniteSuffixRecursiveSyntax/Helpers/Selection/Evaluation/Correspondence/Compiler`は、
下記の単一callee backendを、任意個・異なるarityのuser規則の相互再帰へ拡張する。
各直接参照は引き続き`guard(R);param_k`で、実引数は独立したnullary再帰helperの呼出し列に限る。
本体ではseq/alt/not/star、独立helper呼出し、他のuserへの呼出しを自由に組み合わせる。
calleeごとのarityと有限viewの組合せから固定nullary規則を列挙し、実捕捉列を等値queryで選ぶ。
user呼出しの有限arity/参照検査に失敗した場合は、元の失敗式へ下げて実引数を評価しない。

helper prefixだけを実安定表で固定した後、user段数について全user行を同時帰納する。
行不変条件は、規則のarityに合う任意の実保持文字列列を、その正確な候補語／その他viewへ対応させる。
親のviewは継続へ構文的に残り、子の新しいviewで上書きされない。
元helperも生成product helperも実宣言から閉じ、helperの意味や停止性を外部の仮定として渡さない。
有限な全宣言・開始式の一致検査から、元文字列言語・全残余・有限失敗・有限実行の存在と
全physical clock未定義を保存する。helper固定後のuser段数対応であり、同physical clock対応ではない。

主例の元arityは`[0,0,0,0,0,0,0,0,2,2,1]`、生成Seqは固定844規則・全nullary。
非空の二語`a`/`ab`を親子で逆順に保持する相互再帰を、深さ0/1/2で元・生成双方直接実行した。
再照合は空でないsuffix `ab`上で行う。outerは子から戻った後に自身の保持値`ab`を実際に消費する。
子のviewが親へ漏れた場合と実引数を逆順に渡した場合は失敗することも直接実行した。
balanced `a^n b^n`の実捕捉をn=1/2/4で確認し、候補外の長い値を否定再照合で使う
元・生成双方の成功と、短い`ab`に変えた場合の失敗を確認した。
user循環は全入力・全clock未定義、空捕捉の反復は非空suffix `ab`上で全clock未定義。
未定義実引数の先行は全入力・全clock未定義を保存し、失敗実引数を先へ移すと有限失敗になる。
preflight省略の誤った有限失敗、guard欠落の検査拒否、不正arity/範囲外userが
未定義実引数を評価せず失敗する動作も検証した。

この拡張でuser本体の相互再帰という制限は外れたが、親依存actualおよびactual内のuser呼出しは未対応。
EOF backendはそれらを既に扱える一方、直接参照にEOFを要求する。
両方の長所を合わせる有限内容観測は上記`FiniteSuffixObserved`へ接続した。
任意位置での無guard再照合と、Par/Seq言語クラスの一般一致・分離は依然として未解決である。

## 有限suffix領域で実内容を保つ捕捉再照合

`FiniteSuffixCallCompiler`は、EOFだけでなく、残り入力が指定した有限集合`R`に入る位置で
保持値を再照合する文法をSeqへ変換する。元の直接参照は`guard(R);param_k`という形で、
`guard`は現在のsuffixが`R`の一語と**完全一致**する零幅検査である。
`suffixes alphabet bound`を使えば、残り長さの上限と有限アルファベットによる領域にもできる。
入力全体や、元の実捕捉値の長さを制限する条件ではない。

観測する候補は`R`の全prefixから自動生成する。保持値が候補語ならその語自体を、
それ以外なら`none`（その他）を保持する有限viewへ写す。
元の捕捉語が候補外でも入力から捨てたりcallを拒否したりしない。
`R`に入るsuffixへ一致する語は必ずそのprefixなので、その他の語はその位置で一致しない。
この性質により、選択・否定・star、任意の消費prefixと独立helper呼出しを含む本体で、
実値を候補リテラルまたは失敗へ置き換えられる。候補外の長い値を否定で検査して成功する動作も保存する。

`ExactWordCaptureMachine`は、候補語を読み終えた後の一文字をsinkへ送る有限機械を作る。
空語を含む全語について、受理終状態へ着くことと実捕捉語の完全一致を証明した。
機械の有限和と既存`RegularCaptureProduct`の実再帰parser出力フィルタを再利用し、
候補ごとの等値queryからviewを生成する。全遷移profileの巨大な列挙は不要。
元parserの先読みが失敗・未定義の順序を保存し、継続失敗によって別の捕捉候補へ落ちない。

元文法は、独立したnullary再帰helper群と一つの任意arity calleeからなる。
実引数はhelper呼出し列、本体の呼出しも独立helperに限る。このbackendではuser本体の相互再帰や
親依存actualは扱っていない。前節までのEOF backendを全面的に置き換えるものではない。
元のhelper宣言を変更せず、固定Seq側だけに出力フィルタ規則を生成する。
全宣言・開始式・helperの参照範囲を有限に検査し、実安定表の対応から
全入力・全残余・有限失敗・有限実行の存在・全clock未定義と元文字列受理言語を保存する。
新backendについて同clockや一定clock倍率は主張しない。

主例は元9規則から固定656規則・全nullaryのSeqへ。
`a`/`b`の内容による受理・拒否、同原点の二捕捉`a`/`ab`、候補外の長い保持値を拒否せず使う本体を検証した。
別のsuffix領域`{ab}`では`a`/`ab`を異なる非空語として保持し、再照合で`a`だけを消費して
非空の残余`b`を後続が読む元・Seq双方の直接実行を検証した。
balanced a/b再帰helperによる実捕捉もn=1,2,4で確認し、n=2の元・Seq双方を直接実行した。
nullableな実捕捉値の反復は空でない残り入力上でも全clock未定義を保存する。
未定義helperが先行する引数列は全入力・全clock未定義、逆順の有限失敗も保存する。
空dictionary、アルファベット外文字、guard省略の誤った一般化とその有限検査での拒否も検証した。

条件は引き続き**再照合する現在位置の有限suffix領域**である。
このguardなしでは、候補外の長い保持値が普通に一致する実反例がある。
任意の位置での無制限な再照合、任意user本体、および一般のPar/Seq一致・分離は未解決である。

## EOFで保持値を再照合する相互再帰文法の全体変換

`EmptyObservedSyntax`から`EmptyObservedCompiler`は、保持値の直接の再照合が
`(!any);param_k`（入力末尾の検査後の再照合）という形に限られる一階Par文法を、
固定の全nullary Seq文法へ変換する。この位置では、空の保持値だけが成功する。
この参照を含むseq/alt/not/starや、任意arityのuser呼出しと実引数の相互再帰は許す。
引数内でも親の保持値を同じ操作で調べたり、他のuserを呼び出して消費したりできる。
独立したnullary引数、scanner終端、固定アルファベット、捕捉長の上限は要求しない。

各calleeのarityに応じて有限個の空／非空パターンを列挙し、それぞれ通常結果と空成功だけを
残す二系統のnullary規則を生成する。実Par引数の左から右へのpreflight後、
実際の捕捉列の空性に従って規則番号を選ぶ。捕捉内容を列挙したり、値を入力へ符号化したりしない。
callee行の不変条件は、arityの合う**任意の実保持文字列列**について成り立つ。
空性判定も同じ相互再帰の一部として構成し、外部の停止判定や引数意味の仮定は受け取らない。

通常版／空成功版の式・引数の対応から実規則表の同clock対応を帰納的に証明した。
全入力の全残余・有限失敗・全clock未定義と、元文字列上の受理言語を保存する。
`EmptyObservedCompiler`は実際の全規則（arity/body）と開始式を有限構文比較で確認してから
この定理を適用する。コンパイラは通常版と空成功版を一緒に扱う構造再帰で、生成した実文法の
kernel直接実行も可能である。

具体例の元文法はarity `[0,2,2,1]`、Seqは固定22規則・全てarity0。
balanced a/bの再帰helperからの捕捉、親子で逆になる空／非空パターン、親の保持値への復帰、
親依存queryを含む実引数、実引数内のparameterized user呼出しを直接kernel実行で検証した。
三つの捕捉長（1/2/4組のa/b）と親子長1/3・3/1を確認し、任意入力文字列そのものを捕捉できる
実引数列の全入力・全clockの定理もある。同じ元文法をそのままSeqで動かすと失敗する例は、
文法変換の必要性を示す実行例であり、言語クラス分離ではない。
parameter依存の再帰実引数とnullableなparameter反復は、空入力で全clock未定義のまま。
preflightの評価順序、不正arityや範囲外calleeで引数を評価しない動作も検証した。

この変換は**EOFでの保持値参照という条件を残す**。元の実入力`ab!a`から得た二捕捉`a`/`ab`は
両方非空でも、`ab!`を消費した先では片方だけが再照合できる。
この実反例は空／非空だけでは一般の再照合を置き換えられないことを示す。
無guardのparameterを持つ実規則は有限検査が拒否する。
一般のPar/Seq言語クラスの一致・分離は未解決である。

## scannerによらない実捕捉の空／非空判定

`EmptyResultObservation`は、任意のnullary再帰PEG（引数なしの規則だけからなる文法）を、
元結果を保存する規則と空成功だけを残す規則の二系統へ変換する。規則数は元の2倍。
実Par表と実Seq表の同clockの関係を証明し、全入力・全有効位置・全clockで、
空成功をそのまま保存し、消費成功だけを有限失敗へ写し、元の有限失敗と未定義を保存する。
左右再帰・相互再帰・優先選択・否定・nullableなstarも構文として制限しない。
外部の停止判定やnullable判定は使わない。

seq/alt/starの空成功候補には、元の処理全体の先読みgateを置く。
空にならない前半を早く失敗させると後半の未定義が消えるため、このgateが必要になる。
優先選択では、先行枝が非空成功したときに後続の空成功へ落ちないよう元の先行枝の否定も保つ。
starは元の全反復を先読みしてから最初の本体の失敗を検査し、nullableな本体を有限失敗に変えない。

`EmptyCaptureDecision`はこの判定器を任意個の独立したnullary PEG引数へ接続する。
元Par引数を左から右へ全て先読みした後、実際の捕捉文字列列の`List.isEmpty`に従って
固定のSeq式が継続を選ぶ。捕捉長・捕捉数・停止終端のscanner条件は要求しない。
選ばれた継続は入力を消費してよく、first-order性も保存する。
ただし公開定理は、元の実`evParArgs`の結果と生成式の同clockの対応であり、
捕捉内容全体の復元や、任意のparameterized callee本体の文法変換までは証明していない。
前節までの`CapturedOriginCompiler`の適用条件をこの部品だけで取り除いたとは主張しない。

例では再帰する`a^n b^n`、`a*`、空式から得る互いに異なる三捕捉と消費する継続、
全て空の捕捉、失敗→無限再帰／無限再帰→失敗、未完成clockから有限結果への遷移を検証した。
前半消費後の無限再帰とnullable-starは全clock（後者は全入力）で未定義のまま。
seq/starのgate、選択の優先条件、引数preflightを省くと結果が変わる実反例もkernel検証した。
クラス全体の一致・分離は引き続き未解決である。

## 再照合後に別の保持値も読む入れ子検査

`CapturedOriginQuery.Plan.follow`は`&(param_k;plan)`を追加し、再照合後のplanでも
他の保持値を再照合できるようにした。従来のafter leafのclosed後続条件は維持するが、
入れ子のplan自体は親の両保持値を参照してよい。

新しい`ScannerFrontierValues`は、非空の最大文字集合scannerを読んだ終端では、
同じ原点からの非空捕捉は先頭文字が一致せず再照合できないと証明する。
他方の捕捉がscanner由来でなくても、元入力のprefixであれば同じ局所性質が成り立つ。
空の値だけはその場で再照合できる。入口の2ビットの空/非空検査から後続planを特殊化し、
最初の値が空の場合は原点に留まる通常のquery変換へ戻す。
seq/alt/not/starと再帰するclosed queryを含む既存の実テーブル対応・元文字列言語変換へ接続した。

元とSeqで両停止順序、親子順序反転、片方だけ空・両方空、空の値から非空の値へ進む
二段の再照合を検証した。`star(&(param0;&(param1;eps)))`は、片方でも空なら全clock未定義で、
両方非空なら本体の有限失敗でstarを抜ける。この条件を任意入力と実表で証明した。
二つとも非空なら後続のnullableな式へ入る前に再照合が失敗し、他方が空なら後続で未定義になる例も検証した。

この終端分類はstatelessな文字集合scannerの現在位置についてのもの。
状態が変わるscannerでは保持したabが終端の残りabへ再照合できる反例があり、
この規則を一般finite-state scannerや全ての後続位置へ拡張することはできない。
最大scanner終端・指定消費head・planの零幅制御という条件と、クラス全体の一致/分離は未解決。

## 保持値を再照合した先の検査を入口へ

`CapturedOriginQuery`は、元位置から`&(param0;C)`または`&(param1;C)`を実行する検査を扱う。
Cの両render先がclosedであることを有限検査し、実scanner引数から得た保持値なら、
その再照合と元scannerが同じ終端に達することを証明する。
検査をseq/alt/not/starで組み合わせても各部品は元位置へ戻るため、
この対応を全ての部分結果に持ち上げられる。starの空成功による未定義も保存する。
これは任意の位置でparamをscannerへ置き換える法則ではない。

`CapturedOriginNormalization`は、保持値依存の元queryをclosedな入口queryへ直す。
実capture tupleに限った行対応を再帰表で同clockに閉じ、全root観測を保存する。
`CapturedOriginCompiler`は独立実引数の元順序preflight、query書換え、Seq入口を接続し、
元clock k→Seq2k／Seqk→元kと全入力の元文字列言語・失敗・全clock未定義を証明する。
生成先は固定した12規則である。

実例は`&(param0;'c') / &(param1;'b')`で、保持値を入れ替えると同じ入力上で検査結果が変わる。
旧closed検査は元queryを拒否するが、新検査を通した生成queryはclosedである。
両停止順序n=1,2,4、親子順序反転と親二値復元、再照合後の実再帰helperもkernel実行した。
実捕捉済みqueryのnullable starはcanonical scanner引数を渡す元文法とSeqで全入力全clock未定義。
独立実引数が未定義ならquery以前のpreflightを保ち、これを省くと誤受理する反例も検証した。

後続Cが親保持値を再び読む場合は拒否する。最大scanner frontier・指定消費headと、
元位置から一つの保持値を再照合してclosed後続を読む検査形はまだ必要である。
一般の捕捉依存query／独立引数差分／Par/Seq言語クラスの一致・分離は未解決。

## 捕捉前の実再帰検査を零引数の入口で保つ

`GuardedPairSyntax/Simulation/Correspondence`は、元の二捕捉bodyを
`&Q;maxScanner(A,B);tail`へ広げる。Qはclosedな元のparserで、nullary helperや
同じ二捕捉userへの実再帰を含んでよい。常に成功・停止するとは仮定しない。
Seqは零引数の入口規則で元位置のQを先読みしてから、二つのchunkを捕捉する。
検査に元の捕捉環境を渡さずに済むことは、両render先のclosed構文検査から証明する。

実テーブルで、元clock kの結果はSeq clock 2kへ、Seq clock kの結果は元clock kへ保存する。
元引数の左順preflight準備も同clockで正確に表が一致することを追加証明したため、
`GuardedFrontierPairCompiler.bounds`はこの時計対応を展開前の元文法から直接与える。
全入力の残余・失敗・受理言語・全clock未定義を保存し、targetは固定した12規則である。

balanced a/bまたはa/cの実helperで元位置を検査する両順序と親子順序反転を実行した。
検査が同じ二捕捉userへ再帰し続ける場合の全入力全clock未定義も両側で証明した。
元引数が未定義なのに、その前に失敗する検査を走らせると有限失敗に変わる反例を確認した。
元1clock成功・Seq1clock未定義・Seq2clock成功となる小さい実例で、追加入口の費用も確認した。
捕捉値を直接参照するQは、入口へ移せないため検査で拒否する。

最大scanner frontierと指定消費headの条件は残る。一般の独立引数・任意の前半・
捕捉依存の原点検査への無条件変換と、Par/Seqクラス全体の一致・分離は未解決。

## 実scannerを前半に持つ二捕捉bodyをSeqへ

`ScannedPairFusion`は、元の二引数bodyが保持値を先頭再照合する条件を外した。
元bodyは`maxScanner(A,B);tail`で始まる。maxScannerは入力から停止順序を選び、
長い方の文字集合scannerを実際に走査するclosed parserで、保持値paramを読まない。
nullary helperと二捕捉userの実テーブル対応を、実引数から得た終端に限って同時帰納する。
生成Seqは前回と同じ二つのchunkを捕捉し、元の両値を復元して同じtailへ入る。

`ProducedFrontierPairCompiler`は、独立再帰引数の元の左順検査を残す準備から、
この新しい元bodyへ全grammar/rootの有限AST一致検査で接続する。
全入力の残余・失敗・元文字列言語・全clock未定義を保存し、元の先頭replayは要求しない。
例では両停止順序、親子で長短が逆になる再帰、空捕捉の子、親二値復元を元/Seqで検証した。
二つの文字集合の和を走査すると長い方の終端まで越える`abc!ab:a`の反例を確認し、
そのheadを誤って通す構文検査ではないことも検証した。
同じ元文法をそのままSeqで動かす例は2文字を残すが、生成文法は全消費する。
これは文法変換の必要性を示す例であり、クラス分離の主張ではない。

最大scanner終端という実引数条件と、そこまで読む指定closed headは残る。
任意PEG前半・任意停止位置への一般変換とPar/Seqクラス全体の一致/分離は未解決。

## 独立した二つの再帰捕捉の順序を入力から選ぶ

`MaskedScannerAbsorption`は文字集合ごとに消費経路の安全なhelper候補を計算し、
その集合の閉包を別途有限検査する。実際に消費経路で使うhelperだけに実テーブル不変量を立てるため、
`{a,b}`と`{a,c}`を読む再帰規則を同じ元文法へ置ける。負の先読みは元の計算を保ち、
候補生成の収束・helperの停止性・成功終端を入力仮定にはしない。

`MixedScannerPairFusion`は既存の二scanner終端選択を、nullary再帰helperと二引数userが
混在する固定文法へ拡張する。helper行と二捕捉行の対応を同じphysical clockで閉じた。
`FrontierPairCaptureCompiler`は元引数の左順先読みを保持する準備から、このbackendへ
全grammar/rootの有限AST一致検査で接続する。二つの文字集合に包含順序は要求しない。
入力から選んだ終端順序で二つのchunkを捕捉し、両方の元の値を復元する。

具体例は、`a^n b^n`または先頭a-runを読む引数と、`a^n c^n`または先頭a-runを読む引数。
それぞれ別の実再帰helperを使い、8規則のSeqへ。n=1,2,4で両順序の実捕捉と元/Seqの実行を検証した。
親と子で順序が逆になる再帰、子から戻った親の二値復元、空捕捉の子、
先読み省略による不正個数の誤受理、nullable引数の全入力全clock未定義も検証した。
全入力の観測・元文字列言語は保存するが、成功捕捉が最大scanner runの終端にある条件は残る。
元の二捕捉bodyは入力から長い方を選んで先頭再照合する形である。
任意のPar引数・任意のbodyを扱う一般変換とクラス一致/分離は未解決。

## 独立した再帰引数を入口の実検査とscanner捕捉に分ける

`FrontierArgumentNormalization`は、各実引数を独立した再帰parserとして書ける入口を追加した。
引数は`P;!choice(A)`であり、Pと実nullary helperの消費経路が文字集合Aの中だけにあることを
有限検査する。成功すればAの最大runと終端が一致することを、元文法の実テーブルから導く。
`F(arg0,...,argN)`を、元の引数を同じ入口で順に先読みしてからscanner実引数を渡す呼出しへ
変換する。元の順序で失敗・未定義を保存し、成功時は全捕捉tupleが同じになる。
helperの意味や成功終端は仮定として渡さない。

`FrontierArgumentCompiler`は全bodyと開始式を変換し、実再帰文法の観測を保存する。
`FrontierCaptureCompiler`は、その先を選択producer正規化と既存`NestedScannerFusion`へ有限AST検査で
接続し、固定した一階Seq文法で元文字列言語・失敗・全clock未定義を保存する。
具体例では、別々のparserが`a^n b`と`a^n b c^n`を同じ入口から捕捉し、Seqは`a^n b`と`c^n`を
順に捕捉して復元する。後者のhelperは`R ← a R c / b`という実再帰規則である。
3規則arity `[0,0,2]`で、全nと全suffixの実捕捉・正例の受理を証明し、異なる親子値を実行した。
先読みを省くと`a b c c`を誤受理するkernel反例もある。

連続chunkによる復元自体は既存のnested scanner backendを再利用する。
新しい接続は、累積構文やscannerそのものではない、部分的な再帰実引数の入口検査を保存するもの。
捕捉終端が文字集合の最大runと一致する条件と、scanner集合の包含順序が必要である。
任意の独立したPar引数から差分parserを生成する一般構成と、クラス全体の一致・分離は未解決。

## 実producerと複数の累積捕捉をSeqへ

`SelectedProducerNormalization`を、選択規則の任意の正のarityへ拡張した。
実body `D;B` のDを最後の実引数と照合し、全引数の捕捉値を保持したまま
`param(arity-1);B` へ正規化する。普通の規則も選択規則も元のarityを保つ。
`ProducedPrefixFamilyCompiler`は、その出力が既存`PrefixFamilyFusion`の累積捕捉文法と
一致することを有限構文検査し、固定Seq文法へ接続する。
成功残余・有限失敗・定義性・全clock未定義と、元文字列上の受理言語を保存する。

具体例では、同じ入口からParが`a^n`と`a^n b^m`を捕捉し、Seqが順に`a^n`と`b^m`を捕捉する。
元のbodyは全体を読む実再帰producerで始まり、先頭で捕捉値を再照合する構文ではない。
生成先は3規則、arity `[2,0,0]`。親子の別々の値の保持・復元も実行する。
これは既存の累積引数/連続chunk backendと新しい複数引数producer正規化の接続であり、
任意の独立したPar実引数から差分parserを生成する一般変換は未解決である。

## 実再帰producerと、捕捉終端より手前のliteral前半を接続

固定literalを保持値の前から後ろへ回す証明と、その値のprofileを選ぶSeq productは既存である。
`ProducedScannerCompiler`は、そこへ実再帰producerを含む元文法を接続する。
`SelectedProducerNormalization`は一般の一階文法で選んだ正のarityのproducerを正規化し、
選ばないarity 0や複数引数の規則をそのまま保つ。実再帰テーブルの双方向対応を証明し、
正規化先が既存profile backendの実sourceと一致することを有限AST検査で確認する。

元文法では全nの実a^n捕捉があり、別のuserが`a;w;":";w`を実行する。生成Seqは65規則である。
引数がn文字を捕捉する一方、前半literalは1文字で終わるため、n≥2ではその終端が実際に異なる。
既存の回転により、Seq側は捕捉後に残余aを読み、そのあとも同じwを使える。
親子の別長値の捕捉・復元、短いコピーの拒否、nullable producerの全入力全clock未定義を検証した。
これは既存の位置回転法と再帰producerの接続であり、任意の異なる成功終端を扱う一般変換ではない。
一般のPar/Seq一致・分離は未解決のままである。

## 別の引数parserを共通の成功終端から正規化

`CanonicalProducerCompiler`は、実引数Aと消費前半Dが同じ構文である制約を拡張する。
元の実bodyが`D;B(w)`なら、`F(A)`を`&A;F(D)`へ変換する。
AとDが両方成功した際の終端だけを共通のclosed core Cから有限認証し、
失敗・停止性が同じとは仮定しない。元のAを先に評価し、Dは実引数として残すので、
Dだけが失敗・発散する場合も保存する。全bodyと開始式を変換して実再帰文法へ接続した。

`EndpointSupport`は実評価での成功からcoreの同終端成功を導く。文字/rangeからanyへの拡張、
実零幅queryの前置・後置、同coreへ成功する選択、sequenceを有限検査する。
coreは実再帰calleeを含んでよい。Aは親の保持値を検査するqueryを含んでよい。
このcanonicalization自体は、実引数と前半を同じcoreへ接続できない場合や、成功終端そのものが異なる場合を扱わない。
生成Seqの規則数はn(n+2)+bのままで、元文字列・全残余・有限失敗・全clock未定義を保存する。
26規則の実例は親値を検査しながら別の子値を捕捉し、両方を復元する。

## 実再帰producerと零幅実calleeを混合文法へ接続

`RecursiveProducedCompiler`は、上記producerのcall-free制約を外す。
実引数と前半で同じclosed parser Dを評価する条件の下で、Dは実再帰userや、
前半を変換するclient自身を呼んでよい。実引数評価で得た成功から捕捉条件を導き、
元と正規化先の実安定テーブルへの双方向の帰納で、全残余・有限失敗・全clock未定義を保存する。
ここでは同clock一致を主張せず、入力依存の実有限安定化上界を使う。
生成Seq文法は入力非依存で、n(n+2)+b規則のままである。

`ParReturnEffects`と`CheckedOriginCompiler`は、実calleeの成功が零幅であることを有限検査から
全入力・全clockへ証明する。普通の保持値rowが消費しても、実empty-bound cloneだけを認証できる。
`RecursiveProducedOrigin`はこれを同じ元文法へ組み込み、実sequenceの零幅headerと、
再帰producerによる消費前半の両方を固定Seqへ接続する。27規則の実例は親子で別の値を捕捉・復元する。
無制限長a^n bの実引数捕捉、producer/client依存cycle、全入力で発散するproducerも検証した。
実引数と異なる前半については、上記の共通成功終端を有限認証できるケースを接続した。
一般の消費前半、異なる成功終端、Par/Seq一致・分離はなお未解決である。

## 実引数と同じproducerを消費するclosed前半を混合文法へ接続

`ParserPrefixFusion`には既に、同じclosed parserを引数とPar本体の前半で評価する単独の
融合証明がある。`ProducedPrefixCompiler`から`ProducedPrefixCorrespondence`はその
`Pure`とparser独立性の証明を再利用し、正倍率成長・forwarding・origin制御と
相互に呼び合う実文法へ接続する。前半のparser Dはcall/parameterを持たない任意のPEG式で、
選択・先読み・反復を許す。nullable反復も拒否せず、その未定義を保存する。

追加entryは`produced D B`で、元のPar本体は`D; B(w)`である。
そのentryへの全実呼出しが構文的に`F(D)`であることを、元の全bodyと開始式について
有限`conforms`で検査する。引数が同じDであることから、実捕捉の終端と本体でDを
再評価した消費終端が一致する。これにより本体を`param0; B(w)`へ正規化できる。
捕捉語の長さや有限集合を仮定せず、Dの実成功結果からその都度捕捉値を導く。
他のgrowth/origin entryへの引数は従来どおり動的な一階式でよい。

この書換えは任意の環境Eでは正しくないため、無条件のbody同値を仮定しない。
`tables_rows`はproducer行だけを実捕捉に条件付け、他の行は全保持環境で対応させる。
実引数の有限検査から各producer呼出しの条件を導き、全再帰行を同じ通常clockで閉じる。
origin Planの元leaf範囲も検査し、追加partsへの不正aliasを防ぐ。正規化後の実混合文法は
既存`MixedForwardingCompiler`へ渡す。全観測・失敗・全clock未定義を元文字列上で保存し、
targetはn(n+2)+b規則、inline source clock k ≤ Seq clock k ≤ source clock (n+2)kである。

`ProducedPrefixHeaders`は、元の前半を実`H(empty)`呼出しとして保持する。
Hの実宣言がarity1で、bodyが指定producer Dと一致することを有限検査し、先に一段展開する。
この元Par文法からも全観測と言語を保存し、source clock k ≤ Seq clock k ≤ source clock
2((n+2)k)を得る。callee行の意味を外から与える仮定はない。

`ProducedPrefixExamples`のDは`a*;b`で、実closed calleeが捕捉終端まで消費したあとに
親wを使う。親wを3倍化する規則、新しい位置で同じproducerから別のvを捕捉する再帰、
`c*`を渡すorigin規則を経て、growth側のwとproducer側のwをそれぞれ復元する。
直接例はwのa部分長0/1/4、新捕捉vのa部分長4/0/2で、27規則のSeqを実行する。
originの早い復帰、誤引数と誤callee宣言の拒否、arity検査、helper privacy、
nullable producerの全入力全clock未定義も検証する。実calleeを含む小さい例は、元source
clock1では未定義、clock2で成功し、生成Seqはclock1で成功する。
引数をD以外へ変えると元sourceだけ受理する実反例があり、`conforms`はこれを拒否する。
これは変換の検査条件の必要性を示し、言語クラスの分離ではない。

この前半が消費する終端は、検査した引数Dの実捕捉終端と一致する。
同じDを実再帰で計算する場合は、上記`RecursiveProducedCompiler`で接続した。
それと異なる位置へ返る一般のconsuming closed prefix、検査外の呼出し・複数独立捕捉、
一般のPar/Seq一致・分離は未解決である。

## 親の保持値を使う後続を成功復帰の位置に応じて接続

`OriginTailPlan`から`OriginTailInlining`は、下記でClosedに制限していた親tailを拡張する。
子のPlanの全leafではなく、成功して後続へ返る箇所を`Exits`で追う。altの両側は復帰箇所を
持つが、guardの第1項は先読み専用であり、そこで親tailを実行することはない。
notPが成功する場合は元の位置へ返る。`append_eval`はこの区別の下でcommitted choiceと
有限失敗・未定義を保存する。

有限`flowCheck`は、子の成功復帰箇所について次のいずれかを要求する。

- replay partから返るなら、親tailは任意の一階式でよい。子の新しい`w^m`を再照合したあと、
  子のCは`w^m`へscopeを固定し、親tailは元のwを保持した環境で実行する。
- closed partから返るなら、従来どおり親tailがClosedでよい。また、closed partが有限構文検査で
  零幅成功しか持たず、親tailが`param0; C`なら、元の位置でそのqueryを検査してから親wを再照合できる。
- notPの成功で元位置へ返る場合も、親tailがClosedまたは`param0; C`であることを要求する。

query専用subtreeはこれらの復帰条件を要求しないが、元のPlanに残り、失敗も未定義も保存する。
そこでしか使わないclosed partに、実行されない親tailを無条件に付けてbackendへ渡すことをやめた。
`closed_parts` / `closed_plan`はClosed tailで以前の生成文法と一致すること、
`extends_closed_check`は以前の有限検査を通る入力が新検査も通ることを証明する。

`OriginTailInlining`は実混合sourceのbody rewriteと既存Seq backendへつなぎ、入力の一階性、
実entryのlookupと有限checkから、元文字列の全観測・失敗・全clock未定義を保存する。
規則数はn(n+1)+3b+3、mixed source clock k ≤ Seq clock k ≤ source clock 2((n+2)k)である。
`OriginTailRawCompiler`は元の`MultiplyingPrefixCompiler.source`からの接続も保持する。
意味的な復帰位置のoracle、有限捕捉語集合、入力変換は使わない。

`OriginTailExamples`では、子に渡した`w^3`を再照合し、親tailで`!; w; parent(x); w`を実行する。
childの`w^3`とparentのw、新しいxを区別し、再帰から戻ったあとにも親wを復元する。
先読み専用closed partは実userへ`c*`を渡し、成功時に入力を進めるがguardが元位置へ戻す。
`w=c^n d`（n=0/1/4）と親aの生成Seq実行、child値を親へ漏らした入力の拒否、committed child、
query失敗と引数preflightをkernel検証する。別の元文法では、零幅closed成功とnotP成功から
`w; C(w)`へ接続する。nullableなqueryの全入力・全clock未定義もsource/targetで証明する。
元のSpec文法で親の保持値を使う後続を持つ例にも、全入力観測定理を適用する。

入力を消費するclosed成功から親の保持値を使う後続へ戻る場合は、上記で実捕捉と同じ
producerの消費終端へ返るケースを接続した。一般の場合、成功復帰の上記条件を
満たさないPlan、複数headの自動閉包展開、一般PEG prefix、独立複数捕捉、
一般のPar/Seq一致・分離は未解決である。

## 正倍率headからorigin規則への直接呼出しを展開

`OriginHeadInlining`は、選択した1本の正倍率headがorigin entryを直接呼ぶ場合を扱う。
親のtailは`Closed`、factorは1以上とし、子はclosed/replay part上の任意のPlanでよい。
親fallback、子part、開始式、新しい呼出し引数は任意の一階式を許し、子のpartから親へ
戻る実再帰も許す。残りの文法と展開後の有限検査が既存混合backendに適合することを要求する。

子へ実際に渡した`w^m`をWord代入で子のscopeへ固定する。replay partは親の先頭`w`を
照合したあと、残りm-1個を読み、子本体のparam0を`w^m`へ置き換えて実行する。
closed partは原点から実行する。caller側のguardは、closed分岐を実行する場合にも
`w^m`全体の引数preflightを先に検査する。親の元のwと子の新しい`w^m`は混同しない。

後続を子の選択へ単純に分配すると、子の成功後に後続が失敗したとき、子の別分岐を
再試行してしまう。`OriginHeadPlan.after`は、選択した側の成否をguardとnotPで固定して
から後続を実行する。任意の有限Planと任意の部分的な後続結果について、この変換が
成功・有限失敗・未定義を正確に保つことを証明する。子のguard/notPにも対応する。

`OriginHeadParts`は元のpartsを保ち、scopeを変えたparts、後続付きparts、tail、
preflight、fallbackを有限に生成する。元のorigin Planのleaf範囲も検査し、追加された
partsが元の範囲外leafに誤って見えることを防ぐ。対象のhead以外の規則とarityは保持する。
一段の実call展開の後、既存`MixedForwardingCompiler`へ渡し、同じ元文字列言語と全残余、
有限失敗、全clock未定義を保存する。n規則・b partsならtargetはn(n+1)+3b+3規則で固定され、
元の混合source clock k ≤ Seq clock k ≤ source clock 2((n+2)k)を満たす。

`OriginHeadRawCompiler`は元の`MultiplyingPrefixCompiler.source rs`からの接続も行う。
空引数headのPar展開を、旧backendのcallee種別検査と分離し、その後に選択headを展開する。
これにより、旧backendが拒否した「正倍率headから倍率0のorigin規則を直接呼ぶ」元文法を
同じ言語のSeq文法へ変換できる。元sourceの一階性、実entryの有限lookup、有限check以外に
意味的なcallee行の仮定を要求しない。

`OriginHeadExamples`の元文法は、親wから子へ`w^3`を渡す。子のclosed分岐が捕捉終端より
手前へ返る例と、子のreplay分岐が`w^3`を照合し、新しいxを親へ渡して戻ったあとに再び
`w^3`を照合する例を、33規則の生成Seqで直接検証する。`c*`部分が長さ0/1/4の`c*;d`捕捉、
preflight省略の誤受理、子選択の誤った再試行、親fallback、nullable引数、短い子値、
helper privacyも確認する。全入力に対する言語・観測の一般定理をこの元文法に適用する。

親tailが保持値に依存する場合は上記の成功復帰条件で拡張した。条件外の後続、
複数のheadを閉包まで自動展開する手順、一般PEG prefix、
独立複数捕捉、一般のPar/Seq一致・分離は未解決である。

## factor-1の経路と循環も混合Seq compilerへ接続

`MixedForwardingCompiler`から`MixedForwardingCorrespondence`は、下記の混合compilerを
factor-1まで拡張する。`Entry.growth`は倍率1以上を許し、`Entry.origin`は従来どおり
任意のclosed/replay Planを持つ。正倍率headの既知calleeは正倍率entryであることを
要求する。tail/fallback、origin part、開始式、新しいPEG引数は任意の一階式でよく、
両種類のentryの相互callbackを許す。

実original文法から正倍率entryだけを選択し、`SelectedForwardingNormalization`で有限head
展開する。factor-1 edgeは選択した実正倍率規則に閉じることを静的に確認する。
非選択origin規則は本体を保つ。calleeごとのparameter scopeと選択の括弧を保持し、
閉じたfactor-1循環はpreflight後の非消費未定義へ写す。targetの有限head codeは同じ
経路と循環を使い、倍率2以上に達したところで既存の複数等値引数へ移る。
metadata上のcodeの一階性は構文補題だけに使い、行の意味は実混合文法のtblVで証明する。

`tables_rows`は展開後sourceの全正倍率view行とorigin Plan行を同時に閉じ、
全一階式がtarget Seqと同じ通常clockで一致する。`observations_iff`と
`original_undefined_iff`は展開前original文法に戻り、全残余・有限失敗・全clock未定義を
保存する。targetはn(n+1)+parts.length個の固定規則であり、
original clock k ≤ Seq clock k ≤ original clock (n+2)kを満たす。

`MixedForwardingReset`は、元の`MultiplyingPrefixCompiler.source rs`に対して
倍率1以上を正倍率entryへ、倍率0を一段展開したorigin Planへ自動変換する。
既知reset calleeの後続は親parameterから独立であることを検査する。
source一階性と有限`check`から、n(n+3)規則の固定Seq文法、元文字列の言語・観測・
未定義保存、source clock k ≤ Seq clock k ≤ source clock 2((n+2)k)を得る。
入力長、実捕捉値、再帰深度は規則集合や有限展開深度を増やさない。

`MixedForwardingExamples`は同じraw文法にfactor-1経路、`ab → (ab)^3 → (ab)^9`の
実成長、倍率0のcalleeと`c*`の新捕捉、別の`x`を渡した再帰、2規則factor-1循環を置く。
生成Seqを通常clock16で実行し、捕捉終端より前のreset復帰、成長した親値とforwarding親値の
復元、長さ0/1/4の新捕捉、短い親値の拒否を確認する。明示的origin Planとforwardingの
相互callbackも検証する。factor-1循環の空引数呼出しは全入力全clockでsource/targetとも
未定義である。preflight失敗、同clockのsource/target差、committed choice、helper privacyも確認する。

正倍率headからorigin entryへの直接呼出しは、上記で親tailがClosedの場合に対応した。
親保持値に依存する後続、独立複数捕捉、
一般のPar/Seq一致・分離は未解決である。

## 成長headと原点分岐を同じ再帰文法からSeqへ変換

`MixedGrowthCompiler`から`MixedGrowthCorrespondence`は、それまで別文法だった
倍率2以上の保持値成長headと、`ReplayControlFusion.Plan`の原点制御を一つのsourceへ
統合する。成長規則のtail/fallback、原点規則のclosed/replay part、開始式と新しい
引数は任意の一階式でよく、両種類の規則の間の相互再帰を許す。
成長headの既知calleeは成長規則であることを要求する。tail/fallbackから原点規則を
呼ぶこと、原点規則のpartから成長規則を呼ぶことは制限しない。

targetはn(n+1)個の成長用view規則と、parts.length個の原点用0/1引数helperを持つ。
sourceの成長呼出しは等しい保持値の複数引数へ、原点呼出しはpreflightを保った
caller側のPlanへ変換する。`MixedGrowthCorrespondence.tables_rows`は、成長viewの行と
原点Planの行を一つの同時帰納で閉じる。原点partを別文法の意味で解釈する仮定や、
callee行の意味を外から与える仮定はない。全source式と生成式は同じ通常clockで一致し、
全残余・有限失敗・全clock未定義・元文字列の全消費言語を保存する。
`MixedGrowthChecks.check`は一階構文、closed part、Plan leaf範囲、倍率、headのcallee種別を
有限検査する。`MExp.fo`はここで必要なparameter付き一階性とは別の既存判定なので使わない。

`MixedResetCompiler`は元の`MultiplyingPrefixCompiler.source rs`からこの混合sourceへ
自動的につなぐ。倍率2以上の規則は成長規則として保持し、それ以外は空引数calleeの
一段展開でclosed/replay Planへ移す。calleeが存在するresetは倍率0を必要とし、
展開分岐のclosed検査は親tailの捕捉依存を拒否する。missing headは有限失敗を保存する。
元sourceの一階性と有限`check`だけから、n(n+3)個の固定Seq規則、
source clock k ≤ Seq clock k ≤ source clock 2k、全観測と全clock未定義の保存を得る。
元sourceは入力・clock・実捕捉値に依存せず固定される。

`MixedGrowthExamples`は`ab → (ab)^3 → (ab)^9`の途中で原点規則へ移り、`c*`を新しく
捕捉し、成長規則へ別の`x`を渡して戻ったあと、`c*`と各親の完全な保持値を再利用する。
`MixedResetExamples`では同じ成長列の途中で倍率0の子が`c*`を原点から読み、
`c*!xgab`という実捕捉の終端より前へ戻り、その後に親の`ab`または`(ab)^3`を再照合する。
長さ0/1/4の新捕捉、親値を短く取り違えた入力の拒否、preflightの失敗・nullable未定義、
reset fallback、helper privacy、全入力全clockの空引数自己再帰未定義をkernel検証する。

factor-1 forwardingを含む混合sourceは上記の拡張で対応した。Closed tailを持つ選択headから
原点calleeへの直接呼出しもさらに上の前段で対応する。
親保持値に依存するreset後続、独立複数捕捉、一般のPar/Seq一致・分離は未解決である。

## 原点へ戻る空引数calleeをSeqへ接続

`ZeroResetOrigin` / `ZeroResetCorrespondence` は、下記の正倍率compilerが拒否した
倍率0の具体例を、同じ元文字列言語のSeq文法へ変換する。sourceは既存の
`MultiplyingPrefixCompiler.Spec` の規則族
`F_i(w) := (F_next(w^m_i); B_i(w)) / (w; C_i(w))` である。
有限検査`check`は、head calleeが存在する規則について、倍率0と
`ReplayFallbackFusion.Closed B_i`（親parameterに依存しない構文）を要求する。
calleeが存在しなければheadは有限失敗するため、倍率とtailを制限しない。
全source規則と開始式が一階であること以外に、fallbackや新しい動的PEG引数を
制限せず、再帰・相互再帰も許す。

存在する空引数calleeの本体を一段だけ`subst [lit []]`で展開し、その後のClosed tailと
合わせて原点独立の分岐にする。calleeのparameter scopeはこの代入で固定される。
その分岐と元の`w; C_i(w)`分岐を、既存の`ReplayControlFusion`へ渡す。
従って新しいtargetは2n個の0/1引数規則からなる固定一階Seq文法であり、入力の
符号化、有限捕捉語集合、アルファベット制限、実行時の規則生成を使わない。
開始呼出しでは引数のpreflightを保持し、その失敗・未定義も保存する。

`physical_bounds`は任意の実source/target tblVに対してsource clock k ≤ Seq clock k、
Seq clock k ≤ source clock 2kを証明する。`observations_iff`、`undefined_iff`、
`language_translation`は展開前sourceの全残余・有限失敗・全clock未定義と、元文字列の
全消費言語を保存する。これは両方式を別々に保つ空捕捉specializationから進み、
実際のPar→Seq変換になっている。

`ZeroResetExamples`は、旧compilerで`a!`の末尾`!`が残る例の新target受理、
3文字捕捉後に2文字だけ消費する原点分岐、preflight省略の誤受理、nullable引数の
未定義をkernel検証する。相互再帰で`a!`を消費し、新しい`c*`を渡し、さらに
別の親呼出しへ`x`を渡してfallbackで再利用するsource/targetも直接実行する。
空引数自己再帰の全入力・全clock未定義も証明する。
倍率0の後続が親の保持値に依存する場合と、一般のPar→Seq変換は未解決である。

## 異なる本体が混在する実文法で選択的にforwarding headを正規化

`SelectedForwardingContext`から`SelectedForwardingNormalization`は、正倍率head展開を
任意の一階実文法の選択した規則へ適用する。有限`check`は実arity/bodyとmetadataの
一致、factor-1 successorの選択集合内への閉包を検査する。非選択規則は任意の本体・
arityを保ち、そのmetadataは本体を記述する必要がない。補題のtableはすべて実文法の
tblVであり、metadataから作った別文法の行対応を仮定しない。
原点独立分岐と正倍率headの相互呼出しを含む例、選択したcycleと非選択0引数規則の
共存、元のarity・観測・全clock未定義の保存を検証する。
これは混合文法のPar→Par正規化であり、上記のfactor-1対応混合Seq compilerの前段として
実際に接続されている。

## 空捕捉の実呼出しを任意の一階文法で0引数化

`EmptyArgumentSpecialization` は、任意の一階文法について、有限構文検査`zeroCheck`を通る
単一引数呼出しをguardとnullary cloneへ写す。検査は成功時の捕捉が空語になることを保証する。同じ方式のまま行う正規化であり、
Par/Seqのいずれについても元文字列上の全有限観測・有限失敗・全clock未定義を保存する。
残る実引数をliteral/parameterだけへ制限せず、入力依存の任意PEG引数と他のarityを許す。
文法は原規則の通常版と0引数版からなり、規則数はちょうど2nである。

`zeroCheck` はepsilon・空literal・任意の否定query・それらのsequence/choice/starを調べる。
`zero_success` は、成功時の終点が必ず元の位置と一致することを任意の表で証明する。
入力依存の失敗や未定義を消さないため、`F(A)` は
`render(A); F_empty()` とし、Aの判定を省略しない。Aがnullableな反復なら非消費成功による
未定義もguardの側で保持する。calleeの存在とarityはguard評価前に調べる。

clone本体には`subst [empty]`を施す。元calleeのparam0は空語、範囲外parameterは失敗へ
写り、親の保持値へ漏れない。通常規則の全動的環境とcloneの空語環境について、
`EmptyArgumentCorrespondence.tables_rows` が実source/target tblVの対応を同時帰納で閉じる。
実行結果は同clockで一致する。cloneの表がcaller環境に依存しないことも証明する。
意味論的行oracle、入力の注釈、捕捉値全体の有限palette制約はない。

kernel実行は、入力依存lookaheadの成功/失敗、guard省略による誤受理、nullableなquery反復、
arity不一致時に未定義引数を評価しないこと、helper番号の非公開化、c*の動的引数、
二引数規則、cloneのparameter scope、空呼出し再帰の全入力全clock未定義を確認する。
倍率0のa!反例も、Parの受理とSeqの拒否を、それぞれ元位置のまま正確に保存する。

この変換だけではParからSeqへの移行を証明していない。空語calleeの実行を元の位置で
nullary処理へ分離できたが、親の非空captureの後のSeq位置からその処理へ戻る問題は残る。
独立prefixと保持値依存継続の接続、独立複数捕捉、および一般Par/Seq一致・分離は未解決である。
検証は全1135 jobs（Auditを含む）、関連1255定理の標準Lean公理／公理なしの依存検査、
新規39guard（PR66計260guard）。

## 保持値転送と正の倍率更新を同じSeq文法へ接続

`ForwardingSeqCompiler` は各規則が
`F_i(w) := (F_next(w^m_i); B_i(w)) / (w; C_i(w))`
という形で、固定されたm_i≥1を持つ有限一階文法を扱う。倍率1の有限転送経路・転送閉路と、
倍率2以上の成長を同じ文法で混在させられる。B/Cと開始式は任意の一階式を許し、
fresh PEG引数、選択、否定、star、自己/相互再帰を含められる。元文字列上の全有限観測・
有限失敗・全clock未定義を、一つの固定一階Seq文法へ保存する。

Seq側のheadは、Par側の有限展開器と同じfuel/規則番号/訪問済み集合を辿る。
転送辺は引数を再消費せず子のheadへインライン化し、子の結果のあとへ親tailをつなぐ。
親fallbackの開始位置と選択の括弧を保つ。閉路は非消費の未定義へ、missing calleeは
親fallbackへ写す。成長辺だけで追加のコピーを分割捕捉し、子の倍率版へ入る。
生成規則数はちょうどn(n+1)、保持語の長さや再帰深さで版の数は増えない。

`ForwardingSeqHead.evaluator` は、完成した有限head展開とSeq headの局所一致を証明する。
`ForwardingSeqCorrespondence.tables_rows` は、展開後Parと生成Seqの実tblVについて全保持版の
行対応をclock帰納で閉じる。両者は同じ通常clockで一致する。元Parへの有限展開の対応と
合成すると、元clock k≤Seq clock k、Seq clock k≤元clock(n+2)kとなる。
最終`observations_iff`と`language_translation`は展開前の実Par文法をsourceとする。
有限語palette、alphabet/profile制約、意味論的行oracle、外部の停止仮定は渡さない。

kernel実行は転送から3倍再帰へ入るabの1/3/9/27コピー、2段転送の親継続!/?への復帰、
転送閉路、missing callee、引数不一致、選択のcommitを確認する。継続内でc*により新しい
引数を長さ0/1/4で捕捉し、親abへ戻る実行も直接Seqで検証する。
追加のSeq引数へ元の範囲外param1が漏れないことも、否定検査と親値復帰を含めて検証する。
単独の倍率1閉路で空引数を渡す場合は、全入力・全clockで元/Seqとも未定義と証明する。
元clock1では未定義、Seq clock1では成功する例も残し、同clock一致を元文法には仮定しない。

倍率0は含まない。空語を渡した子が親の捕捉前の位置からaを消費し、親が!を続ける例では、
元がa!全体を受理するのに、このSeq構成は!を残す。Validの拒否とこの実反例を検証した。
これは変換の境界であり、言語クラスの分離ではない。コピー以外の語更新、独立複数捕捉、
任意Par文法のこの規則形への正規化、および一般Par/Seq一致・分離は引き続き未解決である。
検証は全1131 jobs（Auditを含む）、関連1216定理の標準Lean公理／公理なしの依存検査、
新規49guard（PR66計221guard）。

## 非循環の転送headをスコープ付きで有限展開

`ForwardingHeadExpansion` は、転送headをn+1段まで辿って実callee本体へ展開する。
元の規則数をnとすると、その深さで打切りが使われないことを転送headの有限グラフについての
非fuel切れ定理から証明する。閉路ならpreflight付き未定義へ、非転送規則または
未定義calleeならその本体へ止まる。展開中も実引数を再照合する検査を残す。

各callee本体には`subst [param0]`を施す。これにより、calleeの範囲外parameterは失敗へ写り、
親に余分な保持値がある環境でも漏れ出さない。選択の括弧も
`((A / B); parentTail) / parentFallback` のまま保ち、sequenceへ分配しない。
`WordExpansionRefinement` は、任意のWord引数に対し、このスコープ付き展開の情報順序を
実引数評価込みで持ち上げる。

`ForwardingHeadBounds` は元本体のclock kを展開本体のclock kへ、展開本体のclock kを
元本体のclock k+n+1へ写す。`FiniteBodyRewrite` は、実source表でのこの有限遅延を
文法全体の実source/target表へ接続する。`ForwardingHeadNormalization` の生成文法は
Par文法であり、元clock k≤展開clock k、展開clock k≤元clock(n+2)kを証明する。
一階性、元文字列上の全有限観測・有限失敗・全clock未定義を保存する。
意味論的行oracle、外部の停止仮定、捕捉語paletteは渡さない。

kernel実行は、転送から3倍再帰へ入る非循環経路、2段転送の親継続への復帰、閉路、
捕捉語abの1/3/9コピーを確認する。元clock1が未定義なのに展開clock1では成功する例を
直接検証し、同clock一致を仮定していない。余分な親parameterを読む誤った展開と、
選択を分配して誤受理する実反例も検証する。

これはこの規則族のPar側の有限head正規化である。展開後の選択木は上記の正倍率compilerへ接続できた。コピー以外の更新、独立複数捕捉、
および一般のPar/Seq一致・分離は引き続き未解決である。
検証は全1124 jobs（Auditを含む）、関連1167定理の標準Lean公理／公理なしの依存検査、
新規33guard（PR66計172guard）。

## 倍率1の転送閉路を自動判定して除去

倍率1を含む同じ規則族に対し、`ForwardingPrefixTrace.classify` は各規則の先頭の
factor=1呼出しだけを辿る。高々n+1段で、非転送規則または未定義calleeで停止するか、
閉じた転送集合を返す。fuel切れが起きないことを、訪問済み番号の重複なし・範囲内という
不変量と有限個数の上界から証明した。閉路側は全訪問規則のfactor=1、実規則の存在、
calleeの集合内所属を有限検査する。集合には閉路へ入る経路も含まれる。
任意の閉じた転送集合に入る番号が自動でcycle判定されることも証明している。

`ForwardingPrefixCycles.rows_none` は、この有限な構文条件から、実tblVが全通常clockで
未定義になることを任意の入力・任意の読み取れる保持語で証明する。tail/fallbackの内容に
意味論的制限は要らない。元のfactor=1引数が保持値を元位置で捕捉し直し、同じ位置・値の
callee行を呼ぶため、閉路に入ると有限失敗でfallbackへ移ることがない。

`ForwardingCycleElimination` はcycle判定の規則本体を
`&param0; (empty)*` に置き換え、それ以外を保つ実文法を生成する。
先頭のpreflightは必須で、保持値が欠ける・入力と不一致の場合は、元の本体も有限失敗する。
単純に全本体を未定義へ写すと、この挙動を失う。任意の環境・実source tblVにおける本体一致を
導き、書換え後の実tblVとの同clock一致を帰納で証明した。任意の開始式について全有限観測・
有限失敗・全clock未定義・元文字列言語を保存する。一階性も保存する。

実例は0→1→2→1の転送集合、保持値を3倍にしてその集合を呼ぶ別規則、未定義calleeへ
転送する規則を一つの文法へ混在させる。短い入力でのfallback成功、コピーが足りる入力での
閉路未定義、空捕捉、引数不一致、保持値なしの環境、preflightを省いた場合の誤った未定義を
kernel検証する。成長規則へ続く非循環転送は、cycleに分類されないことも確認する。

これはPar側の文法正規化であり、上記の正倍率compilerでは有限head展開を介してSeqへ接続する。
独立複数捕捉、および一般Par/Seq一致・分離は引き続き未解決である。
検証は全1118 jobs（Auditを含む）、関連1134定理の標準Lean公理／公理なしの依存検査、
新規40guard（PR66計139guard）。

## 規則ごとに異なる倍率を有限個の保持表現で吸収

`MultiplyingPrefixCompiler` は、各規則が
`F_i(w) := (F_next(w^m_i); B_i(w)) / (w; C_i(w))`
という形で、構文に固定されたm_i≥2を持つ場合を扱う。倍率は規則ごとに異なってよく、
自己/相互再帰の途中で切り替わる。B/Cと開始式は任意の一階式を許す。
n規則の元文法に対し、通常版と各元規則の倍率版を各calleeに作り、ちょうどn(n+1)規則の
固定一階Seq文法を生成する。元文字列・全有限観測・有限失敗・全clock未定義を保存し、
実際の再帰tblVの評価は同じ通常clockで一致する。

倍率mの版は、同じvをm-1個の実引数に保持して、元の保持値w=v^mを表す。
通常版は1引数でw=vを表す。元のprefix引数w^rは、既にwを消費したSeq位置から
r-1個の引数としてwをそれぞれ捕捉することで照合する。子はr版へ入り、渡された
wからw^rを復元できる。再帰の深さや捕捉語の長さに応じて版を増やす必要はない。
各版のarityは通常版1、それ以外は倍率-1である。追加引数は独立した値ではなく同じ
元の語を別の区間で捕捉したものなので、独立複数捕捉の一般問題は解いていない。

`RepeatedWordArguments.sequential` は、任意の語式Aをn個並べた実Seq引数について、
一致判定がvalue(A)^nであり、各実捕捉はvalue(A)になることを証明する。
`MultiplyingPrefixCalls` は元の全引数と分割捕捉の終点を一致させ、
`MultiplyingPrefixCorrespondence.tables_rows` は全版の実tblV対応を同時帰納で閉じる。
最終定理の前提は倍率の有限不等式と一階構文だけで、意味論的行oracle、有限語palette、
alphabet/profile制約は渡さない。未知の元規則とprefix calleeは補助規則へaliasしないよう
失敗へ写す。

kernel直接実行では3倍の1/3/9/27コピー、3倍と2倍が交互の1/3/6/18/36コピー、
親値を各深さで再利用する1/4/10/28コピーを確認する。継続のc*によるfresh捕捉と親ab復帰、
親不一致、補助規則非公開化、未知calleeも検証する。空捕捉は任意の倍率・全入力・全clockで
元が未定義、倍率≥2ならSeqも未定義と証明する。

倍率1はこのcompilerでは扱わない。`F(w) := F(w) / w` は元では再帰が進まず未定義だが、
現在の分割規則をそのまま適用するとarity不一致による有限失敗からfallbackで成功してしまう。
この実反例とValidの拒否を証明している。検証は全1114 jobs（Auditを含む）、
関連1094定理の標準Lean公理／公理なしの依存検査、新規55guard（倍長版と合わせてPR66計99guard）。
保持値転送との混在、コピー以外の語更新、
この形への任意文法の正規化、独立複数捕捉、および一般Par/Seq一致・分離は未解決である。

## 最初の全再照合より前に倍長引数で再帰する場合

`DoublingPrefixCompiler` は、各規則が
`F_i(w) := (F_next(ww); B_i(w)) / (w; C_i(w))`
という形の有限文法を、規則数がちょうど2倍の一階Seq文法へ変換する。
nextは自己再帰・相互再帰・未定義規則を許す。B/Cは任意の一階式であり、選択・否定・
star・任意のPEG実引数を伴う再帰呼出しを含められる。元の開始式も任意の一階式を許す。
calleeの先頭に全保持値の再照合を要求しない。原入力・任意Char列の全有限観測と
全通常clock未定義を保存し、実評価器は同じ通常clockで一致する。

Seqの各規則には通常版と半分保持版を作る。通常版の保持値vは元のw=vを表し、
半分保持版はw=vvを表す。元位置pとSeq位置jの不変量は
`sfx(x,p) = w ++ sfx(x,j)`。元の倍長引数wwの照合は、Seq側ではjからwだけを
照合することで同じ終点へ届く。子はそのwを半分として保持するため、元の子のwwを
失わない。その後のB/Cではviewを代入して元の全値を復元する。B/C内の新しい呼出しは
通常版に入り、実引数全体を新しい値として捕捉する。未知の元規則番号は失敗へ写し、
補助規則への意図しない参照を防ぐ。

`WordViewSubstitution` は語式の代入をPar/Seq両方の実引数評価まで持ち上げる。
`DoublingPrefixEvaluation` の一時的な行対応仮定は、
`DoublingPrefixCorrespondence.tables_rows` が実際の両tblVについてclock帰納で証明する。
最終言語定理に意味論的行oracle、有限語palette、alphabet制約、profile注釈はない。
規則数2nという上界はこの直接compilerのものに限り、一般の文法サイズ上界ではない。

kernel実行でabの1/2/4/8/16コピー、非2冪の残余、2規則の相互再帰と親の全値再利用、
継続中のc*による新しい非空捕捉（長さ1/3/8）と親abへの復帰、短い親の拒否を確認する。
空の倍長捕捉はfallbackへ有限失敗せず、全入力・全通常clockで元/Seqとも未定義である。
補助規則番号の非公開化、未知callee、実引数評価前のarity検査も検証する。

これは最初の再照合が遅延する一つの再帰族を閉じるが、任意Par文法のこの形への正規化、
他の引数更新との一般的な混在、独立複数捕捉を証明していない。
一般の言語クラス一致または分離は引き続き未解決である。

## prefix入口で新しい語を作る実user呼出し

`ChangedWordPrefix` は保持値転送を `R(w ++ V(w))` へ広げる。
Vはliteral／parameter／sequenceで作る語式であり、実際のcalleeは新しい語全体を
捕捉する。親は元のwを保持する。calleeが新しい捕捉全体の再照合から始まる場合、
その本体を `w; V(w); B[w ++ V(w)]` に展開し、既存の停止検査付き反復回転と
固定Seq compilerへ接続する。valueの有限paletteや捕捉語の形の注釈は渡さない。

`WordCallUnfolding` は既存 `WordArguments.word_eval` を再利用する。任意Word引数Aと
任意一階callee本体Bについて、実Par `R(A)` の通常clock k+1は、clock kでの
`&A; B[param0 := A]` と全partial結果が等しい。代入は実引数の内部まで行い、
calleeの範囲外parameterは親のparameterへ漏らさず失敗へ写す。引数の新しい語が
実入力と一致するというpreflightは一般には必要である。

低層の展開は任意のWord引数を扱うが、今回の最終Seq接続はAが親のwから始まる場合に
限る。`WordPrefixInlining` は新語全体の代入・先頭wのfactor・停止条件を証明し、
`ChangedWordPrefix.check` が実calleeのarity/bodyと展開後caller本体の一致、VのWord
構文を有限検査する。既存の構文条件と合わせ、全入力の固定一階Seq元文字列言語、
有限観測・有限失敗・全clock未定義を保存する。通常clockは元k≤先k、先k≤元2kで対応する。

実例のprefix自体が `R(ww)` または `R(wb)` で新しい保持値を作り、RからFへその
新語の2倍を再捕捉して相互再帰する。前者は親2文字→R4文字→子F8文字→R16文字→
子F32文字、後者は親ab→Rのabb→子Fのabbabbとなる。深さ0/1/2の元実行と、
深さ1の生成Seqを両引数形式について通常clock12で直接実行し、短い新語／親復帰の失敗もkernel検証した。
空捕捉の倍長prefixは全入力・全通常clockで元／Seqとも未定義である。

Word条件の外では単純代入は誤る。Aが `a / b`、Bが `param0; param0`、入力がabなら、
元は最初に捕捉したaの2回目が失敗するが、代入先はaのあとbを選び直して成功する。
この反例とcheckerの拒否も検証した。これは代入手法の限界であり、言語クラスの分離ではない。

検証は全1100 jobs（Auditを含む）、関連995定理の標準Lean公理／公理なしの依存検査、
新規42guard。この展開経路では、入力依存の選択・star・user呼出しを含む任意PEG引数、親のwを先頭に
持たない新語の最終Seq接続、先頭再照合のないcallee、独立複数捕捉、および一般の
Par/Seq一致・分離は引き続き未解決である。

## 保持値を転送する消費user prefixを展開して接続

`R(param0)` は実際の一階Par呼出しであり、現在の保持値を元位置から再捕捉して
calleeへ渡す。`ForwardedCallUnfolding` は、calleeの自由parameter参照が0だけという
有限構文条件から、通常clock k+1のその呼出しと、clock kの `&param0; body(R)` の
全partial結果が等しいことを証明する。任意のcaller環境を先頭保持値だけのcallee
環境へ射影できることを、実引数評価も含めて構文帰納で示す。bodyが独立でも、
引数preflightは一般には省けない。

`BoundedBodyRewrite` は、このように呼出し段数を消す規則変換を扱う。
元の通常clock kの実表は先のclock k以下、先のclock kの実表は元のclock 2k以下となる。
同clockの表一致を仮定せず、全有限観測・有限失敗・全clock未定義を保存する。
`ExpressionContext` はsequence／優先選択／否定／starの下へ情報順序の対応を持ち上げ、
途中の位置の妥当性を実物の表のrange不変量から導く。

`ReplayCallInlining` と `FoldedUserPrefix` は、calleeが全保持値の再照合から始まる
場合を、実規則のarity・body一致・parameter範囲を調べる有限検査で扱う。
`R(w) := w; B(w)` を呼ぶ元本体 `(R(w))*; w; tail` は、
`(w; B(w))*; w; tail` へ展開できる。既存の `LeadingReplayStar` の
`(w B)* w = w (B w)* !B` という停止検査付き回転と、再帰continuation compilerへ
接続する。Bは単なるscannerではなく、fresh引数を捕捉する実user再帰・相互再帰と
親の保持値再利用を含められる。calleeがcallerへ戻る呼出しも許し、非再帰性や
意味論的な成功・行oracleを仮定しない。最終Seq文法は固定され、入力文字列を変更しない。

実例ではFの反復中にRへ保持値abを転送し、RからFへ新しいababを渡す。
さらに深さ0/1/2/3で保持値長2/4/8/16を使い、各親へ全保持値を再照合して復帰する。
生成Seqの相互再帰を通常clock12で直接kernel実行し、短い子・親の再照合失敗も確認した。
展開前がclock1で未定義、展開後が同clockで成功する例を持つため、同clock表一致では
このpassを正当化できない。nullableな実user prefixは全入力・全clockで元／Seqとも
未定義であり、非replay callee、不正parameter範囲・同一caller/calleeのfoldを拒否する。

検証: 全1095 jobs（Auditを含む）と、関連953定理の標準公理／公理なしの依存検査。
新規48定理をguardで追加検査した。元・先の通常clockは同一とは限らない。
保持値転送だけという条件は上のWord引数変換で一部解消した。任意PEG引数や
再照合より前に消費する任意callee、および一般Par/Seq一致・分離は未解決である。

## 長さ可変 scanner を保持値の照合付きで反復する入口

`Entry.scannerIterate q` は、実補助 scanner を呼ぶ生の入口
`(scan(q); &param0)*; param0` を扱う。固定 literal prefix の列挙ではなく、
各反復が scanner の読める長さ全体を消費する。捕捉値 `w` を q から読んで
実際に到達する状態を r とすると、捕捉終点での Seq 入口は
`(scan(r); param0)*` になる。scanner が終わる絶対位置は元・先で同じであり、
元の零幅 query と先の全保持値消費が位置対応を次の反復へ保つ。
空捕捉と零消費 step も含む partial-result 対応から、nullable 未定義を保存する。

`GuardedScannerIteration` の位置対応を、実コンパイル済み補助規則に対する
`GuardedScannerFilter`、再帰 plain/product 行の同時帰納、元 header の出力 profile
検査へ接続した。元の反復の消費 profile は H(q) の有限閉包と最終全保持値との積で
覆う。最終的な定理に補助行や再帰行の意味論的 oracle はない。

`ReadableScannerProfiles` は scanner の遷移文字から alphabet を集め、その生成
profile domain を q からの正確な可読性で絞り、H(q) を作る。元の優先遷移で
各 listed arc が実際に有効であることを有限検査し、scanner の再帰出力検査を証明する。
異なる到達先を持つ同文字重複 arc はこの frontend では拒否する。
`ScannerLoopCompiler` は反復する user と、新しい scanner 捕捉を返す getter user
からなる元テンプレートの H/C/A を構成する。入力は実機械・開始状態・tail 構文だけで、
捕捉語の palette や手書き出力集合を渡さない。tail の有限参照／profile 検査から、
全入力の固定一階 Seq 元文字列言語、通常 physical 定義／全 clock 未定義が得られる。
alphabet は scanner の文字だけでよく、tail の文字や入力全体の所属は要求しない。

`ScannerLoopExamples` は q0 が a、q1 が b を読む部分機械を使う。全 k の `a b^k`
が可読であり、親 ab・長さ可変の中間 abbb・子 a・親 ab の復帰を実行する。
単純な反復と親子再帰の生成 Seq 文法を通常 clock12 で直接 kernel 検証する。
捕捉後の tail 失敗を保持し、非可読 capture、不正参照、無効な優先 arc を拒否する。
`ScannerLoopCaptureExamples` は全 k の `a b^k` を実元 user が通常 physical clock で
捕捉することと、捕捉長が非有界なことを証明する。`ScannerLoopUndefined` は alphabet
外の X 上で空捕捉となる実 root が、元・先とも全通常 clock で未定義と証明する。

この入口は無界長の独立 scanner prefix を反復へ追加するものである。
一般の消費する parameterized user prefix、全再照合を伴わない任意依存継続、
独立複数捕捉、および一般 Par/Seq 一致／分離は未解決である。

検証: 全 `lake build` 1088 jobs（Auditを含む）成功。関連905定理の依存公理は
標準Lean公理または公理なしで、新規55定理には `#guard_msgs` による依存検査を追加した。
非可読 capture の検査を外すと、実元のnullable未定義が実先の有限失敗へ変わる反例も検証した。

## 既存の有限prefixと呼出し元制御

固定文字列を消費してから保持値を再照合する入口も、走査・直接再照合と
同じ `RecursiveScannerProductCompiler` へ統合した。`Entry.shift q R` の元入口は
`lit (R q); param0` で、生成先は実捕捉の終点から `lit (R r)` を消費する。
`r` は捕捉全体の有限 profile から決まる実 scanner 到達状態である。
`ScannerReplayResidual.check` は、ラベル付き状態の実遷移がラベル先頭を読み、
その文字を末尾へ回すことを有限検査する。未ラベル状態には別の走査を置ける。
この検査と開始状態での捕捉の可読性から `u ++ w = w ++ v` を導き、
成功・有限失敗を含む入口の全 partial 結果を保存する。`u` と `w` の可換性は要求しない。

残余ラベルの検査を既存の有限 body 検査に含め、plain/product 行の同時帰納、
実元規則の出力 profile 証明、全入力の有限観測・固定 Seq 元文字列言語・
physical 定義／全 clock 未定義の対応まで接続した。成功や row の oracle、
全状態 Total は新しい profile 経路の最終入力にない。`ScannerReplayResidualExamples`
では `ab; param0` と別状態の a/b 走査と直接再照合を同じ文法へ置き、
`(ab; &aba)*; a` の入力依存・語数非有界の捕捉を実 unary 再照合呼出しで取得し、
親 `aba` →走査側 `b` →子 `ababa`、その後の両親の全値再利用を検査する。
`ab ++ aba ≠ aba ++ ab` でも残余 `ba` が正しい。有限注釈と指定入口形式という
制約は残り、任意 PEG prefix や独立複数捕捉、一般の一致／分離は未解決である。

入口は単一 leaf に限定せず、`Entry.alt` と `Entry.guard positive test tail`
による任意有限の入れ子へ拡張した。leaf は直接再照合・scanner・認証済み固定 shift
から選び、guard の test と tail は同じ元位置から評価する。生成先の `targetHeader`
は捕捉終点で同じ全 partial 結果を返し、正／負の query をその場所で評価してから
対応する tail へ進む。優先選択では plain header の正先読みと負ガードで枝を固定し、
本体の失敗や未定義によって別入口へ戻らない。単純な本体の枝配布は使わない。

有限 layout／entry-state 検査は両枝・全 test を再帰的に検査する。実元規則の
header 出力 profile は選択で和、guard で tail の集合となり、query 自体の評価は
残る。この形を既存の plain/product 同時帰納と全入力言語・physical 定義／未定義
へ合成した。`EntryControlScannerExamples` は同じ user で正 shift query→別状態走査と
負 shift query→直接再照合を切り替え、再帰捕捉と親復帰を確認する。`ab!` の
直接再照合／走査の選択では、選択済み replay の本体失敗を保持し、素朴な枝配布だけが
誤受理する差も kernel で確認する。

全ての成功する header の消費終点が実 capture 終点以後になる構成であり、
負 query 単独のように元位置へ空成功で戻る本体は、この入口変換だけでは扱えない。
その場合は以下の呼出し側正規化を使う。
任意 PEG prefix、別 compiler との統合、独立複数 capture、および一般一致／分離は
引き続き未解決である。

`ScannerOriginControl` は、各 unary user の実元本体を、
`sourceHeader entry; sourceExpr body` という有限 leaf の選択・否定・正先読み guard
の任意有限制御木 `Plan` として与える。leaf 本体内と実引数内には同じ user 群の
再帰・相互再帰・任意の Arg の連結／選択／否定／star を許す。
`normalize` は caller の元位置でまず `&normalizedArg` を評価し、制御木の各 leaf を
依存 leaf には同じ実引数、非依存 leaf には空文字列を渡す unary call へ展開する。元 user の引数評価を飛ばさないため、
引数の失敗が否定 leaf の空成功へ変わることはない。

生成した leaf 規則と元 Plan 規則の実行表を、同じ通常 physical 段数で対応させた。
共通補助 scanner の全実行行が両実文法拡張で一致することと、元引数の実再捕捉を
使い、構文帰納と user 段数帰納で対応を導く。`readyCheck` は有限の参照範囲と非依存構文の検査で、
成功／行／捕捉形 oracle を要求しない。正規化後の実 core 文法の有限 profile 検査と
合成して、元実 Plan 文法から固定一階 Seq 文法への全入力 SObs・同じ元文字列言語・
physical 定義／全 clock 未定義を証明した。

`ScannerOriginControlExamples` では、従来の非有界 `(ab;&aba)*;a` を実 unary call で
捕捉し、親 `aba`→scanner 側 `b`→子 `ababa` と両親への復帰を確認する。
別入力 `ababaX` では実引数 `aba` を成功捕捉しても、元本体の負 leaf が
元の位置へ空成功で戻り、後続が同じ全入力を読める。生成 Seq の実通常表にも
その元位置への復帰を導いた。preflight を省くと失敗引数が空成功になる差、
nullable 引数の全入力・全 clock 未定義も kernel で検査した。
負 leaf は scanner と `X` の後に新捕捉値を読み、`ababaXabaZ` なら否定失敗、
短いコピーの `ababaXabZ` なら元位置へ空成功となる両方を生成 Seq へ接続した。
全体本体には capture 終点以後という制約を課さないが、各消費 leaf の入口形式は
指定した replay／scanner／認証済み shift とその制御である。
任意 PEG prefix、独立複数 source 捕捉、一般 Par/Seq 一致／分離は未解決のままである。

さらに `Part.closed` の leaf は header を置かず、元位置で直接 Arg 本体を評価する。
有限の `independent` 検査は、先読み内や実引数内も含めて caller の param 参照を禁じる。
呼び先の本体は新しく捕捉した値を使ってよく、閉じた leaf から同じ user への再帰や
捕捉依存 user への呼出しも許す。任意の実 recursive table と二つの環境での全 partial
評価一致を構文帰納で導き、成功・停止性・行の仮定なしに旧捕捉値を空に置き換える。
生成先ではその leaf に空引数を渡し、replay の空 header を経て元位置で本体を実行する。
元実引数の preflight は残し、失敗や未定義が値消去によって消えないようにする。
この分岐を既存の同 physical 段数の Plan 行帰納へ統合しており、最終の全入力 SObs、
元文字列言語、physical 定義・全 clock 未定義の定理は同じ有限検査から得られる。

`CaptureIndependentOriginExamples` は abc を捕捉して a だけを消費する実行と生成 Seq の
同じ終点を確認する。同じ user の選択では非依存 a 枝と完全再照合枝が混在し、
bbc 上では後者が全捕捉を消費する。同じ文法内の c 再帰から、非有界捕捉・scanner・再照合を使う
既存の親子再帰へ入り、全値復帰と全入力の固定 Seq 言語変換を接続する。
abc 引数が ab 上で失敗すると本体 a は実行されず、nullable 引数は全入力・全 clock で
未定義のままになる。query や実引数に隠した旧 param は有限検査で拒否する。
非依存 leaf には capture 終点以後の制約がなくなったが、旧値を使う消費 leaf の
指定入口形式、unary、共通 machine、成功する有限 profile 注釈は引き続き制約である。

固定 shift の捕捉にも、可読性による事前制限を弱めた。
`ScannerReplayResidual.completeCheck` は、ラベル付き状態がラベル先頭文字の遷移を
実際に持つことを有限検査する。従来の `check` は存在する全 arc の回転だけを検査し、
必要な arc がない場合も通るので、二つの検査を区別する。実入力の捕捉 prefix w と
入口の成功から `w ++ tail = u ++ w ++ rest` が得られ、二つの有限検査により
その w の全体が実 residual machine に可読だと帰納できる。従って非可読なら
実元入口 `lit u; param0` は、任意の文法・実 table・clock で有限失敗する。

profile 経路の `entryCheck M` は shift について、従来の実 profile 可読性または
この機械の完全性を受け入れる。可読時は従来の回転、非可読時は実入口の有限失敗を
導き、既存の失敗を生成する targetHeader/shiftedBody へ接続した。plain/product 行、
選択を確定する header 制御、caller の元位置 Plan、有限 grammar/body/root 検査と
全入力 SObs・固定 Seq 元文字列言語・physical 定義未定義の定理にそのまま合成する。
元の actual 引数評価は残り、未定義が失敗に置き換わることはない。

`UncheckedShiftCaptureExamples` の一つの実引数は `(ab)*;c` と従来の非有界引数を選ぶ。
前者の `abababc` は実 unary call で捕捉に成功するが、ab 残余周期には非可読であり、
旧可読性検査は false、新入口検査は true となる。shift 呼出しは有限失敗し、その負の
query を通る別 user は元位置で a を一文字だけ消費する。後者の枝では既存の
親・子の全捕捉を再利用する再帰が成功する。両方を生成 Seq の物理実行と全入力言語へ
接続し、nullable 実引数は全入力全 clock で未定義を保つ。必要 arc を欠く一状態機械は
旧 sound-label 検査に通っても、実 a 捕捉から a 再照合に成功し得る。この機械を
completeCheck と弱化後の入口検査が拒否する反例も kernel で確認する。
完全な residual machine の shift では捕捉の可読性制約が不要になった。

`PrefixCaptureQuery` は、生の元本体 `lit u; &param0` / `lit u; !param0` も扱う。
`prefix_query` は任意の式 a/b・文法・strategy・実 table・環境について
`a; &b = &(a;b); a` と `a; !b = !(a;b); a` の全 partial 結果一致を証明する。
検査後は同じ元位置で a を決定的に再実行するため、有限失敗・未定義も保存する。
この恒等式自体は一般の prefix に成り立つが、ここで完成した有限 compiler への
合成は固定 literal prefix と旧 capture の query に限る。

有限 `linkCheck` は独立 literal leaf と、同じ literal の shift 入口＋空継続の実 leaf を
構文で結び付ける。異なる literal や非空継続は拒否する。生の正負 query と既存 leaf の
選択・否定・guard を持つ Body を、元位置の query と独立消費を行う Plan へ変換する。
`SemanticBodyRewrite` は同じ呼出し番号と arity を保つ本体の全 partial 書換えから、
実再帰表全体の各 physical 段数での一致を導く。`syntaxCheck` からこの書換えを
実元規則ごとに証明するので、行一致を最終入力にせず、実引数内・本体内の同 user
再帰や相互再帰にも適用する。既存の有限 profile 検査へ合成し、生の元文法から
固定一階 Seq への全入力観測・元文字列言語・physical 定義／全 clock 未定義を得る。

`PrefixCaptureQueryExamples` の実元 rule は `ab; !param0` そのものである。
`(ab)*;c` を含む実 unary 引数が abababc を7文字捕捉した後、旧値を否定照合して
ab の2文字だけを消費する。正の query では実捕捉 ababa の全5文字を必要とし、
abababa 上で2文字だけ消費、ababa 上の短い再照合は失敗する。
同じ正 query user が c を読み、入力依存の `c*;ababa` を新しく捕捉して自身へ再帰する。
cccabababa 上で複数回入れ直して正 query に至り、後続が残りの ababa を消費する。
これらの生成 Seq の実物理結果と、否定 query 後続／同 user 再帰の全入力固定言語を
証明し、nullable 実引数は全入力全 clock で未定義を保つ。
生の固定 prefix query まで到達したが、保持値を使う任意 PEG prefix・独立複数 capture・
一般 Par/Seq 一致／分離は引き続き未解決である。

入力依存の可変長 prefix にも、断片捕捉の既存 compiler を使って接続した。
`FragmentMixedRecursive` へ独立 scanner leaf（tails.length+1）を追加し、
その元本体は `A = a*#` だけを評価する。生成先は元位置で空引数を渡す独立 scanner 行を
追加し、実引数の preflight を先に保つ。純粋な scanner を直に置くと clock 0 でだけ
元 user の未定義とずれるため、実 unary 行を使って全 ordinary physical clock を合わせた。
従来の consuming/replay/stuck leaf と同じ Plan 内で混在できる。旧アドレスは保持する。

`FragmentPrefixQuery` の実元 user Body は `A; &param0` / `A; !param0` そのものである。
有限 `copyCheck` で shift-kind と空継続の実 leaf を結び、共通の predicate-push 恒等式で
その copy を元位置から先読みしてから独立 A を消費する Plan へ変換する。
既存の selected-fragment 引数 `star(step G); H` を ternary/unary target 呼出しへ分ける
変換が、A の終点より後で捕捉が終わる場合も受け持つ。source の捕捉は一つのままで、
target の三つの引数はその捕捉の断片であり、独立複数の source 捕捉ではない。
SemanticBodyRewrite から実元／Plan 文法の各 physical 段数一致を導き、断片 compiler の
対応へ合成して、全入力 SObs・固定一階 Seq 元文字列言語・physical 定義／全 clock 未定義を
有限 Body/link 検査だけから得る。停止や実行行の oracle を入力にしない。

`FragmentPrefixQueryExamples` は長さの異なる a-run を読み、aa#a の全捕捉を確認しても
A の aa# だけで成功する。短い aa# コピーは正 query を拒否し、負 query を通す。
H の正 query は同じ元 user を新しい空捕捉で呼び、その後外側の完全な捕捉へ戻る。
同じ固定開始式が n=1,2,4 の反復語で全入力を消費し、その文法全体に全入力言語変換を
接続する。scanner 単独なら成功する a# 上でも実 aa 引数の失敗を先に保ち、preview を
省いた素朴な呼出しだけが誤成功する。clock 0 の実未定義、nullable H の全入力全 clock
未定義、非空継続や replay-kind を copy として指定した場合の有限拒否も kernel で確認する。

実引数の family を、fragment 引数の任意の有限な優先選択木へ拡張した。
`FragmentMixedRecursive` の3つの表面 template は before / choices / after を表す。
choices の `seq G H` は一つの fragment 引数を指定する葉、`alt` は候補間の優先選択である。
ここでの seq は template の組であり、実引数二つの連結ではない。元の実 call は引き続き
unary で、引数は `&before; (arg1 / arg2 / …); &after` となる。
`ArgumentGuard.choice_call_eq` は任意の実 table・環境で、成功した引数の枝を固定してから
本体へ入る全 partial 恒等式を証明する。本体の失敗／未定義で別の捕捉へ戻らない。
終点検査も選択木全体の後に置き、その失敗を引数候補の失敗と混同しない。
生成 Seq は選ばれた引数を同じ位置・同じ table で再検査し、従来の fragment leaf 変換へ渡す。
相互再帰する renderer・選択木の対応を既存の physical 段数帰納に組み込み、
実 G/H と before/after の内部から同 user を呼ぶ場合も含めて、元の全入力観測・
固定一階 Seq 元文字列言語・全 physical partial 結果を保存する。新しい行 oracle は不要。

`SelectedFragmentArgumentExamples` では aa#aa#a 上で先頭候補が aa#aa を捕捉し、
本体の query が有限失敗する。後の aa#a 候補なら成功するが、正しい変換は選び直さない。
呼出しを選択肢へ素朴に分配した Seq だけが誤成功する。終点検査で同じ誤りが起こる例も
kernel 検証した。先頭引数自身が失敗する a#a#a では後続候補へ進み、aa#aa#aa では
先頭候補のまま成功する。ネストした選択木の H は同じ raw query user を空捕捉で呼ぶ。
固定開始式2つに全入力の言語変換を適用し、nullable な先頭候補は全入力全 clock で
後続候補と有限失敗の終点検査を遮断し、元位置の失敗はその nullable 候補を遮断すると証明した。

別の経路として、`UniversalCaptureProfiles` は完全な固定 shift／直接再照合の
入口制御木に対し、実引数の形と手動 profile 注釈の制約を外した。
`CaptureViews` の全捕捉再構成だけでは本体入口の位置差は解消しないため、ここでは
既存の finite-state 残余機械による入口対応へ直接合成する。各 user の入力／出力候補を
observer の全有限 profile に自動設定する。有限 profile は連結の合成で閉じ、star の候補
計算も同じ有限集合内に留まることを証明した。これにより scanner／user の全 summary
検査、実引数内の全 nested call 検査、全 rule 本体検査を、元の呼出し番号の scope と
入口の構文検査だけから導く。成功する注釈の発見を利用者の仮定にしない。

元 user は unary、入口は replay または完全な回転残余機械を持つ shift と、それらの
有限 alt／正負 guard の制御木である。この入口制約の下で、実引数と本体の継続は
literal・param・user・seq・alt・notP・star の全構文を許す。連結後の捕捉は全体の
有限 transition profile を合成して扱い、引数の部分ごとの有限文字列 palette を要求しない。
任意の個数の連結、入力依存で非有界の反復、同 user／相互再帰と親の全値再利用を
含め、既存の生成固定一階 Seq の全入力 SObs・元文字列言語・定義／全 clock 未定義へ
合成した。補助行が安定した共有 user clock では全 partial 結果が一致するが、
この経路は source と target の生 physical clock が等しいとは主張しない。
一般 scanner 入口は全 profile では安全でないため、新しい自動検査では拒否する。
既存の精密 profile による scanner 変換はそのまま利用できる。

`UniversalCaptureProfileExamples` の元規則は `!(a;param0);param0` の入口に続き、
旧値を二倍にする実引数 `param0;param0` で同じ user へ入り、子から戻って親の値を
もう一度照合する。初期引数は `b*;a` で、a-fragment family 外の実捕捉を使う。
同じ固定開始式の複数入力で、捕捉長と再帰深さを変えた実行を kernel 検証し、
生成 Seq の生実行も直接確認した。一般の全入力言語保存の実例とし、nullable 引数の
全入力全 clock 未定義、および不完全 shift／無条件 scanner の有限拒否も証明する。
これは制限された入口の文法 family 全体に対する注釈不要の変換であり、任意 PEG prefix
や複数の独立 source capture を含む一般 Par→Seq 変換ではない。

`AutomaticOriginControl` は、この自動 profile 生成を元位置制御と生 prefix query へ合成する。
元の Plan／raw Body の有限構文検査だけから、正規化で生成する各実引数と core 本体の
scope、各 core 入口の完全 shift／replay 条件、および全有限 profile 検査を証明する。
閉じた leaf は旧 capture を空に置き換えて元位置で実行できるので、消費しない負 query や
capture より短く消費して終わる本体も含め、任意の実 Arg と同居させられる。
`prefixCheck` は元の `linkCheck`／independent／scope と入口の完全性だけを検査する。
利用者は生成 core 文法の検査成功や、入力／出力 profile 集合を別に与える必要がない。
既存の body 書換え・caller 正規化・helper 安定化を順に合成し、元の生文法から固定 Seq の
全入力観測・元文字列言語・定義／全 clock 未定義を得る。

`AutomaticOriginControlExamples` の実元規則は `a;!param0` と `a;&param0` である。
実引数 `a;b*;a` が abba の全4文字を捕捉しても、負 query は a の1文字だけを消費する。
正 query は aaa の全コピーを必要とし、aaaa なら1文字消費、aaa なら有限失敗する。
同じ元文法では負 query を guard に使い、保持値の二倍を同じ user へ再捕捉して、
子から戻ると親の全値を再利用する。入力依存の捕捉長と再帰深さを変えた source 成功・
生成 Seq 成功、および早期 query の生 target 実行を kernel で検証した。
固定開始式2つの全入力言語変換、実引数失敗の優先、nullable 引数の全入力全 clock
未定義、旧値を参照する閉じた leaf と無条件 scanner 入口の有限拒否も証明する。
これは元位置に戻る本体と任意実 Arg の接続であり、prefix 自体は認証済み固定 literal に
限られる。一般の PEG 本体 prefix や独立複数 source capture の変換はまだ未解決である。

`FinitePrefixControl` は、prefix を一つの固定 literal から、有限消費の制御式へ広げる。
消費葉は literal、保持値への正負 query と seq／優先 alt／notP は任意有限の深さに入れ子に
できる。prefix の途中の旧値 query が枝を変えるため、成功する消費語や長さは旧値に依存してよい。
CPS 変換は、既に消費した語を静的な word offset として持ち、各 query をその語に対応する
shift/replay leaf で元位置から検査する。選択の test は継続前の prefix だけを評価し、
一度成功した枝を後の query／継続の失敗や未定義で選び直さない。

成功した prefix の消費語が有限の構文由来候補に入り、連結ではその語を正確に連結することを
証明した。この制約は prefix の消費に掛かり、実引数の捕捉長／語彙には掛からない。
有限 `checkAt` は、使用する各 word offset の独立 read leaf と shift/replay copy leaf を
実構文で検査する。続いて既存の元位置変換と自動 profile 検査へ合成する。
任意 table・環境・strategy で CPS の全 partial 対応を証明し、実元規則を書き換えて
全入力 SObs・固定一階 Seq 元文字列言語・定義／全 clock 未定義へ接続した。
source の unary 呼出しの実 Arg は引き続き任意の連結・反復・query・user 呼出しの入れ子を許す。
この単体 frontend の raw prefix 本体には消費する user 呼出しがない。
非有界の再帰継続を CPS の終端へ置く場合は、後述の `RecursiveFinitePrefix` を使う。

`FinitePrefixControlExamples` の実元規則は `(aa / a); &param0` そのものである。
aaa から aa を捕捉すると、aa の選択後に全コピー query が失敗する。正しい生成先も拒否し、
query を枝へ素朴に分配した本体だけが a へ戻って誤成功する。別の prefix
`a; !param0; a / a` は、同じ aaa 入力でも旧値 aa なら1文字、旧値 aaa なら2文字を
成功消費する。旧値依存の prefix 長を実 source／target で kernel 検証した。
消費 prefix を含む notP、実引数内から同じ user への空捕捉 query、外側の全 aa 捕捉への
復帰、入力依存の `a;b*;a` 捕捉、元位置の空成功、nullable 引数の全入力全 clock 未定義、
欠けた offset link の拒否も確認し、固定開始式2つに全入力言語変換を適用した。

この経路は固定 literal 一個への制限を外したが、prefix の消費は構文から有限に列挙できる
必要がある。prefix の consuming star／非有界の user 呼出し、一般の PEG prefix、
独立複数 source capture、および一般 Par/Seq 一致／分離はまだ未解決である。

`RecursiveFinitePrefix` は有限 prefix の CPS 終端を実際の再帰継続へ接続した。
元 Body は prefix でそのまま終える `finish` と、`prefix; param0; tail` として
全保持値を再照合して任意の Arg 継続へ入る `resume` を持ち、同じ文法に混在できる。
`resumeCheck` は各成功消費語に対応する実 shift/replay leaf の本体がその tail と
構文的に同じことを有限検査する。Arg の構文等値は kernel で計算する。
単なる「継続結果が一致する」という仮定を最終入力にせず、任意 table／環境／strategy の
実 leaf 評価を prefix 終点からの全値再照合と継続評価へ合わせる。
先の CPS 対応をこの終端へ具体化し、元規則の実本体書換え・元位置正規化・自動 profile
から、再帰規則群全体の全入力観測・固定一階 Seq 元文字列言語・定義／全 clock 未定義を得る。
tail は旧値参照、任意の Arg 連結・選択・否定・反復、同 user／相互再帰を許す。

`RecursiveFinitePrefixExamples` の raw source 規則本体は、`a;&param0;a/a` の prefix の後に
全 param0 を読み、子へ `param0;param0` の二倍捕捉で同じ user を呼ぶ。子から戻ると
`?` と親の元の全値を照合する。実初期引数も入力の a-run から末尾2文字を残して捕捉するため、
初期捕捉長・各子の捕捉長・実際の再帰深さが同じ固定文法で入力依存となる。
初期長1/2/4と深さ0/1/2の source 実行、生成 Seq 成功、深さ1の生 Seq 実行を
kernel 検証した。子のコピー不足や親の復元コピー不足は全消費にならない。
再照合失敗だけでなく tail だけが失敗する例でも prefix を選び直さず、素朴分配だけが
誤成功する。prefix と再照合成功後の nullable tail は固定入力の全 clock で未定義を保存する。
早期終了する負 query user も同じ実元文法に残し、2つの固定開始式の全入力言語変換、
nullable 実引数の全入力全 clock 未定義、異なる tail／欠けた継続 link の拒否も証明した。

これにより新しい有限 prefix の後に非有界の再帰継続を置ける。prefix 自体で消費する star／
非有界 user 呼出しはまだ扱わず、tail への入口には全保持値の再照合を要求する。
任意の PEG prefix と独立複数 source capture、および一般 Par/Seq 一致／分離は未解決である。

`CaptureOriginRewrite` は、本体書換えの正しさを「実際の Par 呼出しが作れる環境」に
制限しても、文法全体の各 physical 段数の評価一致へ持ち上げる。実引数の成功から、
各捕捉値が同じ呼出し元入力の prefix であることを導き、その行だけを対応させる。
任意の架空の環境の行一致や全 table の一致は要求しない。元 first-order 文法の実 table の
soundness から捕捉条件を導くため、到達可能な行の oracle を新たに仮定しない。

この不変条件を使い、`GuardedReplayIteration` は非有界の query 付き prefix へ進む。
任意の語方程式 `u ++ w = w ++ v` の下で、実保持値 w が元位置に照合できれば
`(u; &param0)*; param0` を、捕捉終点での `v*` へ移せると全 partial 結果で証明した。
空の反復は両側で未定義のままである。u が一文字 c の場合、実捕捉 prefix と最初の
`c;param0` の成功だけから w が c の反復語であることを導き、v=c を得る。
最初の照合が失敗すれば prefix の反復は0回で止まり、元位置から全 w を再照合する。

`GuardedReplayCompiler` の raw source 本体は `(c;&param0)*;param0;tail` であり、
prefix 自体の反復回数に構文由来の上限はない。正規化は最初の `c;param0` を先に検査し、
成功枝は実 fixed-shift leaf の後で c を貪欲反復して tail へ、失敗枝は直接再照合 leaf の
後で tail へ進む。この分岐も tail の失敗で選び直さない。有限の実 leaf／tail 構文検査から
capture-origin 本体書換えを導き、既存の元位置制御・自動 profile compiler へ接続した。
旧有限 prefix／早期 query／実再帰継続の body family と同じ文法で混在でき、固定一階 Seq の
全入力観測・元文字列言語・定義／全 clock 未定義まで証明する。

`GuardedReplayExamples` では prefix 反復回数1/2/4と再帰深さ0/1/2を独立に変える。
同じ user の子は全保持値を二倍に再捕捉し、終了後に親の元の値を再利用する。
生成 Seq の生実行も直接 kernel 検証した。`a;b*;a` の非 unary 捕捉では最初の query が
失敗し、0反復＋全値再照合を保つ。固定開始式2つの全入力言語変換、nullable 実引数の
全入力全 clock 未定義、成功した反復／再照合後の nullable tail の全 clock 未定義、
不正 tail link の拒否も証明した。generic な残余補題は ab/aba の非可換例で v=ba を使い、
元の ab をそのまま再開すると誤ることと、空 step の全入力での未定義を確認する。
この例単独は補題の検証であり、`GuardedReplayCompiler` 自体の反復 step は一文字 c である。
次の共通 compiler の入口拡張で、複数文字の step を実文法変換へ接続する。

架空の保持値 b を aba の元位置に与えると、元反復本体は ab だけ消費する一方、
無条件に正規化すると最後の a も消費する。これは同じ元位置から b を捕捉できない行であり、
捕捉不変条件を外した body 書換えが実際に誤る反例として kernel 検証した。
この証明を任意 table の全環境一致と取り違えない。

この一文字 frontend に続き、`RecursiveScannerProductCompiler.Entry.iterate q R` は
`(lit u; &param0)*; param0` を直接の source header として扱う。u は開始状態の
固定ラベルであり、一文字には制限しない。有限 `headerCheck` は residual machine の
sound-label 検査、開始ラベルの存在、完全性を検査する。成功する捕捉の可読性や形を
注釈として要求せず、実際の捕捉全体の profile が到達状態を決める。

捕捉 w が読めるなら、実残余ラベル v と `u ++ w = w ++ v` を導き、捕捉終点で
`lit v` を貪欲反復する。読めないなら、実捕捉 prefix と完全性から最初の `u;param0` が
有限失敗すると導き、元 header の0反復＋全 w 再照合を、捕捉終点の空消費へ移す。
可読性の失敗を header 全体の失敗に置き換えない。`iteration_header` は任意の文法・
strategy・table 間で、この対応を全 partial 結果について証明する。従来の汎用回転補題は
import cycle を避ける低層 `GuardedReplayRotation` へ移し、名前空間と既存 API を保った。

plain 行に加え、反復残余を読む実 inline filter と継続の product 行も接続した。
`ControlFilter.seq_transfer` は異なる実文法・table 間の連結 filter 対応を合成する。
反復 header の出力集合は全有限 profile の保守的な集合とし、実元規則の成功からの
出力包含を証明した。自動 profile 検査、同じ user-clock の全 partial 対応、元位置 Plan
正規化、固定一階 Seq 文法の全入力観測・元文字列言語・physical 定義／全 clock 未定義
へ既存の定理を接続する。Arg 継続・実引数の seq/alt/not/star と実 user 再帰を制限しない。
入口は有限 alt／正負 guard にも入れ子にできる。

`RotatedGuardedReplayExamples` は二状態の ab 周期機械と、同じ user を再帰的に呼ぶ
実元規則を使う。親の捕捉 aba の残余は ba、子の abab と次の ababab の残余は ab であり、
子から戻ると親の全値を再利用する。反復回数1/2/4と深さ0/1/2を独立に変えた source 成功と
生成 Seq の成功、および通常 clock8での Seq 実行を kernel 検証した。別の root は
非有界 `a;b*;a` を実捕捉し、周期に非可読な値の0反復を保つ。再帰 user 全体を別 user の
実引数にする root は新しい product 行を実際に通る。2つの固定開始式の全入力言語変換、
継続失敗時の反復確定、親コピー不足での未消費残り、空捕捉成功、nullable 実引数の
全入力全 clock 未定義、反復成功後の nullable 継続の全 clock 未定義、必要 arc 不足と
空 step の有限拒否も検証する。

固定語一つの反復から、`GuardedReplayControl` は捕捉を保つ step の PEG 制御全体へ広げる。
原子は `lit u; &param0` であり、seq／優先 alt／notP／star を任意有限の深さに入れ子にできる。
原子ごとに同じ共通 machine 内の開始状態と完全回転ラベルを有限検査する。各反復で違う語を
選べる。`Entry.aligned c` の生 source header は、この制御 c の後に全 param0 を再照合する。

核心の `Aligned x w p q` は、実入力に対して `sfx x p = w ++ sfx x q` であることと
両位置の有効性を記録する。`atom_results` は原子の成功後にも同じ保持値 w が新しい元位置で
照合できると導く。非可読な原子は有限失敗へ移し、可読な原子は実捕捉 profile が選んだ残余
literal へ移す。`Results` は成功位置の対応だけでなく None と有限失敗を区別する。
この関係は連結・優先選択・否定で保存され、`star_results` は元の残り入力長による強い帰納で
greedy star へ持ち上げる。`p = w.length + q` により、元と残余側の進捗／空成功が一致し、
nullable step の未定義も保存する。反復回数の有限上限や成功する trace を仮定しない。

`control_results` は構文全体についてこの関係を導き、`header_eq` は最後の全保持値照合を
外して、捕捉終点からの残余 PEG 制御と全 partial 結果を一致させる。任意の文法・table・
strategy 間で成立する。新しい controlArg と独立 inline filter の構文一致を証明し、
plain/product 行、実再帰継続、自動 profile、元位置正規化、固定一階 Seq の全入力観測・
元文字列言語・physical 定義／全 clock 未定義へ接続した。成功行や捕捉形の oracle は追加しない。

`GuardedReplayControlExamples` の同 user 再帰では、長い abab step と否定 guard 付きの
短い ab step を各回で選ぶ。捕捉 aba の残余は baba／ba、子の abab では abab／ab となり、
親の全値へ戻る。ab 単位1/2/3/5と深さ0/1/2、生成 Seq clock8の直接実行、再帰 user 全体を
別 user の実引数にした product 行の直接実行を kernel 検証した。長い literal が成功しても
直後の保持値 query が失敗したら短い原子を試す必要があり、`(abab/ab);&param0` とまとめる
素朴な変換は ababa 上で残り2文字を生じる。正しい guarded alt は全消費する。
入れ子 `((long*) ; short)*` では内側の貪欲反復の後の失敗を短い反復へ戻さないこと、
非周期の非有界実捕捉、nullable 実引数の全入力全 clock 未定義、否定原子の空成功を反復する
制御自身の全 clock 未定義、成功 header 後の nullable 継続、入れ子の不正原子の有限拒否も検証する。
四状態の別文法は ab／ac という異なる周期を同じ実反復内で混在させ、その source 実行・
生成 Seq 成功の存在・固定開始式の全入力言語変換を証明する。この大きい生成表の直接実行は
行わず、直接 Seq 実行の検査は二状態の実再帰／product 文法で行っている。

`FiniteProfileClosure` は、既存の反復用 profile 閉包について、生成元が全て正しい有限 profile
なら `profiles.length` 回以内に必ず閉じると証明した。各回が未閉包なら重複除去した集合が
真に増え、有限全 profile 集合の長さを超えるためである。従来の conservative fallback は
この場合には使われない。任意の閉じた部分集合への包含も導き、反復で情報が失われないようにする。

`AlphabetCaptureProfiles` は、指定した有限アルファベット Σ の一文字 profile から、この閉包で
domain を自動構成する。Σ 上の全語の profile が入り、domain の各要素も実際の Σ 語で
実現される。これは有限の保持値 palette ではなく、長さ非有界の全 Σ 語の有限な観測である。
有限 source 検査は M の arc・実 header・body・root の literal の文字が Σ に含まれること、
参照範囲・header layout、および domain の各 profile での入口条件を確認する。H/C/A の成功する
注釈をユーザーが選ぶ必要はない。入力文字列全体が Σ 語であることは要求せず、最終定理は全 x を量化する。

再帰 summary は入力 profile が domain 内なら domain、外なら全 profile とする。
そのため、実際に source から捕捉できる値だけに domain を適用しつつ、元の grammarCheck が
検査する全 profile 行についても sound な summary を維持する。`iterate`／`aligned` の
headerEffects は、旧全 profile 集合から、実 source control の消費効果と全保持値 profile の
積へ精密化した。`rawControlArg` は guarded control を通常の Arg で表し、call-free 評価一致と
実成功の output_shape からこの集合への包含を導く。これにより、反復・再帰・保持値の合成でも
Σ domain が保たれる。既存の全入力観測・固定一階 Seq 元文字列言語・定義／全 clock 未定義へ接続した。

この自動経路は無条件 scanner 入口も一律には拒否しない。実 source alphabet から生成した
全 profile がその状態で読めれば、既存 scanner 再開の条件を導出できる。
`AlphabetCaptureProfileExamples` は a/b を読む状態0と、先頭 a の成否を記憶する状態1/2を
同じ M に持つ。source 全検査を通し、全256 profile のうち生成 domain は3個となる。
旧 Universal frontend はこの scanner 入口を拒否する一方、新経路は実再帰引数を認証する。
同じ user の保持値二倍の再捕捉と親全値への復帰で長さ1/4/10の値を作り、その後の scanner
消費を1/2/4文字で変えた source 実行・生成 Seq 成功、および通常 clock12の Seq 直接実行を
kernel 検証した。nullable 引数の全入力全 clock 未定義、欠けた alphabet、未知文字を含む
実引数構文、不正 literal 観測ラベルの有限拒否も検証する。生成 target の行キーは従来の全
profile 列挙のままであり、ここで target のサイズ削減は主張しない。

`LiteralPrefixObservation` は回転ラベルとは別に、固定 literal の未照合 suffix をラベルに持つ。
空ラベルになった状態は、その literal が捕捉内で既に読み終わったことを記憶し、Σ の残りの文字を
吸収する。有限 label 検査と実 capture path から、literal が捕捉内で完了した場合、捕捉後に
残余 literal を必要とする場合、および有限失敗を区別する。`peek_transfer` は、保持値 w が
実元位置で照合できれば、元位置の `&lit u` を捕捉終点の実残余 query へ移す。
追加の alphabet-loop 検査により、実 profile が生成 domain に入ることから w が Σ 語だと導き、
`argument_domain`／`actual_literal_probe` は source の実再帰引数評価からこの条件を供給する。
新たな成功行や保持値形 oracle は使わない。

前回衝突した aab／bba は、追加した観測状態では異なる profile になる。
aabz／bbaz の捕捉後の残余入力が同じ z でも、元位置での literal a の成功／失敗を正しく
終点へ移す具体例と、任意の実再帰引数成功からの一般 probe 定理を kernel で確認した。
`GuardedReplayControl.literalQuery` は、この観測を seq/alt/not/star の原子へ組み込み、
`replayQuery` は空消費の保持値 query を表す。実 capture profile ごとの frontier 検査を
入口検査へ接続したため、観測に使う alphabet state から読めることだけを要求できる。
旧 universal frontend は alphabet 依存の原子を保守的に拒否し、alphabet-derived frontend は
生成 domain の有限検査から受理する。内部で完了する literal、空 capture、非周期 capture、
Total ではない configured frontier、および nullable query 反復を kernel 検証した。

`GuardedFinitePrefix` は、生の有限 capture 依存 prefix `e` を消費する原子
`raw e; &param0` を、これらの原子からなる制御へ CPS 正規化する。
`e` は literal、保持値の肯定／否定 query、seq、優先選択、not を任意に入れ子にできる。
有限の read/finish 検査が、必要な literal query と guarded shift の元文字列を検査し、
alphabet backend がそれらの metadata 証明書と実捕捉 frontier を検査する。
選択した出力語を消費する継続は prefix 成功後に commit し、継続の失敗／未定義を理由に
prefix の別枝へ戻らない。空出力語は `replayQuery` へ送り、nullable 反復の未定義も保存する。
`compile_eval` は任意 grammar/table/environment 下の partial 結果を示す。
`normalize_eval` はこの等式を原子の外側の seq/alt/not/star 全体へ持ち上げるので、
有限 prefix 自体の消費を含む原子を非有界回数反復できる。

source の実 rule 本体を書き換える `SemanticBodyRewrite.Related` から全 physical clock の
同値を導き、実 recursive plain/product backend、全入力観測、固定一階 Seq 文法による
元文字列言語、定義性、全 clock 未定義へ接続する。外側の入力を Σ 語へ制限しない。
一般定理は任意の有限 prefix 構文と有限 metadata 検査に対するもので、例の unary Σ に
限定しない。

`FinitePrefixMachines` と `AutomaticFinitePrefix` は、この有限 metadata の手動割当てを除く。
`support` は成功出力だけでなく、選択の失敗枝や not の内部、連結で可能な全 literal offset を
構文から集める。その語の suffix を literal 観測状態へ、循環回転を shift 観測状態へ変換し、
重複を除いた有限状態列から machine・read・finish を生成する。空 literal 状態は完成済み
literal の記憶と alphabet frontier を兼ねる。全長回転が元の語へ戻ること、suffix／回転の
遷移先が生成集合内にあること、および各有限 label／完全性／alphabet 検査の成功を証明した。

注釈なし `Control` は有限 prefix 原子、retain、seq/alt/not/star を持ち、source の実 rule は
`rawControl` から直接記述する。`certificates` は、生成した metadata と各生成 capture profile の
frontier を一般定理から導く。さらに alphabet も prefix、実 recursive body、root の literal から
自動収集する。`automatic_check`／`automatic_language_translation` の仮定は source の user 参照が
範囲内にあるという実行可能な構文検査だけであり、機械、状態番号、残余ラベル、成功行、保持値形の
注釈を受け取らない。元文字列全入力の固定 Seq 言語と、既存の観測／定義性／全 clock 未定義へ接続する。
生成 target は従来の全 profile 行キーを使うので、サイズ縮小や実用的な変換コストは主張しない。
`AutomaticFinitePrefixExamples` は手書き metadata なしで、3状態 unary と5状態 binary の観測器を
生成し、実再帰捕捉・親復帰の source 実行から固定 Seq 全入力言語へ接続する。unary では生成 Seq を
clock8／実 product 行 clock3で直接 kernel 実行し、空捕捉と全 clock nullable 未定義も検証する。
binary では ab／aba の非可換残余 ba、長い捕捉内で完成した literal の EOF query、Total ではない
configured frontier を検証する。否定内部の probe や選択後の全連結 offset の収集、範囲外 user と
不完全 alphabet の拒否も有限検査する。

`AlphabetOriginControl` は、caller-origin の Plan 正規化を alphabet-derived backend へ接続する。
`normalize_literal` は実引数の preflight、閉 leaf へ渡す空捕捉、選択／否定／guard を通して
source literal 条件が保存されることを示す。各 leaf の header と実生成 profile frontier の有限検査から
`coreEntries`／`coreBodies` の検査を導き、元の実 Plan 文法の全入力観測・固定 Seq 元文字列言語・
定義性／全 clock 未定義へつなぐ。旧 universal frontend が拒否する literalQuery 原子を含められる。

`AutomaticFiniteOrigin` は、注釈なし有限prefix control と recursive Arg 本体を持つ dependent leaf、
または保持値から独立した closed leaf を、Plan の選択／否定／guard で組む実 source 文法を定義する。
source rule の leaf は `rawControl; param0; body` または closed body そのものなので、
whole user 本体は捕捉終点以後に終わる形へ限定しない。機械／read／finish／alphabet を構文から生成し、
生の leaf の全 partial 評価を任意環境／table 下で正規化して全 physical clock の rule-body 同値へ上げる。
その後の caller-origin 正規化と alphabet backend へ合成する。
`automatic_language_translation` の仮定は、Plan／user 参照範囲と closed leaf の構造的 capture 独立性、
root の参照範囲という実行可能な source 検査だけである。新しい成功行／capture 形の注釈は要求しない。
否定は捕捉前の元位置へ、独立 leaf は捕捉終点より前の消費終点へ返ることができる。ただし dependent
leaf 内の消費原子は依然として retained query を伴い、その header は全保持値を再照合する。
任意の全再照合なし依存継続を扱えたという主張ではない。
`AutomaticFiniteOriginExamples` は実再帰で捕捉長1／4／10と親復帰を検証し、loop leaf の失敗を
否定すると、alphabet 外の X を含む入力で whole user が元位置へ空成功で戻る例を示す。
独立 leaf が捕捉4文字に対して1文字だけ消費する場合は、生成 Seq を通常 clock8で直接検証する。
単純な loop／原点復帰は通常 clock2で実行し、独立 leaf の user 呼出しを実引数とする product ケースは
行対応から同じ生成 Seq の通常 clock 実行の存在を導く。全 profile 文法を kernel で直接展開する大きい
product 実行検査は、この環境のメモリ消費が大きいため完了していない。nullable loop の否定／代替枝も
全 clock で未定義のままで、初期引数の有限失敗は空成功へ変わらない。引数 preflight を省くと誤受理する
対照と、closed 依存／範囲外 Plan の拒否も kernel 検証した。



これは各消費原子の後にも全旧値が照合できる guarded step の PEG 制御である。
任意 PEG prefix、捕捉の照合を保たない一般の依存 step／消費 user 呼出し、全保持値の再照合を
伴わない一般の依存継続、独立複数 source capture、および一般 Par/Seq 一致／分離は
引き続き未解決である。

断片経路は固定 literal に限らず、入力依存で非有界の区切り scanner prefix を扱う。
この経路の実引数は G/H で選択する codeword＋a-fragment family とその有限優先選択閉包に限定し、prefix も A に限定する。
自動 profile 経路は実引数の形を制限せず、対応する入口 family を完全固定 shift／replay／
捕捉の照合を保つ guarded step の PEG 制御とその有限入口制御木に限定する。
有限状態 scanner compiler との任意混在、任意 PEG prefix／実引数、独立複数捕捉、および
一般 Par/Seq 一致・分離は依然未解決である。


任意の捕捉依存 PEG prefix、独立複数捕捉、一般 Par/Seq 一致・分離は未解決である。



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


### Physical-prefix row correspondence and observer handoff

`CapturePrefixRows` strengthens the row invariant used by the heterogeneous
recursive compiler. For every physical decomposition `sfx x p = w ++ sfx x j`,
the source unary row at `p`, supplied with `w`, equals its profile-specialized
Seq row at `j`. The prefix need not arise from the user's configured argument
at the same approximation stage, or from that argument at any stage. Both
finite failure and undefined evaluation remain part of this equality.

The proof derives replay rotation from a literal witness in an empty grammar;
no soundness condition is imposed on the two replay tables. It then inducts
on seeded user rounds with the stronger physical-prefix invariant. The old
same-stage argument condition follows from this invariant using actual capture
soundness, so the evaluator step applies without assuming that condition as a
separate row oracle. `rows_of_capture` permits the witnessing capture to come
from any sound first-order CBV grammar and table, at an unrelated stage.

For any finite observer `D`, `filtered_rows` factors an observed source row
through the captured word: the tail starts at `run D q w`, rather than `q`.
`filtered_rows_profile` obtains that state from the finite incoming profile.
This is an identity for the real recursive rows and all partial results; it
is not yet a generator for filtered user rows. The proof uses physical suffix
soundness of successful target row queries to compose the consumed prefixes.

The kernel example configures the user's argument as `Z`, which fails on
`ababa#aba`, but supplies the physical prefix `aba` directly to its unary row.
The source row succeeds, and the target row's success follows from the general
row theorem. A two-state b-parity observer distinguishes the full three b's
from the two b's in the tail, detecting an incorrect unshifted observer state.

This removes the same-stage capture premise needed for the next recursive
argument construction. Parameter-bearing user calls inside arguments still
require generated product user rows and a simultaneous argument/body proof.
Multiple independent arguments, arbitrary body entry, original-grammar
normalization, and general Par/Seq equality or separation remain unresolved.

Validation: full `lake build` passed (847 jobs), including Audit. All thirteen
new public axiom guards use only standard Lean axioms. The new module has no
proof placeholders or Lean warnings.


### Explicit recursive users inside dependent arguments

`RecursiveArgumentCompiler` replaces the fixed argument chosen per callee by
an explicit, structurally nested argument at every call site. Its syntax has
literals, retained parameters, independent recursive helpers, unary user calls,
sequence, prioritized choice, negation, and arbitrary nested stars. The same
syntax describes both user bodies and arguments; user calls inside arguments
can therefore invoke mutually recursive parameter-bearing users, whose bodies
can call further users with different arguments. Rendering is structural and
does not recursively expand a callee's configured argument at compile time.

Each user still has a nonempty fixed literal shift and the source row entry
`(shift_i param(0)) body_i`. The joint phase machine supplies complete finite
profiles. The compiler generates ordinary target rows and product target rows,
indexed by callee, incoming profile, and either plain mode or observer start/end
states. A product row reads the same rotated prefix as the plain row, then
filters the body from the state obtained by processing both the captured word
and that rotated prefix. Its argument is the actual translated argument, so
Seq's argument evaluation captures and consumes it once; no retained value is
passed through a helper call merely to run a filter.

`ProfileControl` implements profile selection over any actual plain expression
and its actual product expressions. Its one-step correctness premise is local
and is discharged structurally in the recursive compiler. Undefined arguments
stay undefined, and a later continuation failure cannot select a different
capture/profile. `ControlFilter` supplies the compositional sequence law.

`RecursiveArgumentCorrespondence.evaluator_of_rows` proves plain and filtered
evaluation together by structural induction, allowing recursive user calls
inside the arguments themselves. `tables_rows` discharges its row premise by
induction over seeded user rounds, simultaneously for every physical incoming
prefix and every valid product state pair. Both modes have the same leading
rotated prefix; therefore the existing physically justified prefix-failure
seed preserves their zero-stage relation. The argument-stage and body-stage
inductions are separate, resolving the mismatch that motivated the stronger
physical-prefix invariant. No semantic row or argument-filter oracle remains
in the final evaluator, observation, or language theorems.

`observations_iff` removes the seeds and relates actual finite observations of
the two fixed first-order grammars on every unchanged original input string.
`language_translation` provides the corresponding fixed Seq grammar. Complete
partial-result correspondence also preserves undefinedness.

The kernel example uses different shifts `a` and `aa`. A recursive user under
argument repetition captures the parent's six a's; a later call under star
uses that retained value to capture fourteen a's for a recursive child. The
child copies all fourteen after its delimiter, and the parent copies its own
six after return. Substituting a six-character child copy or a two-character
parent copy fails in the actual source grammar. Generated Seq observations
follow from the unbounded compiler theorem, rather than bounded evaluation of
the large profile/product grammar. An empty argument iteration is proved
undefined in every seeded target round.

Remaining scope: multiple independent general arguments, arbitrary source
body entry, and normalization of arbitrary original first-order grammars into
the shifted unary form. The new syntax uses literals and the listed controls;
ordinary character atoms and other original syntax have not been normalized
into it. General Par/Seq equality or separation remains unresolved.

Validation: full `lake build` passed (852 jobs), including Audit. All
thirty-eight new public axiom guards use only standard Lean axioms. The five
new modules have no proof placeholders or Lean warnings.


### Capture-dependent origin control with recursive arguments

`OriginControlNormalization` allows source unary bodies to be finite trees of
prioritized choice, negation, and positive guards over shifted-replay leaves.
A source rule need not start with replay and can return before its argument's
endpoint. Leaf tails and call-site arguments retain the recursive argument
syntax, including capture-dependent user recursion and nested stars.

The syntactic normalization expands a control call into its caller-side tree
of leaf calls, preceded by lookahead of the normalized argument. The lookahead
preserves argument failure and undefinedness before negation can inspect a
branch. Every leaf re-evaluates the same deterministic argument at the same
origin and stage, supplying the same word; later branch failure cannot select
a different capture. This does not assume the original source is a normalized
core grammar.

Par-to-Par normalization is proved at every ordinary physical table round for
the entire recursive family. The row invariant relates a source control-user
row to the tree of actual normalized leaf-row queries. All leaves are unknown
at zero; the plan's all-unknown law handles negation. At successor rounds the
shared prefix and structural evaluator induction relate the recursive tails.
The row premise is discharged by induction, while independent helper tables
are transported between actual installed grammars. `normalized_observations_iff`
then composes with the recursive argument compiler to prove actual finite
observations and fixed Seq language translation on unchanged original strings.
No semantic row/filter oracle or source-replacement assumption remains.

The kernel example combines parent-six / child-fourteen / parent-six capture
reuse with guarded choice and negative fallback. Short copies fail under a
final delimiter. After a failed recursive branch, another caller returns after
one character although its argument captured six, demonstrating restoration of
the origin. Generated Seq observations, including that earlier endpoint,
follow from the unbounded theorem. A kernel counterexample shows that dropping
the argument lookahead turns a failed `Z` argument into success via negation.
Empty argument iteration is unknown in every source physical round, and the
generated Seq grammar has no finite success or failure observation for it.

Remaining scope: arbitrary consuming sequences/stars at body entry are not
yet reduced to origin control trees. Every consuming leaf still starts with a
nonempty fixed shifted replay. Capture-independent consuming leaves, multiple
independent general arguments, atom normalization, and arbitrary original
grammar normalization remain open. General Par/Seq equality or separation is
not established.

Validation: full `lake build` passed (854 jobs), including Audit. All
twenty-eight new public axiom guards use only standard Lean axioms or no
axioms. The two added modules have no proof placeholders or Lean warnings.


### Empty replay shifts and capture-independent consuming branches

The recursive argument compiler now permits an empty fixed replay shift.
For `u = []`, the source replays the actual captured word and the target tail
starts immediately at its endpoint, with an empty literal prefix. No
periodicity test is appropriate in this case. `UsersValid` consequently
requires only valid body syntax. The complete simultaneous plain/product row
proof, finite observations, and fixed-grammar language translation apply to
these users together with users having nonempty shifts.

`OriginControlNormalization.Leaf` now explicitly distinguishes replay leaves
(`some u`, including `some []`) from capture-independent leaves (`none`). A
closed leaf body may consume literals, sequence, choice, star, independent
helpers, or invoke recursive users that capture and use their own arguments.
It cannot refer to the incoming argument value at its own lexical scope. That
condition is syntactic (`Closed`), and `render_closed` proves the actual source
expression's environment independence.

A replay leaf receives the original normalized argument; a closed leaf
receives an empty literal argument and has an empty core replay prefix. This
lets it start at the original origin without advancing over the discarded
capture. Both kinds still query installed unary core rows at the same physical
round. The normalization row induction uses the closed source body's
independence to relate its incoming environment to `[[]]`. Therefore source
origin control can choose between replay and capture-independent consuming
branches in the same recursive family. The outer argument guard still
preserves argument failure and undefinedness even when the selected body
ignores that argument.

The new kernel example mixes a nonempty replay, an unshifted replay, and a
closed consuming fallback. The fallback consumes a literal, runs a recursive
capture parser, repeats literals, and calls the same control user with a fresh
argument. After return the outer parent value is reused. Both the replay and
fallback inputs are accepted, and an incorrect inner copy is rejected. A
separate physical core execution shows that passing the six-character original
argument to the closed leaf incorrectly advances it and fails, while its empty
argument succeeds. Generated Seq observations follow from the full compiler.

An unshifted replay accepts the nonperiodic capture `abac` in `abac#abac`.
A direct recursive cycle through an empty argument remains unknown in every
source physical round; the generated Seq grammar has no finite success or
failure observation on that input. This checks that removing nonempty shifts
does not introduce an implicit progress assumption.

Remaining scope: general capture-dependent consuming sequences/stars before
replay, multiple independent general arguments, character-atom normalization,
and normalization of arbitrary original first-order grammars. General Par/Seq
equality or separation remains unresolved.

Validation: full `lake build` passed (856 jobs), including Audit. All 93
public PR theorem dependencies were rechecked. Fourteen new guards use only
standard Lean axioms or no axioms; four existing normalization guards now
include standard `Classical.choice`. The new modules have no proof
placeholders or Lean warnings.

### Consuming continuations without reopening priority choice

`ContinuationPlan` normalizes `P ; Q`, where `P` and `Q` are finite origin-control plans. It keeps original leaves for tests and adds leaves that execute an original leaf followed by `Q`. The choice case explicitly tests the old left branch: `(&A ; continued A) / (!A ; continued B)`. Distributing to `(A ; Q) / (B ; Q)` would reopen a successful `A` if `Q` failed, so it is unsound. The guarded construction preserves the full partial result, including undefinedness. The correctness theorem supports arbitrary appended-leaf offsets, and `expression_eq` discharges its local semantic premises with actual generated expressions.

`LeafContinuation` factors an arbitrary `Arg` tail into actual replay-leaf bodies. The tail may use retained captures, stars, and recursive calls with fresh arguments. Its `Consumer` condition requires every successful output path to select a leaf; arbitrary plans, including negative tests, remain allowed in guards. Closed leaves may be duplicated only when the appended tail is also syntactically closed. Replay leaves have no such restriction. `source_body_eq` identifies the generated body with the existing origin-control source grammar's exact `sourceLeaf` syntax using one common ambient renderer, preserving recursive addresses and capture scope.

`ContinuationGrammar` independently lifts the general plan normalization through actual mutually recursive grammars. Each rule has its own leaf expressions, two plans, and arity. All ordinary physical tables agree at every round for either CBV strategy. Its observation theorem preserves unchanged original strings and retains only syntactic boundedness/first-order premises, with no assumed recursive-row or filter correspondence. This is a within-strategy grammar normalization, not yet a new end-to-end Par-to-Seq theorem for consuming control families.

Kernel examples check a parent `aa` capture, a fresh child `aaaa` capture through recursive calls, and reuse of the original parent afterward. A short successful replay followed by a failed tail rejects `ab#`, while naive distribution accepts it; the guarded normal form rejects it. An empty-star tail after a committed branch remains undefined for arbitrary grammar tables. Unbounded observation preservation is obtained from the grammar theorem rather than a finite example run.

At this checkpoint the global-family assembly and Par-to-Seq composition were still missing; the following section closes that connection. General consuming-entry stars, multiple independent general captures, arbitrary original-grammar normalization, and general Par/Seq equality or separation remain open.

Validation: full `lake build` passed (860 jobs), including Audit. All 31 new theorem guards passed with standard Lean axioms or no axioms. The four new modules have no compiler warnings or proof placeholders; source audit passed.


### Consuming control families composed with the fixed Seq compiler

`ContinuationFamily` now performs that assembly for actual mutually recursive source grammars. Each user supplies its own finite `Leaf` list, origin-control plan, and optional `Arg` continuation. A user with no continuation may use the full original control plan, including a standalone negative test that returns at the origin. A user with a continuation requires the plan to select a leaf on every successful output path. Replay leaves permit arbitrary capture-dependent continuations; a closed leaf requires a closed continuation. These two user forms coexist in the same recursive grammar.

The generated global leaf list concatenates per-user groups. Users with a continuation keep original leaves for guards and append copies with that user's continuation in their bodies. `emit` shifts every plan into its own group without changing original user numbers. The actual source renderer and the normalization renderer share the global ambient layout, so captures stay in their original lexical scope and recursive calls keep the same original user addresses.

`placed_leaf`, `user_body_eq`, and `bodies_eval` discharge the finite placement and local body identities. `tables_eq` then proves equality of ordinary physical tables at every round between the actual source grammar, whose bodies still contain consuming sequence outside their control plans, and the generated origin-control grammar. `observations_iff` composes this with `OriginControlNormalization.observations_iff` to obtain a fixed first-order Seq grammar on unchanged original strings. `language_translation` has only syntactic validity/closedness and independent-helper validity premises. It assumes no capture profile, table stage, row/filter oracle, or replacement-source equivalence.

`ContinuationFamilyExamples` mixes four original users: a capture-dependent parent with a guarded choice followed by a distinct consuming continuation; a shifted child that recursively captures/replays its own argument; a closed consuming root with its own continuation; and a control-only negative-test user. The latter captures one character but returns at its original origin. Actual source runs accept parent `aa` / child `aaaa` / parent `aa`, including a deeper child recursion. They reject reopening a committed short replay, a short child copy, and a short parent copy. Seq observations for the two accepted and three rejected inputs follow from the unbounded translation theorem; the large generated profile grammar is not executed at a guessed finite stage.

The remaining general question is unchanged: these are unary families whose capture-dependent consuming paths first reach a fixed-shift replay leaf. General consuming-entry stars before that replay, arbitrary original-body normalization, and multiple independent general captures are not covered. No general Par/Seq equality or class separation is claimed.

Validation: full `lake build` passed (862 jobs), including Audit. All 56 public PR theorem guards passed; 25 were added with this family composition. Dependencies are standard Lean axioms or none. The six added modules compile without warnings or placeholders; source and whitespace audits passed.

### Leading replay repetitions with their greedy stopping test

`GreedyRotation` proves the complete partial-parser identity `(A B)* A = A (B A)* !B` for decreasing deterministic parsers. It includes failure, undefined recursive queries, and zero-consumption loops. The proof uses strong induction on the actual remaining input position, without requiring that A or B consume a nonempty word. For actual first-order CBV expressions, decreasingness follows from a sound table's physical-prefix property. This local soundness premise is discharged by `tblV_sound` when transporting recursive grammars.

The final `!B` is necessary. On `ab#`, `(a b)* a` fails after greedily consuming `ab`; `a (b a)*` instead succeeds after the first `a`. Its missing stopping test would manufacture an early endpoint. The guarded rotated expression fails correctly. Empty capture with a consuming B progresses normally, whereas empty capture and empty B remain undefined.

`LeadingReplayStar` adds source users with bodies `(R B)* R tail`, where R is a fixed literal shift followed by parameter replay. The shift may be empty; captured values are not bounded or enumerated. B and the tail may use the retained capture, independent recursive helpers, and arbitrary valid recursive user arguments, including fresh captures. The source is normalized to the ordinary replay leaf `R ((B R)* !B) tail`, then translated by `ContinuationFamily`. Existing control-only and consuming-control users remain available in the same mutually recursive family.

Ordinary physical source and normalized tables agree at every round. The final observation and language theorems preserve original strings and require only syntactic family/entry validity and independent-helper validity. They retain no partial-row, capture-profile, non-nullability, or replacement-source premise. The grammar is generated once independently of runtime captures and input length.

Kernel examples use an outer two-character capture, a six-character capture replayed inside the leading star with a one-character shift, and a fresh twelve-character child capture inside each loop body. One and two iterations succeed and preserve parent reuse after child return. Short child/parent copies are rejected. Seq observations follow from the unbounded translation theorem, not a bounded run of the generated profile grammar.

This closes a leading-star case that has a final replay and a replay at the start of each iteration. Arbitrary leading consumption before the first replay, repetitions without that structure, multiple independent general captures, and arbitrary original-grammar normalization remain open. General Par/Seq equality or class separation is still not established.

Validation: full `lake build` passed (865 jobs), including Audit. All 77 public PR theorem guards passed; 21 are new for this extension. All dependencies are standard Lean axioms or none. The nine added modules compile without warnings or placeholders; source and whitespace audits passed.

### Selecting different replay leaves inside a leading star

`LeadingReplayStar.User.selected` generalizes the leading repetition from one fixed shifted replay R to a finite origin-control parser A. Its source body is `(A B)* A tail`; A expands the supplied leaves and plan at the original position, using choice, negative tests, and positive guards. The generated `ContinuationFamily.User` retains A as its control plan and appends the rotated continuation `(B A)* !B tail`. The existing guarded continuation normalization then distributes this tail into selected leaves without reopening a successful choice.

`render_expand` connects the actual source renderer with the finite plan syntax, and `rotate_tail` applies the general partial-parser rotation with an arbitrary suffix. Whole-table equality, observations, and fixed Seq language translation are proved by the same physical-round transport as before. The computed syntactic `Valid` condition requires a bounded plan that selects a leaf on every successful output path, valid leaf/argument syntax, and the existing closed-continuation condition for closed leaves. It retains no row, state-profile, non-nullability, or source-replacement oracle.

`SelectedReplayStarExamples` uses two output leaves with different shifts and literal markers, plus a negative guarded probe. Under the same six-character capture, the two leaves consume different spans. One leading-star execution chooses L, then R, then L, while recapturing twelve characters in each child invocation and preserving the original capture after return. The kernel checks two accepted runs and short child/parent rejection. Their Seq observations follow from the unbounded grammar translation. Another actual partial-evaluator example distinguishes the committed short choice from an unsound distribution that retries the longer leaf after a suffix failure.

This extends the leading-star case to per-iteration branch selection. The Consumer and closed-leaf conditions still restrict the eligible control syntax; arbitrary first consumption before replay, unrestricted leading stars, multiple independent captures, and general Par/Seq equality or separation remain unresolved.

Validation: full `lake build` passed (866 jobs), including Audit. All 86 public PR theorem dependencies were rechecked and all guards passed; 9 guards are new. All dependencies are standard Lean axioms or none. The ten added modules compile without warnings or placeholders; source and whitespace audits passed.


### Leading repetitions without a mandatory final replay

`GuardedStarFactor` removes the final A requirement from the preceding rotation. For decreasing partial parsers A and B, put `G = &(A B) ; A`. It proves the complete partial-result identity

```
(A B)* C = (G ; (B G)* ; B ; C) / (!(A B) ; C).
```

The guard on every later A prevents consuming an A whose B fails. For example, `(ab)* ac` accepts `abac`; using an unguarded `(ba)*` on the right loses the final `a` and rejects it. The initial negative branch also commits to the original star result: a later C failure cannot restart C at the original position. The proof includes failed/undefined parses, zero iterations, empty successful iterations, and differing A/B consumption. All guards and repetitions are inline expressions; no recursive rotation helper or extra clock hypothesis is needed.

`StarThenPlan` gives the actual finite leaf layout for this identity. A and C are expanded from two bounded origin-control plans P and Q over a local leaf list. P is Consumer; Q may also return through a negative test. Original leaves implement tests, selected P outputs receive B in one copy block and `(B G)* B C` in another. `ConsumingPlanOutputs` tracks only output leaves, so guard-only and C-only leaves remain unchanged in the copy blocks. In particular, a closed C-only leaf does not acquire an unused capture-dependent continuation. A closed leaf actually selected by P still has the existing closed-continuation restriction.

`StarThenCompiler` combines these users with the earlier control/consuming/leading-replay users in one mutually recursive source grammar. It proves equality of ordinary physical tables at every round, then composes the existing translation to a fixed first-order Seq grammar. The final observation/language theorems preserve the same original input strings. Their assumptions are independent helper validity, computed syntactic family validity, and valid entry syntax. No partial-row, runtime capture/profile, non-nullability, replacement-source, or clock-cofinality premise remains.

Kernel examples include zero repetitions, mixed L/R repetitions with different shifts under the same six-character capture, fresh twelve-character recursive child captures, a final successful A with failed B, a final negative test returning before the argument endpoint, and a closed final `ac` leaf despite a capture-dependent loop body. They reject a short retained copy and distinguish both missing-next-iteration guards and an unsound fallback after C failure. Seq observations of the recursive examples follow from the unbounded translation theorem. Empty capture/empty iteration preserves undefinedness.

This removes the mandatory final replay and permits an independent final origin-control plan. It still requires an eligible finite Consumer plan at the beginning of each iteration, and computed validity for its generated leaves. Arbitrary consumption before the first replay, unrestricted original body normalization, and multiple independent general captures remain open. General Par/Seq equality or class separation is not established.

Validation: full `lake build` passed (871 jobs), including Audit. All 38 new public theorem dependencies are standard Lean axioms or none and have guarded checks. The five added modules compile without warnings or placeholders; source and whitespace audits passed.


### Recursive normalization from source body syntax

`BodySyntaxNormalization.Body` supplies the source tree before normalization. Its constructors are a raw replay/closed leaf, priority choice, negative predicate, sequence of two bodies, and `starThen a B c` for `(a B)* c`. Both a and c are recursively supplied bodies, so the leading-star structure can occur inside choices, predicates, sequences, and other eligible repetitions. Raw leaf bodies and B retain the existing arbitrary recursive argument syntax.

`BodyNormalForm` computes the finite leaf array and control plan. Joining forms places right-hand leaves after the left array and shifts their plan references. Sequence selectively appends the normalized right body to actual output leaves and uses the original guarded bind. `ConsumingPlanOutputs.bind_correct` now covers all finite plans, including a negative test that succeeds at the origin and proceeds directly to the right body. Consumer is no longer required at sequence nodes. Repetition uses the guarded `(a B)* c` construction after recursively normalizing both a and c. Bounds and nonempty-array proofs are generated by the constructors.

`Ready` recursively checks the source syntax and requires the normalized a plan to be Consumer at each starThen node. `BodySyntaxCompiler.Valid` combines these readiness checks with the existing computed validity of generated leaves/plans. Thus a closed leaf followed by a retained-dependent continuation can still fail validity; this does not establish unrestricted closure under arbitrary sequencing. Likewise, a predicate-output iteration need not satisfy the Consumer check. These conditions are syntactic, with no supplied equivalence or partial-row certificate.

The normalization theorem preserves the full partial evaluator at every valid physical position, deriving endpoint bounds from SoundTV. `BodySyntaxCompiler` then generates the actual mutually recursive source grammar from the original trees, proves physical-table equality at every round, and composes the fixed first-order Seq translation on the original strings. The final theorem requires helper/entry validity and the computed family validity. There is no runtime capture bound, semantic replacement-source premise, or clock-cofinality hypothesis.

`BodySyntaxExamples` uses source trees containing a negative prefix, sequences around an outer star, and a nested inner star in its selected body. One run completes two inner iterations within one outer iteration, then invokes a fresh twelve-character child capture while retaining the original six-character capture. Existing mixed-branch, zero-iteration, failed-last-B, negative/closed-final-body, and short-copy cases also pass. Their Seq observations follow from the general unbounded grammar theorem; examples do not provide normalized leaf arrays or source-equivalence witnesses.

This closes recursive normalization for the stated syntax with readiness/generated-validity checks. Arbitrary original bodies, consuming closed prefixes followed by retained-dependent work, unrestricted star operands, and multiple independent general captures remain open. General Par/Seq equality or class separation is still unresolved.

Validation: full `lake build` passed (875 jobs), including Audit. All 69 public PR theorem dependencies were rechecked and all guards passed; this extension adds 31 guards. The nine added modules compile without warnings/placeholders; source and whitespace audits passed.


### Plain stars with predicate outputs

`NullableStarControl` removes the operand Consumer requirement for a new ordinary `Body.star` constructor. A negative predicate selected as an output succeeds at the origin, so its enclosing star immediately becomes undefined. The finite `freeze` transformation replaces only such output paths by an explicitly divergent guarded branch. Original leaves and guard queries keep their partial behavior. `eval_change` proves that the transformed result either equals the original result or replaces an original empty success by undefinedness; `star_change` proves that star cannot distinguish these cases.

The divergent leaf is closed and appears only as a guard query. A separate replay leaf supplies the syntactic output of that unreachable branch. Selective continuation copies therefore never append capture-dependent continuations to the divergent closed leaf. The final zero-iteration result is represented by a predicate plan, rather than by a closed epsilon output leaf; this also allows enclosing stars to freeze that empty result. Consumer here remains a syntactic output-path condition and does not assert positive consumption by all replay leaves.

The normalizer feeds the transformed operand through the existing guarded repetition factorization with positive epsilon as B and a predicate epsilon as C. `repeat_eval` proves full partial-evaluator preservation, without an operand Consumer, nonempty capture, or non-nullability premise. `BodySyntaxNormalization.evaluator_eq` includes ordinary star by recursively normalizing its operand and applying this theorem. The physical-table and fixed Seq observation/language results follow through the existing body grammar compiler.

`NullableStarExamples` proves that its operand is not Consumer, checks generated syntactic validity, accepts `ab!ab!#ab` while retaining `ab` across iterations and after stopping, rejects a short final copy, and preserves undefinedness when a predicate succeeds without consuming. A nested star example remains undefined. The general `nested_star_none` theorem and the actual source-body theorem establish that nested-star undefinedness holds for every position and table, including all physical approximation rounds. The accepted Seq observation follows from the unbounded translation theorem.

Ordinary star no longer introduces a Consumer readiness condition. The older specialized starThen constructor retains its check, and generated-family validity/closedness still restricts the supported bodies. Consuming closed prefixes followed by retained-dependent work, full coverage of arbitrary original grammars, and multiple independent general captures remain unresolved. General Par/Seq equality or class separation is still not established.

Validation: full `lake build` passed (877 jobs), including Audit. All 87 public PR theorem dependencies were rechecked and guards passed; 18 guards are new. The two new modules and extended body normalizer compile without warnings or placeholders; source and whitespace audits passed.


### Automatic entry from ordinary Arg source bodies

`ArgumentBodyView.view` derives Body syntax from an ordinary `RecursiveArgumentCompiler.Expr`. Literal/helper/user expressions become raw leaves; choice, sequence, predicate, and ordinary star are recursively viewed. `param 0`, `param 0 ; b`, `lit u ; param 0`, and `lit u ; (param 0 ; b)` are recognized as replay heads. The remaining body b is retained as actual argument syntax. The local view theorem preserves the complete partial evaluator at valid positions; it does not require source validity/closedness or a supplied source-equivalence witness. Every generated view is Ready because the bridge uses ordinary star rather than the specialized starThen constructor.

`ArgumentBodyCompiler` takes a list of original Arg bodies and constructs an actual unary source grammar with those bodies. The automatically generated views supply the intermediate Body grammar. Header equality and body correspondence yield equality of ordinary physical tables at every round. Composing with the existing Body/Seq compiler proves fixed first-order Seq observation/language preservation on the same original strings. The final assumptions are independent helper/entry validity and computed validity of the generated family. No caller-supplied Body tree, leaf layout, readiness proof, semantic row/profile oracle, or replacement-source equality remains.

`ArgumentBodyExamples` supplies only original Arg bodies. Its iteration chooses between complete L/R branches with different fixed replay shifts, each invoking a child with a fresh twelve-character capture. It checks retention of the original six-character capture after return and the outer two-character capture after the user call. Mixed, zero-iteration, failed-last-body, negative final-body, closed final-body, and short-copy cases pass; corresponding Seq observations follow from the unbounded grammar theorem. These source branches select complete iterations, rather than claiming an unguarded distribution of an earlier `(A / B) ; C` source.

The generated-family validity restriction is substantive. `consuming_prefix_source` checks that the ordinary source body `a* ; "#" ; param 0`, called with argument `a`, accepts `aaa#a`. `consuming_prefix_not_valid` proves that this same original body fails the automatic compiler's computed Valid condition. This is a limit of the normalization criterion, not a language-class separation or evidence that this language lacks a Seq grammar. Consuming closed prefixes before retained-dependent work therefore remain a concrete next gap. Full coverage of arbitrary source grammars, multiple independent general captures, and general Par/Seq equality or class separation remain unresolved.

Validation: full `lake build` passed (880 jobs), including Audit. All 112 public PR theorem dependencies were rechecked and guards passed; 25 guards are new. The three new modules compile without warnings/placeholders; source and whitespace audits passed.


### Consuming scanner prefixes with changing retained-dependent arguments

`ScannerCapturedArguments` types argument consumption by a static scanner alphabet A. Safe arguments may use old parameters, literals/characters from A, sequence, choice, star, and arbitrary negative queries. An environment invariant says that each retained word consists of A characters. Substituting those actual words produces the existing scanner-safe syntax; successful argument evaluation therefore leaves the scanner's dropWhile endpoint unchanged. A separate prefix lemma derives that the actual new captured word also consists of A characters. The final invariant is thus propagated from real call arguments rather than supplied as an oracle. `singleton_scan` identifies the singleton scanner with ordinary one-character literal repetition.

`ScannerArgumentFusion` considers a fixed unary grammar whose rules are `scan A ; tail_i`, all using the same A. Tails may consume arbitrary input, reuse captures, and recurse; every nested unary call must have an alphabet-safe argument. Supported recursively checks calls within arguments and negative queries as well. Consuming user calls directly inside safe arguments are not admitted; queries can contain supported recursive calls. The entry expression satisfies the same syntactic check and starts with an empty environment.

The physical-table relation aligns a Par row at the origin with a Seq row after its actual captured A-word. Both scanners reach exactly the same endpoint, after which recursive tail correspondence applies under the preserved capture invariant. This proves complete entry evaluator equality at every physical round, all-input observation equivalence, and a fixed first-order Seq language translation. The same grammar is sufficient for this family. No fixed callee argument, capture-length bound, finite Word palette, supplied row correctness, or initial replay is assumed.

The examples pass retained `a` twice and append a fresh `b*`, capturing `aabbb` in a child invocation. The child scanner consumes an additional `ab` before the delimiter, replays `aabbb`, and returns to the parent's retained `a`. Empty fresh suffix and short-child rejection also pass; Seq observations follow from the general all-input theorem. The consuming-prefix `a* ; "#" ; param 0` case is covered when its actual argument is syntactically alphabet-safe. This is a separate scanner-family theorem and does not change the previous automatic normalizer's `consuming_prefix_not_valid` result.

The alphabet condition is essential for this identity construction. A capture `a#a#` on input `a#a#a#` crosses the scanner delimiter: Par accepts and Seq with the same grammar rejects, and the argument fails Safe. This is a boundary example, not a class-separating language. Captures crossing the scanner frontier, arbitrary consuming closed prefixes, integration of this family with the general body compiler, and multiple independent general captures remain open. General Par/Seq equality or separation is not established.

Validation: full `lake build` passed (883 jobs), including Audit. All 133 public PR theorem dependencies were rechecked and guards passed; 21 guards are new. The three new modules compile without warnings/placeholders; source and whitespace audits passed.


### A runtime shift cannot use one fixed finite capture filter

`CBV/RuntimeShiftFilter.lean` examines the remaining consuming prefix
`a*;#` directly. `scanner_eval` proves that this actual expression consumes
`a^n#` on every input `a^n# ++ rest`, for either strategy and arbitrary
tables and environments. The shift length is unbounded and input-dependent.

Write `b(n)=a^n#`. For a capture `b(n)++b(m)`, the necessary overlap
condition is exactly

```text
(b(n)++b(m)) is a prefix of b(n)++(b(n)++b(m)) iff n=m.
```

`no_uniform_filter` proves that no fixed valid finite `RegularCaptureProduct.Machine`,
with any accepting-state predicate, decides this condition for all n,m.
Correctness would make its states after b(n) pairwise distinct: append b(n)
to distinguish any colliding b(n),b(m). `CaptureOrbit.bounded_collision`
then contradicts the finite width. `fixed_shift_filter` separately confirms
that the existing phase machine remains exact for each individual static
shift. Merely choosing one larger fixed machine cannot extend that method
to this unbounded runtime family.

This is a compilation-method obstruction, **not a Par/Seq class separator**.
Indeed `seq_compare_blocks` and `seq_observations` prove that one fixed
first-order Seq grammar, `Replay(x)=x` with entry `Replay(a*;#)`, accepts
every b(n)++b(n) and finitely rejects every b(n)++b(m) with n!=m. It stores
the runtime block itself rather than a finite phase. No argument above
excludes Seq mechanisms using retained captures, recursive work, or queries.

The next missing construction must preserve that kind of unbounded runtime
information while also preserving the original argument parser's selected
capture, undefinedness, and later reuses. The direct two-block comparison
is already handled by Seq; turning arbitrary crossing captures into such
a representation remains unresolved. General equality or separation has
not been established.


### Retaining a runtime prefix codeword for crossing captures

`CBV/PrefixCodeCapture.lean` begins the replacement for a uniform finite
filter. For any prefix-free code, if the actually selected argument capture
is `u++v` for complete codewords u,v, successful replay after consuming u
forces u=v. The codeword set and the individual words may be infinite and
unbounded. `actual_capture` derives this from actual first-order argument,
head, and replay evaluations through a sound table. The argument may use
retained values or recursion; its selected capture is never guessed anew.

`collapse` is a complete partial-result identity at the advanced body entry.
With a complete v at the current suffix, matching the old `u++v` and using
it in an arbitrary first-order continuation is equivalent to matching the
retained u twice and replacing every old parameter occurrence by that
duplicated view. Unequal codewords give failure on both sides. Equal words
preserve every continuation result, including undefinedness. `view_eval`
uses `CaptureViews.evV_rebind`, so parameter uses inside call arguments,
choice, predicates, and repetition are covered through the same arbitrary
recursive table. The proof does not assume the continuation succeeds.

`actual_entry` derives this identity at a real source call from its argument
and head evaluations; it does not assume the final replay succeeds.
`two_header_entry` instantiates it with the actual two-header argument
`(a*;#);(a*;#)` and body prefix `a*;#` at every valid physical suffix, for
all first/second header lengths and every first-order continuation.
`scanner_at` supplies the actual argument/head results. No finite phase or
finite value palette is used for this representation.

`PrefixCodeCaptureExamples.recursive_execution` kernel-checks physical
source Par and candidate target Seq grammars on the same ordinary input.
The source retains parent `aa#aa#`, captures child `aaa#aaa#`, and reuses
the parent after the child returns. The candidate retains `aa#`/`aaa#`
and duplicates them where the source uses its longer capture. Both accept
`aa#aa#aa#@aaa#aaa#aaa#!?aa#aa#`; both finitely reject the short parent
copy and unequal child headers. A preflight of the original two-header
argument precedes candidate Seq calls.

**Scope:** the unbounded theorem is a local entry/representation identity
within one strategy and recursive table. The finite recursive executions
do not establish an all-input recursive grammar translation. The remaining
work includes translating the recursive rows, preserving argument failure
and undefinedness at calls, and handling captures beyond the two-complete-
codeword shape. No general Par/Seq equality or separation is claimed.


### Runtime prefix-code representation now gives a recursive translation

`CBV/RuntimePrefixGrammar.lean` closes the recursive-table and call-level
gaps left by the preceding local representation lemma for the two-codeword
family. A `Header` supplies a closed call-free parser A (choice, predicates,
and nullable repetition are permitted), a prefix-free code, and a proof that
each successful A capture is in that code. This is a lexical output
certificate, not a supplied equivalence of source/target calls or tables.
The parser and its words need not have a length bound or finite value palette.

For a finite list of raw tails, the source has unary rules with bodies
`A;param0;tail`, and each source call captures the actual result of `A;A`.
The target call first tests `&(A;A)` at the original position, then captures
A once. Target rules replay the retained codeword twice, and rewrite all
old parameter uses to that duplicated view. Raw zero-argument recursive
calls choose a rule in this family; ordinary consuming sequence, choice,
predicates, and repetition are allowed throughout the tails and entry.
This is a constructor for a specified source family, not a renderer for
arbitrary source argument syntax.

`tables_shifted` proves the correspondence on ordinary physical tables at
every stage, including zero. If the two selected codewords differ, the
source and target body prefixes both fail. If they agree, both prefixes
reach the same original-input suffix and `evaluator_of_shift` compares the
continuations with old capture u++u and retained target capture u. Recursive
calls are handled by the previous physical stage; no helper stabilization
or caller-supplied recursive equivalence is needed. The preflight preserves
argument failure and undefinedness before querying the target row.

`observations_iff` preserves every finite success remainder and finite
failure on every original input. `language_translation` constructs one fixed
first-order Seq grammar and entry, independent of the input, preserving
whole-string recognition. Undefinedness is preserved by the complete
physical partial-result equalities; no final-success assumption is used.

`RuntimePrefixExamples.header` proves the lexical certificate for the actual
`a*;#` parser, using the prefix-free code defined by
`dropWhile (accepts ['a']) w = [#]`. Both code safety and prefix freedom are
proved, not assumed. Its two-rule mutual recursion changes the runtime
header length from 2 to 3 to 1, then restores the child and parent captures.
The source physical tables accept
`aa#aa#aa#@aaa#aaa#aaa#%a#a#a#!?aaa#aaa#?aa#aa#` and reject the short parent
and unequal child. Target Seq observations follow from the all-input
translation theorem. `previous_candidate_all_inputs` also proves the exact
source/target pair of the preceding `PrefixCodeCaptureExamples` equivalent
on all inputs; those earlier finite checks now have an unbounded bridge.

`preflight_stage_zero` checks why the guard is present: on `a#`, the original
two-header argument and the generated target call both finitely fail at
stage zero, whereas a plain target call capturing one header reaches an
undefined stage-zero row.

The general class comparison remains unresolved. This compiler fixes each
call argument to the two-head parser A;A, uses one common closed call-free
header parser, and begins every rule body with A followed by immediate
replay. Arbitrary selected arguments, captures with other shapes, independent
multiple captures, and arbitrary consuming prefixes are not covered. The
result is an actual fixed recursive grammar translation for this family,
not a proof of the general reverse inclusion.


### Preserve independently selected two-codeword arguments

`CBV/SelectedPrefixGrammar.lean` removes the fixed `A;A` argument of the
preceding compiler. Each source rule has its own closed call-free argument
parser B, allowing prioritized choice, predicates, and repetition (including
undefined nullable repetition). Its output certificate says that every
successful selected capture consists of two complete words of the header's
prefix-free code. The certificate constrains the captured shape; it does
not supply a source/target evaluator or recursive-table equivalence.

Source calls are ordinary `F(B)`, with source bodies `A;param0;tail`. The
constructed target first tests **the original B**, then captures A once and
uses the duplicated retained value. In particular, it does not replace the
argument by `A;A`, choose B's result again after a continuation failure, or
ignore B's undefinedness when A could fail.

The body header can now fail even after B succeeded. A finite counterexample
in `SelectedPrefixExamples.early_head_failure` makes the resulting clock
difference explicit: on `a#a#X`, the original physical stage-zero call is
undefined, physical stage one fails, and the target already fails at stage
zero while evaluating A as an argument. Ordinary stage-by-stage equality
would be false here.

The proof uses the existing `SeededClock` construction **only on the source
side**. A failed A prefix is placed in the initial source row, justified by
an actual finite source computation. `tables_shifted` relates these source
rounds to ordinary target physical stages. It handles B's actual selected
capture, obtains the first codeword from A's independent successful parse,
and uses prefix freedom to identify that word with the first part of B's
capture. Unequal parts cause matching replay failures; equal parts reach
the same suffix with corresponding retained values. `stable_eq` removes
the seeds by their proved cofinality with source physical tables.
`observations_iff` and `language_translation` consequently concern the
actual ordinary grammars and unchanged original inputs, including finite
failure and preservation of undefinedness.

`SelectedPrefixExamples` supplies syntax-derived code certificates for B
with choice and tests before/after capture. A second argument has an
unproductive empty-star fallback. A guarded `a*;#` header independently
rejects the X case even though B succeeded. The old three-generation
recursive good input is accepted and the short parent copy rejected; Seq
observations follow from the unbounded translation. `a#a#Z` tests rejection
by the original selected argument before any target header or row query.
`undefined_argument` proves that an undefined B remains undefined before
body entry for arbitrary tables, and `undefined_at_every_stage` checks an
actual argument with empty-star divergence at **all** physical stages.

This closes the independently selected argument and early-head-failure
gaps within the two-codeword, closed call-free argument family. The argument
parser still cannot depend on retained parameters or call recursive helper
parsers, the header remains closed call-free, and other capture shapes or
multiple independent captures are not translated. General Par/Seq equality
or separation remains unresolved.


### Recursive helpers for runtime prefix-code captures

`RecursiveCodeGrammar` removes the closed call-free restriction on both
header A and the independently selected argument B. A finite installed
component of ordinary nullary PEG rules may be recursive or mutually
recursive and may include undefined cycles. A and each B can use any
lexical expression over this component, including choice, predicates,
sequence, and repetition. Their successful captures still require the
same prefix-free code and two-codeword shape certificates; those
certificates are stated at the actual stabilized standalone helper table.

The generated grammars install the same helper component before their
unary user rules. Source user bodies have `A;param0;tail`, and source calls
pass B. Target calls test the original B and capture A; target bodies
replay the captured word twice and replace old parameter uses by duplicate
views. User tails may contain mutual recursion, sequence, choice,
predicates, and repetition. No helper calls into user rules or retained
parameter dependencies are permitted in A or B.

`frozen_lexical` and `seeded_lexical` derive the helper evaluation
correspondence from actual physical helper rows, using independence of
the installed component. `tables_shifted` synchronizes source prefix-seeded
rounds with target rounds having stabilized helpers. The proof then removes
both internal clocks using proved cofinality. `observations_iff` preserves
**all finite observations on the same original input** between the actual
ordinary grammars; `language_translation` produces one fixed first-order
Seq grammar. Its final statement contains no table advice, oracle, seeded
semantics, supplied row equivalence, or input transformation.

`RecursiveCodeExamples` uses the genuine recursive helper
`R <- 'a' R 'b' / eps` and header `R '#'`. A separate unproductive nullary
cycle coexists in the same component. Successful balanced-header captures
satisfy a prefix-free code certificate derived from the actual helper
syntax and consumption. An argument parses two such headers. Kernel
execution checks parent `aabb#`, child `ab#`, restoration and replay of the
parent capture after return, and rejection of a short parent copy. Target
observations are obtained from the all-input theorem. The cyclic argument
is undefined in the ordinary source at every physical stage, and the
generated Seq grammar has no finite observation for it on any input.

This closes recursive **independent helper** parsing in the runtime
prefix-code construction. It does not cover arguments depending on retained
values, arguments recursively calling the parameterized user component,
other capture shapes, arbitrary consuming prefixes, or multiple independent
captures. General Par/Seq equality or separation remains unresolved.


### Retained-value-dependent arguments in the same runtime code compiler

`HelperArgument.Syntax` extends lexical argument expressions with retained
parameters, under sequence, choice, predicates, and arbitrary repetition.
Calls still target the independent nullary recursive helper component.
`eval_eq` proves complete partial evaluation agreement using actual helper
row agreement and the same retained environment; parameters are not erased.

`RecursiveCodeGrammar.User` now certifies its argument's successful
**actual environment-dependent** captures in the stabilized helper table.
Every such capture must still have two codewords, for every environment.
Source calls pass the original argument B. Target calls instead test
`view B`, where old parameter zero is read as two copies of the retained
header word. `argument_view_eval` derives full partial result agreement
from helper independence and the retained-parameter relation. This commits
the same argument selection before header evaluation. The shifted-row
invariant now quantifies the original calling environment. The existing
cofinality proof gives ordinary fixed-grammar `observations_iff` and
`language_translation` on unchanged inputs, with no externally supplied
recursive equivalence or filter oracle. Undefined dependent arguments
remain undefined before body entry on both sides.

`DependentCodeExamples` uses `!param0; (R '#'); (R '#')` as the actual
argument, with `R <- 'a' R 'b' / eps`. It accepts a fresh child's capture
only if the old retained value does not already match there. The argument's
selected result changes when only the parent's retained value changes.
A separate kernel test shows that testing the unmodified argument with
only one retained header word changes its result; the duplicated view is
required even for partial argument selection. The actual recursive source
accepts parent `aabb#`, child `ab#`, then reuses the parent's two-word value
after return. It rejects short parent copies and a child repeating the
parent value. All target observations follow from the all-input theorem.
Earlier closed recursive-helper and unproductive-cycle examples still pass.

This removes the **retained-value independence** restriction on argument
parsers in this construction. Headers themselves remain independent of
retained values. Two-codeword capture certificates, independent nullary
helper calls, and unary user rules remain restrictions. Recursive argument
calls into parameterized users, general capture shapes, independently
multiple captures, arbitrary consuming headers, and general Par/Seq
class equality or separation remain unresolved.


### Any positive fixed codeword count, chosen separately per rule

`CodewordReplay` removes the special role of two codewords from the local
runtime capture representation. Unique prefix decoding compares an arbitrary
finite list of codewords against another encoded list plus an arbitrary
suffix. If `u ++ flatten(vs)` can be replayed after consuming the first
codeword `u`, then `vs` must be a list of copies of `u`. A target replay of
`length(vs)+1` copies of `u` forces the same condition. When the condition
fails both replays fail; when it holds their consumed strings and subsequent
retained-value views agree. `collapse` preserves the complete partial
result for every first-order continuation, strategy, and table.

`CountedCodeGrammar` incorporates this representation in the ordinary
recursive compiler. Each user rule carries its own natural `extra`; its
successful original argument captures `extra+1` complete codewords. The
words are not assumed equal: equality is forced by actual shifted replay,
and unequal captures fail correctly. Headers are the same independent
recursive PEG parsers as before. Arguments retain the `HelperArgument`
syntax, so selection, predicates, repetition, retained parameter uses, and
independent recursive helper calls remain supported.

The caller's count determines the view of old retained values used to test
the original argument. The callee's separate count determines replay and
views after a fresh capture. Thus different counts may coexist in mutual
recursion without changing the fixed grammar at runtime. Actual helper
stability, prefix-failure seeds, and both cofinality bridges again yield
`observations_iff` and `language_translation` for all finite observations
and whole-string recognition over unchanged original inputs. The theorem
permits any positive initial view count; empty initial environments require
positivity so a missing parameter cannot become a successful empty replay.
No count bound shared by all grammars or codeword length bound is assumed.

`CountedCodeExamples.headers_captured` derives actual shape certificates
for every count from `R '#'`, where `R <- 'a' R 'b' / eps`. Dependent
arguments first test `!param0` and then parse the required number of
headers. A three-generation physical source execution alternates counts
**3 -> 1 -> 3**, with runtime codewords `aabb# -> ab# -> #`, and reuses
both child and parent values after return. Kernel checks also reject a
short parent copy and an unequal three-codeword capture. All generated Seq
observations follow from the full same-input translation theorem.

Counts remain fixed **per rule**, rather than varying without bound with
the input. This closes the fixed two-codeword restriction, but does not
translate arbitrary capture shapes, retained-value-dependent headers,
argument calls into parameterized user rules, independent multiple
captures, or arbitrary consuming prefixes. General Par/Seq class equality
or separation remains unresolved.


### Leave the final header outside an input-dependent capture

A separate route keeps the **whole original capture**, avoiding loss of
its input-dependent codeword count. For a partial header parser A, let
`B = (A &A)*`. `LastCodewordRotation.rotate` proves
`B A = A A*` for all deterministic decreasing partial parsers, including
finite failure, later undefined results, and nullable repetition loops.
`expression_rotation` connects this equation to actual first-order CBV
expression evaluation under a sound table. `capture_endpoint` derives from
a successful actual B that either A already fails at the original position
and B is empty, or B ends at a final successful A immediately followed by
A's finite failure. `last_trace` constructs the B trace with one fewer
iterations from any nonempty maximal finite A trace. No grammar count is
used in these parsers.

`LastCodewordCandidate` first supplied a candidate; its all-input certificate
is now `LastCodewordExamples.all_inputs` below. Set A to `a* '#'`, B as above, and `tail = '!';param0`.
The source has `F(x) <- A x tail`, called as F(B) under Par.
The Seq candidate has `F(x) <- A tail`, plus
`V(u) <- (&A u)* !A`, entered through `&B; &V(A); F(B)`.
V checks that the maximal run consists of copies of its runtime first
header; F retains B's entire capture and consumes the final header before
reusing that original capture after '!'.

For `u = a^k '#'`, the **same fixed pair of grammars**, independent of k
and n, is proved to accept every `u^(n+1) '!' u^n` for all k,n, including
n=0. These are ordinary physical-stage evaluations and SObs derivations,
not bounded enumeration. `capture_at` and `captured_value` prove that the
actual B captures n complete runtime words while leaving the final word.
`verifier_at` checks all n remaining words, and `body_at` verifies the same
retained full string after the source shifted replay and the candidate's
last-header consumption. Both runtime header length and captured word
count are unbounded without changing the grammar.

The initial `&B` is necessary for partial semantics: with header
`A / (eps)*`, input `a#aa#Z` gives an undefined source argument. A premature
verification sees unequal headers and finitely fails before reaching the
later undefinedness. The actual ordinary Seq candidate without `&B` thus
fails, whereas the guarded entry remains undefined. This guard-order
counterexample is kernel-checked.

The all-input gap for this candidate is closed below, followed by a
recursive integration for the same designated argument family. The
preceding fixed-count recursive compiler is separate. General Par/Seq
class equality or separation is still unresolved.

### Last-header verification on every original input

`LastCodewordVerification.Run` labels every actual strict header step with
its consumed substring. `run_of_trace` derives these labels from ordinary
sound evaluation and the header's prefix-code certificate. `capture_run`
extracts the whole maximal run from the successful original B itself;
it proves that B's actual capture is exactly the run with its final word
removed. The empty exception is an empty capture with A failing at origin.
No list of words or periodicity certificate is assumed at call entry.

For any run `u::vs`, the captured prefix matches after the first header iff
all words in vs equal u. Unique prefix decoding proves this for arbitrarily
long nonuniform lists, not only powers of a header. `verifier_run` proves
that the fixed expression `(&A;param0)*;!A` has exactly this result on the
actual remaining run. A mismatch stops the repetition, then `!A` rejects
at the mismatching header, even if more copies occur later.
`actual_entry` connects source replay and target last-header consumption
with the same entire capture and an arbitrary continuation, including its
failure or undefinedness.

`LastCodewordGrammar` installs actual ordinary source and target rows for
a pure prefix-code header A and a call-free tail b that may use the held
parameter, sequence, choice, predicates, and repetition. Its translation is
`F(B)` under Par to `&B; &V(A); F(B)` under Seq, with B=(A;&A)*,
source F(x)=A;x;b, target F(x)=A;b, and V(u)=(&A;u)*;!A. The grammar is
fixed independently of input lengths and header counts, including zero
captured words. `physical_agreement` proves complete partial agreement at
every positive source and target physical stage, on every input suffix.
Stage zero may differ because the Seq guard can reject before an
uninitialized row query; monotonic lifting and actual table stability give
`observations_iff` and `language_translation` on unchanged original inputs.
The final theorem contains no supplied table correspondence or filter oracle.

`LastCodewordExamples.all_inputs` specializes this theorem to the exact
previous candidate with A=a*;'#' and b='!';param0. Unequal headers, short
retained copies, zero captures, and undefined continuations are also checked
in ordinary physical tables. Recursive continuations for this argument
family are integrated below. Recursive headers for this new route, more
general capture shapes, and independent multiple captures remain
unresolved, along with general class equality or separation.


### Unbounded last-header captures through mutual recursion

`LastCodewordRecursive` removes the call-free-tail restriction for this
route. A fixed finite set of unary user rows shares a pure prefix-code
header A and the argument B=(A;&A)*. Each source user body is
`(A;param0);render(source,tail)`; each target body is
`A;render(target,tail)`. Calls in arbitrary finite sequence, choice,
predicate, and repetition syntax may call any user row, recapture B at the
new position, and return to the unchanged whole parent capture. Both
renderings use exactly the same retained environment, without a repeated
word view or a grammar-fixed count. The ordinary target installs a single
unary verifier V(u)=(&A;u)*;!A and renders each call as
`&B; &V(A); F(B)`.

The verifier's entire physical row stabilizes after one ordinary round,
including every retained value and every physical suffix. Freezing this
proved row separates its initialization from recursive user depth. The
source's actual failed `(A;param0)` prefixes are seeded before user
iteration. `seed_entry` proves that this seed exactly matches the Seq
verifier's early rejection on every successful B. It uses the proved local
entry equation with an undefined continuation, and cannot seed a negative
answer for an undefined argument. The seed is bracketed by ordinary frozen
rounds; existing cofinality transports the full recursive table induction
to actual ordinary grammar observations. No stable row, periodicity test,
recursive equivalence, or selected capture is an external oracle in the
final `observations_iff` / `language_translation` theorem.

`LastCodewordRecursiveExamples` checks an actual mutual 0→1→0 call chain:
parent capture `(a#)^3`, child `aa#`, grandchild `#^2`, followed by return
and reuse of the whole child and parent strings. The actual arguments
therefore change counts 3→1→2 and header lengths 2→3→1 at runtime. Both
ordinary strategies accept the complete input and reject short parent or
child copies and unequal child headers. A separate source continuation
with an empty literal loop is undefined at every ordinary stage and has
no finite observations on either generated grammar.

The source family still requires the designated last-preserving argument
and leading shifted replay, a shared header, and one retained capture per
user row. The independent recursive header extension follows below. This
is not a transformation of arbitrary first-order Par grammars; general
argument/capture shapes, multiple independent captures, and general
Par/Seq equality or separation remain unresolved.


### Independent recursive headers with unbounded capture counts

`LastCodewordHelpers` and `LastCodewordHelperGrammar` remove the shared
header's call-free restriction. The existing `RecursiveCodeGrammar.Header`
provides a valid independent nullary helper component and a prefix-code
certificate for the header's actual stabilized evaluation. The new
compiler installs these helpers, the unary verifier V, and all recursive
user rows. Neither header lengths nor the number of words captured by
B=(A;&A)* are fixed by the grammar or bounded by the theorem.

`lexical_environment` proves that a nullary lexical expression ignores its
caller's retained environment even before stabilization and at arbitrary
query positions. The existing actual helper floor initializes the nullary
component; `stable` proves that one further ordinary round stabilizes the
whole parameterized verifier row for every held string. The combined
frozen selection includes both the nullary helpers and this unary row;
it does not incorrectly treat V as an independent nullary helper.
`lexical_table` and `syntax_eval` identify actual header, argument, and
verifier evaluations with the standalone component's physical table.
Nonproductive helper recursion is included, not replaced with failure.

The previous successful-capture local entry equation works for any sound
table and environment-independent header, so it applies directly to these
actual helper computations. Prefix-failure seeds and recursive row
induction then preserve the same full retained strings through arbitrary
user sequence, choice, predicates, repetition, and mutual user calls.
`stable_eq`, `observations_iff`, and `language_translation` remove the
intermediate clocks and give ordinary fixed-grammar preservation on every
unchanged original input. No helper agreement, recursion equivalence,
periodicity test, or capture value is supplied by the user in the final
theorem beyond the independent component and its code certificate.

`LastCodewordHelperExamples` uses the actual recursive header
`R <- 'a' R 'b' / eps; A <- R '#'` alongside a nonproductive helper cycle.
Ordinary evaluations verify captures `(aabb#)^3`→`ab#`→`#^2`, mutual calls,
return and reuse of the entire parent/child strings, rejection of short
copies and unequal child headers. Choosing the nonproductive helper as
the header makes the original argument undefined at every physical source
stage and leaves the generated Seq grammar without a finite observation
on every input.

The remaining source restrictions are the designated last-preserving
argument B and leading shifted replay A;param0, a shared independent
header (not a header depending on held values or user rows), and unary
user captures. General source argument/capture shapes, multiple independent
captures, and general class equality or separation remain unresolved.

### Preserve an input-selected stop before later codewords

`SelectedCodewordVerification` and `SelectedCodewordGrammar` extend the
unbounded-count route to `S=A;&(A;G)` and `B=S*`, with an arbitrary pure
condition G. The condition may stop B before the maximal run of A ends;
its result is evaluated by the original argument, not selected by a new
search or a grammar-fixed count. Each successful S consumes exactly one
actual A codeword and guarantees another A at its endpoint. A successful
nonempty B therefore supplies its own word trace and final header, even
when later headers are unequal or G stops early.

The Seq helper is now `V(u)=(&S;u)*;!S;u`. It shares the original step's
stop test rather than demanding that A fail after the replay. Starting
after the first captured A, its repetition follows the remaining original
S trace; the final u checks the one remaining header. Prefix-freeness
proves that it succeeds exactly when the shifted replay of the whole
original capture succeeds. The empty-run case is selected separately.
The generated entry is `&B; (!S / &V(A)); F(B)`, where source F has body
`A;param0;b` and target F has body `A;b`. The original whole capture is
retained for all later uses by b. Preflighting B before V preserves an
undefined original stop condition, including when V could otherwise
reject earlier on unequal headers.

`physical_agreement` proves full partial equality at every pair of
positive ordinary table stages, for every original suffix. The ordinary
`observations_iff` and `language_translation` then preserve every finite
observation and the same original-string language. No count, chosen
endpoint, run witness, or verifier oracle is an input to the generated
syntax. G may contain ordinary repetition, predicates, and choice, so
undefined conditions and nullable loops are included in the theorem.

`SelectedCodewordExamples` demonstrates the method boundary on
`a#a#aa#?a#`, with A=`a*;#` and G=`!'?'`. B captures only the first `a#`;
the source then matches `a#a#`, consumes the later unequal `aa#` in its
continuation, and reuses the retained `a#` after `?`. Both new ordinary
grammars accept, while the previous maximal-run verifier rejects the
later unequal word. Further kernel examples check counts zero and three,
short and unequal copies, an undefined condition after earlier unequal
words, and an undefined continuation. An empty successful step is proved
undefined at every table and position.

The standalone compiler uses a pure shared header and condition, with a
call-free parameter-using continuation. Extensions to mutual user recursion
and independent recursive headers and conditions follow below.
Arbitrary argument expressions, arbitrary capture shapes, dependent
headers/conditions, multiple independent captures, and general Par/Seq
class equality or separation remain unresolved. The verifier counterexample
above distinguishes verification methods, not language classes.


### Selected stops across mutual user recursion

`SelectedCodewordRecursive` keeps the same B=(A;&(A;G))* capture and V
syntax while allowing arbitrary user sequence, choice, predicates,
repetition, and mutual calls in the continuation. A and G remain pure;
both the unbounded word count and each header's length are input-selected.
Every user row retains its whole original capture, passes a newly selected
B to each recursive call, and recovers the old capture on return. There is
no word-count argument or changed representation of the held string.

Zero-word capture is a material initialization case. If A fails at entry,
B succeeds with the empty capture and the new `!S / &V(A)` guard succeeds
through !S. Nevertheless, both actual user bodies must fail on their A
prefix. The previous source-only prefix seed and uninitialized target user
row therefore cannot be used unchanged. The new compiler seeds actual
prefix failures on both sides: source A;param0 and target A. `seed_entry`
relates the two seeds through the actual selected-stop probe, including
its successful-zero case. Applying the already proved entry equation to
an empty-literal loop proves this seed relation without assuming a final
header where none exists. Both seeds are bracketed by ordinary frozen
rounds; neither gives a negative answer for a genuinely undefined prefix.

`tables_shifted` proves the full recursive row relation with these two
seeds and the physically stabilized unary verifier. `stable_eq`,
`observations_iff`, and `language_translation` remove the intermediate
clocks and preserve ordinary finite observations and the language of the
same original strings. The output is a fixed ordinary Seq grammar.

`SelectedCodewordRecursiveExamples` verifies a mutual 0→1→0 chain with
captures `(a#)^3`→`aa#`→`#^2`. Every capture stops before its final header
and a later unequal header consumed only by its continuation; return
reuses the whole grandchild, child, and parent captures. Both ordinary
grammars accept, reject short parent/child copies and unequal replayed
headers, and accept a variation with an empty grandchild capture. A
separate example confirms the real zero-capture/header-failure seed on
both sides. Undefined stop conditions are preserved for every table and
environment, while a nullable-loop continuation is undefined at every
ordinary source stage and has no finite observation on either side.

This compiler retains the guarded-star argument shape, leading A;param0
replay, pure shared A/G, and unary user captures. Its independent recursive
header/condition extension follows below. Arbitrary source arguments and
capture shapes, conditions depending on held values, and multiple independent
captures remain open, as does general Par/Seq equality or separation.


### Recursive conditions preserve the selected capture endpoint

`SelectedCodewordHelpers` and `SelectedCodewordHelperGrammar` allow both
A and G to call a valid independent nullary recursive parser component.
The code certificate concerns A's actual canonical helper evaluation;
G may use arbitrary lexical sequence, choice, predicates, repetition,
and nullary helper calls. Neither may inspect the retained value or call
the parameterized user rows. Users still recapture B=(A;&(A;G))* and keep
the entire selected capture through mutual user recursion and return.

`LastCodewordHelpers.stable_unary` generalizes the existing stability
proof to any parameter-using helper expression over the independent
component. The original last-header stability theorem now specializes
this lemma. The selected verifier has the same actual floor: initialize
the nullary component, then perform one further ordinary round for its
unary row. This proves stability for every retained value, rather than
treating the parameterized row as independent or supplying a semantic
verifier table. Actual selected rows determine the canonical lexical
computations on each side, including the two frozen round-zero tables
used to compute their actual failed-prefix seeds.

The successful-argument entry equation requires only a sound actual table,
header code certificate, and environment independence of A and S; these
follow from the installed lexical component. The two-sided seed relation
therefore extends to recursive headers and conditions without assuming a
final successful header in the empty-capture case. The recursive table
induction and both seeded clocks' ordinary cofinality yield `stable_eq`,
`observations_iff`, and `language_translation` for the same original
strings and ordinary fixed grammars. The generated syntax contains no
input-dependent word count or selected endpoint.

`SelectedCodewordHelperExamples` uses A=`R;'#'`, with
`R <- 'a' R 'b' / eps`, and G=`&A`. The stop condition thus actually calls
the independent recursive parser too. It succeeds on `aabb#` and rejects
`aab#`. Ordinary executions select captures `(aabb#)^3`→`ab#`→`#^2`,
consume later unequal words only in their continuations, restore and reuse
parent/child captures, reject short or unequal copies, and accept a case
with an empty grandchild capture. Both actual seeds handle zero captured
words with a failed initial header. Nonproductive recursion is tested
separately in A and in G: the respective source start is undefined at
every ordinary stage, every input, and every valid position, and the
compiled target has no finite observation on any input. The G example
uses a nullable header, so an undefined condition cannot become an empty
successful iteration or a finite star stop.

The guarded-star argument shape, leading shifted replay, shared independent
A/G, and unary captures remain restrictions. General argument/capture
shapes, headers or conditions depending on held values or user rows,
multiple independent captures, and general Par/Seq equality or separation
remain unresolved.


### Codeword control and disjoint retained parts

`CodewordControlFilter` moves beyond the designated guarded-star argument.
Its finite `Expr` syntax permits header tokens, epsilon, arbitrary tests,
sequence, prioritized choice, negation, and nested ordinary star. `render A d`
is the original parser. The generated `filter A d` compares every consumed
codeword with a retained runtime word while preserving the original parser's
chosen branches and exact endpoint. Each node preflights its original parser;
choice locks the original successful arm, and star checks the original stop
condition after comparison. An unequal word cannot turn into a different arm
or an earlier successful stop. Empty-success loops remain undefined.

The local `success` theorem derives a concrete codeword list from any actual
successful original trace; it does not take a decomposition oracle as input.
`replay_success` then identifies the complete partial source replay with the
filter followed by a one-word replay at the original endpoint. This uses the
prefix-code shift lemma to reject nonuniform captures. For uniform captures,
commuting the initial word with the consumed list gives the exact replay
endpoint. The continuation represents the original whole capture by the
concatenation of two disjoint retained values via `wholeView`; it can use the
whole value repeatedly, inside tests and recursive call arguments in the
local theorem. No header need succeed after the original argument endpoint.

`CodewordControlGrammar` constructs ordinary fixed grammars for the source
argument `B = A;render A d` and unary source body `A;param0;b`. The target's
binary rule retains the two consecutive values from `[A,render A d]`, and
its body is `param0;wholeView b`. A unary verifier checks `filter A d` after
capturing A. The target entry is `&B;&Verifier(A);Body(A,render A d)`.
The first preflight preserves undefined original arguments before any
comparison can reject them. With a Pure prefix-code header, Pure control
tests, and a call-free parameter-using continuation, `physical_agreement`
proves full partial equality at every pair of positive ordinary stages.
`observations_iff` and `language_translation` preserve the same original
strings and all finite observations, with no assumed successful argument.

`CodewordControlExamples` checks input-selected header lengths and word
counts, the actual disjoint capture pair, reuse of the whole captured string,
short/unequal copies, committed choice and committed star counterexamples
to naive comparison, successful nested repetitions with multiple inner
iterations, undefined nested repetitions for arbitrary tables and positions,
and undefined original arguments/continuations in the actual grammars.

This is a new argument-control compiler, not yet an integration with the
previous recursive-user/recursive-header compiler. Its shared independent
prefix-code header, leading source replay, mandatory initial header capture,
and Pure tests/call-free continuation remain restrictions. Arbitrary source
argument shapes, held-value-dependent control/header parsing, independent
multiple source captures, and general Par/Seq equality or separation remain
unresolved. Two target parts represent one original source capture; this is
not a theorem for two independent original captures.


### Codeword control with mutually recursive binary Seq rows

`CodewordControlRecursive` connects the preceding control compiler to an
arbitrary finite family of mutually recursive unary source users. The same
finite control and Pure prefix-code header are shared across those users;
user continuations can contain sequence, prioritized choice, negation, star,
new captures through user calls, and arbitrary later uses of the retained
source parameter. In the target, each user has two parameters containing
the first captured header and the remaining control-selected capture.
Source parameter occurrences become `wholeView` expressions over both parts.
Recursive calls obtain a fresh pair; returning restores the caller's pair.
The source and target renderers insert the actual argument and verifier calls
at each call site rather than requiring manually annotated body leaves.

`Parameters` relates the evaluator for the whole source word with the view
of its disjoint target parts. `entry` derives local entry equivalence from
an actual successful header and control trace, with an arbitrary first-order
continuation and sound actual table. `prefix_identity` specializes this to
the two leading prefixes. Both recursive tables seed only real prefix
failures: the source seeds `A;param0`, the target seeds `param0`. The exact
identity relates the seeds even when verification rejects before querying
the target user row. The unary filter row is physically stable after one
ordinary round. `tables_shifted` and `evaluator_eq` then preserve the view
relation at every recursive stage; ordinary cofinality of both actual seeded
tables proves `stable_eq`, `observations_iff`, and `language_translation`.
These final theorems use the original unmodified strings and fixed ordinary
grammars, with no assumed table relation or supplied trace decomposition.

`CodewordControlRecursiveExamples` executes mutual recursion with capture
counts 3→1→2 and header lengths 2→3→1. The actual target pairs are
`(u,u²)`→`(v,eps)`→`(w,w)`. Returning through both callers reuses the entire
original parent captures. Short parent/child copies and unequal child
captures are rejected. A separate header uses genuinely nested star at every
recursion level and has both ordinary execution checks and all-input
observation equivalence. Failed initial headers, early replay failure,
undefined original arguments under arbitrary tables/environments, and a
looping continuation undefined at every ordinary stage are checked too.
A nullable header with an epsilon control successfully captures two empty
parts and preserves an empty whole capture.

This closes the user-recursion gap for the finite codeword-control compiler.
It still requires a shared independent Pure prefix-code header and Pure
control tests, the initial source `A;param0` replay, and one original capture
per source call. Recursive header helpers, control depending on held values
or user rows, arbitrary original argument shapes, and independent multiple
source captures remain open for this compiler. General Par/Seq equality or
separation is still unresolved.


### Recursive helpers inside codeword control: actual entry and seed bridge

`CodewordControlHelpers` removes the Pure-header/test requirement from the
local two-part entry proof. `Control n` permits tests built from an installed
independent nullary recursive component. Structural proofs show that rendered
controls are lexical and generated comparisons use only those helpers and
the retained word. `stable` freezes the actual unary comparison row one round
after the helper component stabilizes, using `stable_unary`; it does not
install a semantic oracle as a rule.

`argument_success` derives the first actual header and both consecutive
captured parts from the original successful argument. `argument_entry` then
preserves the complete partial entry result with arbitrary first-order
continuations. `physical_lexical_at` supplies lexical agreement from actual
ordinary tables at every stage after the helper floor. In particular,
`physical_argument_entry_seq` crosses the Par/Seq entry-position boundary
between arbitrary installed grammars and arbitrary extra ordinary rounds,
with parameter-using continuations that may themselves call the independent
recursive helpers. The theorem takes an actual successful source argument,
not a trace decomposition, a capture-shape assumption, or a supplied table
relation. `prefix_identity` and `seed_entry` give the exact leading-prefix
and finite-failure-seed equations needed for recursive user-row integration.

`CodewordControlHelperExamples` uses A=`R;'#'`, with
`R <- 'a' R 'b' / eps`. Its nested control tests A and A;A, so the header,
control tests, and continuation all actually use the recursive component.
Ordinary table executions keep `ab#ab#` as `[ab#,ab#]`, reuse the whole value
under both conventions, extend the header to `aabb#`, reject short copies,
and reject an unequal committed `ab#aabb#` capture. The general actual-entry
corollary applies on every input and every stabilized pair of ordinary
stages. Nonproductive recursion is tested separately in a control test and
in the header on every input, ordinary stage, valid position, and retained
environment; argument/verifier undefinedness is preserved.

This section proves the recursive-helper entry and seed bridge. It does
not yet compose it with `CodewordControlRecursive`'s full user-row induction,
and it is not a new recursive-helper language translation theorem. That
composition, held-value-dependent header/control evaluation, arbitrary
original argument shapes, and independent multiple source captures remain
open. General Par/Seq equality or separation remains unresolved.


### Recursive helper control inside mutually recursive users

`CodewordControlHelperGrammar` completes the preceding composition. A
single generated grammar contains the independent nullary header/test
helpers, the unary comparison verifier, and mutually recursive users.
Source users retain the whole argument A;D; target users retain consecutive
A and D captures and reconstruct the source value through parameter views.
Actual helper tables determine both prefix-failure seeds. Induction over
user stages preserves the split environments, and ordinary-table
cofinality gives all finite observations and the same original input
language in fixed ordinary grammars.

`CodewordControlHelperGrammarExamples` combines the recursive balanced-word
header and nested recursive control tests with two mutually recursive
users. Actual captures change from three words to one to two, including an
empty second target value, and the parent value is reused after return.
Kernel executions reject short parent/child copies and unequal captures.
A nonproductive header stays undefined for all inputs, valid positions,
environments, and ordinary stages; neither grammar has finite observations.

The preceding local-only composition gap is therefore closed. The shared
independent helper/header/control discipline, source leading A;param0,
and one original unary capture remain restrictions. Held-value-dependent
header/control evaluation, arbitrary original argument shapes, independent
multiple source captures, and general Par/Seq equality or separation remain
unresolved. All 33 additional public theorem guards use standard axioms.


### Retained context in codeword-control comparison

`CodewordControlFilter.success_environment` generalizes the comparison
induction from `[u]` to `u::E`, with arbitrary additional retained values.
Tests, choices, negation, and nested repetition execute in that same
environment. The header can also inspect it, provided its actual successes
are certified codewords. A successful raw run produces its actual word
sequence; the filter keeps precisely that run when every word equals u.
`replay_success_environment` connects this to the original whole-capture
replay and the two consecutive target parts, preserving partial outcomes
of the continuation. Existing unary theorems specialize these results to
empty E. Raw failure and undefinedness use the existing environment-general
`filter_fail` and `filter_none` lemmas.

This closes a local semantic restriction, not the fixed-grammar context
transport problem. `CodewordControlEnvironmentExamples` makes the latter
precise. On `a#aa#?`, a retained `?` test stops before the unequal second
word and comparison succeeds; deleting the context consumes that word and
comparison fails. A quantified theorem rules out any context-independent
result for that same input and comparison word in this construction.
Simply adding the parent parameter as a Seq argument fails too: Seq must
match its literal at the new input position. A nullable repetition changes
from undefined to finite success if the retained test is erased.

Thus the next grammar construction must actually preserve or encode the
caller context inside its verifier. Replacing it with the comparison word,
erasing it, or appending a parameter argument is insufficient. These
obstructions concern those specific construction choices, not arbitrary
Seq grammars; general Par/Seq equality or separation remains unresolved.


### Adjacent comparisons keep parent control in the caller

The preceding context transport obstruction can be avoided locally by
moving comparison into the original caller rather than moving the parent
into a unary verifier. `AdjacentCodewordControl` checks each consumed
codeword against the bytes immediately following it. An ordinary unary
Seq rule with body `param0`, called with `[A]`, captures the current header
and replays it after that header. Lookahead makes the comparison zero-width;
it does not receive or inspect the caller's parameters.

For codewords u followed by ws and remaining input r, `Linked` checks all
adjacent pairs and the final word against r. `linked_replay` proves these
checks equivalent to the original whole capture u++ws.flatten matching
ws.flatten++r. The final comparison is essential: the shifted source replay
needs one extra copy after the selected argument. Zero remaining words and
empty codewords are included without assuming positive consumption.

The inline filter preserves raw-node preflight, prioritized branches, and
greedy stopping tests. Its success theorem derives the actual word sequence
and checks `Linked` for arbitrary finite sequence, choice, negation, tests,
and nested star in the original environment E. Raw failure and undefinedness
are preserved before comparison. `argument_checks` identifies the shifted
replay predicate, and `entry` preserves the complete partial continuation
result with the whole capture represented by two consecutive target values.
`physical_compare` and `physical_entry` discharge the comparison premise
using actual ordinary Seq tables at every positive stage in arbitrary
first-order grammars containing the replay rule.

`AdjacentCodewordExamples` provides fixed source and target grammars whose
parent is freshly captured from input. The same child input captures one
or two words depending on whether its parent is `a#` or `#`. Both ordinary
executions accept, and both reject short copies and an unequal word. Actual
target evaluation retains `[a#,[]]` or `[a#,a#]`. A nullable parent test stays
undefined through original-argument preflight.

This establishes the local entry mechanism and concrete dynamic-parent
executions, not all-input equivalence of those example grammars or a full
recursive compiler for parameter-dependent control. Next, replace the old
whole-control unary verifier in the user-row induction with this caller-side
filter, preserving parent environments through parameter views. Arbitrary
original capture shapes, independent multiple captures, and general Par/Seq
equality or separation remain unresolved. All 15 new public theorem guards
use standard axioms or none.


### Actual parent-dependent calls and all-input parent restoration

`AdjacentCodewordCalls.physical_agreement` connects the local adjacent
entry to actual Par and Seq calls in possibly different first-order
grammars. It works at arbitrary rule addresses and every pair of positive
ordinary stages, on every input, valid position, and retained environment.
The header is a shared independent Pure prefix-code parser. The codeword
control and continuation are call-free first-order expressions, but the
control tests can inspect any retained caller parameters. There is no
manually supplied comparison oracle: an actual unary Seq replay rule
discharges the adjacent comparison premise.

The proof first preserves original-argument failure and undefinedness.
On success, actual source argument evaluation determines both capture
parts. Original-argument preflight, adjacent entry, and ordinary rule-body
lookups give complete partial equality. Source and target do not need the
same table stage. Surrounding grammars may have other first-order rows;
the theorem imposes only the specified user/comparison rows and the
call-free control/continuation restriction. `stable_result_eq` transfers
agreement after any fixed stage offset to the stable partial result.

`AdjacentCodewordExamples` now follows the child with `?;param0` in the
parent, reusing the original parent after return. The two accepting inputs
are `#@a#a#a##!a#a#?#` and `a#@a#a#a##!a#?a#`. A short parent copy, short child
copies, and unequal codewords are rejected by both ordinary executions.
The input-selected parent changes the child's actual one-/two-word
capture; no literal parent is baked into the grammar.

The earlier example's all-input gap is closed: `child_agreement` applies
on every input and every parent environment, `root_agreement` handles the
fresh outer capture and return, and `all_inputs` proves all finite success
and failure observations agree on the unchanged original input. The
resulting fixed target grammar recognizes exactly the source's language.
Early-stage equality is unnecessary; stable correspondence uses the
ordinary-stage offset of two.

This still does not compose parent-dependent control with arbitrary
mutually recursive user continuations or recursive header helpers. Those
remain the next compiler integration, alongside arbitrary original
argument shapes and independent multiple captures. General Par/Seq
language-class equality or separation remains unresolved. All eight new
public theorem guards use only standard axioms.

### Parent-dependent control through mutually recursive user rows

`AdjacentCodewordRecursive` removes the call-free continuation restriction
from the adjacent-comparison translation. Its source and target are fixed
finite grammars. User tails can mutually recurse, sequence, choose, negate,
and repeat, while control tests inspect the current caller's retained
parameters. Every finite observation and the recognized language are
preserved on the unchanged original input, including failure and
undefinedness. The source remains unary; the two target arguments are
parts of that one original capture.

The source call captures `B=A;D` and its user body begins with `A;param0`.
The target first preflights the original argument and the adjacent filter
under the caller's whole-value view, then calls a binary user with
`[A,wholeView D]`. That user replays the first part and continues with
both parts viewed as the source whole value. An ordinary unary `param0`
row compares adjacent codewords; the parent is never copied into a new
Seq argument or passed to the comparator.

The recursive row relation uses the actual captured codeword trace and
the source whole-replay prefix condition. It does not assume that D has a
parent-independent canonical value. Both prefix seeds include failures
from their actual leading replay, so a failed comparison remains finite
failure at the seed rather than becoming undefined. Simultaneous evaluator
and row induction establishes correspondence at every seeded stage.
Ordinary-table cofinality then gives the stable partial result, all finite
observations, and language equality.

`AdjacentCodewordRecursiveExamples` exercises mutual recursion 0→1→0,
whole capture counts 2→1→2, and actual Seq pairs `(u,u)→(u,eps)→(v,v)`
for `u=a#`, `v=aa#`. Parent tests choose a shorter child; a different
parent chooses the longer grandchild. On return, each original whole
capture is reused. Short parent, child, and grandchild copies and unequal
words are rejected. A nullable parent test leaves the original argument
undefined under arbitrary recursive tables on both sides.

The remaining restrictions are explicit: A is a shared independent Pure
prefix-code header, D is shared call-free codeword control, and every
source user begins with A followed by replay of its single whole capture.
Recursive header/helper integration for parent-dependent control, arbitrary
original argument shapes, independent multiple captures, and the general
Par/Seq equality-or-separation question remain open. The 37 new public
theorem guards use standard axioms or none.

### Different explicit arguments at each recursive call site

`AdjacentCallsiteRecursive` removes the single shared D restriction from
the parent-dependent recursive compiler. Each call site carries its own
codeword-control argument, including different arguments to the same
callee. Argument tests can inspect the current parent. The generated
source calls remain unary, while the target splits that one capture into
two consecutive Seq arguments. The header A remains shared.

`Body H` records the ordinary first-order body constructors and a per-call
`Argument H`. Each argument is A followed by its own codeword control;
the stored proof checks only call-free argument syntax, allowing retained
parameters. `sourceExpr` directly emits ordinary source calls containing
those actual argument expressions. For syntactically scoped bodies,
`source_syntax` and `source_eq_original` identify the proof's source with
that direct original grammar exactly. `original_observations` and
`original_language_translation` then preserve every finite observation and
the recognized language of that original grammar on unchanged strings.
Both grammars and starts are explicitly proved first-order. This is still
a restricted source family, not a decoder for arbitrary first-order PEGs.

The recursive table relation uses captured traces rather than the chosen
argument syntax, so different call sites can share the same user row.
The existing adjacent-prefix argument applies to each call's own control,
with caller-side parent views and ordinary unary comparator executions.
Simultaneous evaluator and row induction, prefix seeds, and cofinality
close the complete fixed-grammar correspondence. No compatibility premise
requires the different call-site controls to choose the same trace.

The example calls user 0 with a two-word argument at the root and a
three-word argument in the grandchild, passing through user 1 with a
parent-dependent one-word capture. Actual target pairs are
`(u,u)→(u,eps)→(v,v²)`, with `u=a#` and `v=aa#`; the original parent values
are reused after return. Short copies are rejected. The dynamic argument
also chooses different endpoints under different retained parents. An
undefined later argument node remains None for every pair of ordinary
source/target stages even when earlier words are unequal.

All 43 new public theorem guards use standard axioms or none. Remaining
constraints are a shared independent Pure prefix-code A, call-free
codeword control in each argument, one original capture per call, and
source users beginning with A;param0. General original argument shapes,
arbitrary user entry bodies, recursive header/helper integration for this
parent-dependent construction, independent multiple captures, and general
Par/Seq equality or separation remain unresolved.

### General replay arguments mixed with shifted codeword users

`MixedAdjacentRecursive` connects the existing arbitrary-argument replay
translation and the parent-dependent adjacent translation inside one
mutually recursive grammar. A replay source row begins with `param0`;
its target removes that replay and keeps one whole capture. A shifted
source row begins with `A;param0`; its target keeps the two consecutive
parts used by adjacent comparison. Every source user is unary; target
arity is one or two according to the user kind.

An actual argument to a replay user may have arbitrary supported body
syntax, including retained parameters, literals, consuming sequence and
star, prioritized choice, predicates, and recursive calls to either kind
of user. It need not be a codeword sequence, call-free, or independent of
the parent. Each shifted call still uses its own `A;D` argument, where D
is call-free codeword control whose tests can read retained parameters.
Only shifted calls require the shared independent Pure prefix-code A.

Argument compilation uses the caller's parameter view, rather than the
callee's view. The table relation has two parts: any actual consumed
prefix relates a replay source row at its original position to the unary
target at the argument endpoint, while the adjacent codeword trace relates
a shifted row to its binary target. Simultaneous evaluator/table induction
handles recursive argument calls as well as user tails. Actual prefix
seeds and comparator freezing preserve finite failures and undefinedness;
ordinary cofinality gives stable partial equality and all observations.

`MixedAdjacentSyntax.sourceExpr` directly emits ordinary source calls with
explicit actual arguments, including nested recursive arguments. The
syntactic `WellTyped` condition checks only callee existence and entry
kind. For well-typed rows and start, `source_eq_original` is exact grammar
equality; `original_language_translation` preserves the unchanged string
language and proves that both grammars and starts are first-order. This
remains a specified source family, not a normal form for all Par grammars.

The mixed example sends a shifted user's whole parent plus a fresh colon
and a completed shifted child call as the argument of a replay user.
That non-codeword capture survives another shifted call and is reused in
full on return, followed by reuse of the outer shifted parent. Kernel
executions accept this input and reject short outer and inner copies.
Further executions cover a replay user inside another replay user's
argument, empty capture, and calls under predicates. An empty-progress
argument stays None under arbitrary tables, environments, inputs, and
positions, before either callee body is entered.

All 42 new public theorem guards use standard axioms or none. General
Par/Seq equality or separation is still unresolved: arbitrary original
user bodies need not have either leading-replay shape, shifted arguments
are still codeword controls, and independent multiple source captures and
recursive headers for the parent-dependent adjacent method remain open.

### Origin control over mixed replay and shifted leaves

`MixedOriginControl` removes the obligatory leading replay from the
**whole source user body** for the mixed compiler. Each body is a finite
plan of prioritized choice, negation, and positive guards over leaves.
A leaf still has shape `param0;tail` or `A;param0;tail`, but one codeword
user's plan may combine both shapes. Negation can return to the original
caller position before the actual argument's endpoint. Consuming sequence,
star, and recursive calls remain available inside every tail and general
replay argument, including calls whose own bodies use origin control.

The translation first normalizes Par origin control into the existing
mixed compiler's leaf rules. It preflights the actual argument and then
expands the plan into calls to those rules, recomputing the same argument
at the original caller position. This ordering preserves failed and
undefined arguments even when the body is a negation. Codeword arguments
may feed either leaf kind. General arguments may feed ordinary replay
leaves; `Valid` checks this rule-kind condition and leaf existence only.
All leaf bodies may mutually recurse through the original control users.

An ordinary-round simultaneous induction relates each original control
row to its plan evaluated on normalized leaf rows. The evaluator proof
also covers calls inside arguments. Call-free argument and prefix syntax
has grammar-independent evaluation, including retained-parameter tests.
The resulting complete partial equality at every ordinary Par round gives
stable equality and all finite observations. Composition with
`MixedAdjacentRecursive` then produces a single fixed first-order Seq
grammar preserving the unchanged original string language. No semantic
row relation, capture decomposition, or parser equivalence is a premise
of the final translation theorem.

`MixedOriginSyntax` emits ordinary calls with explicit actual arguments.
Its `WellTyped` condition checks callee existence and argument kind.
`source_eq_original` proves exact equality with that original grammar;
`original_language_translation` proves both original first-order facts
and the fixed first-order Seq translation for all input strings.

Kernel executions combine a negative test of an ordinary replay leaf,
a shifted branch, an ordinary fallback, mutual recursion, and a shifted
call inside a general argument. They preserve the entire captured general
argument and outer parent after returning, reject short inner and outer
copies, and select the ordinary fallback when its delimiter is present.
A negative shifted user returns at the original caller position after
capturing two codewords; a short actual argument still fails. Empty-loop
general arguments are None under arbitrary source, normalized Par, and
Seq tables, environments, input strings, and positions, even for a
negative callee plan. All 34 new public theorem guards use standard axioms
or none.

This closes origin choice/predicate composition for the mixed method,
not arbitrary source-body normalization. Plans do not support arbitrary
consuming composition or repetition between leaves; those operations are
inside leaf tails. Shifted arguments still have the specified `A;D`
call-free codeword-control shape with a shared independent Pure prefix-code
A. Recursive headers for parent-dependent adjacent comparison, independent
multiple source captures, and general Par/Seq equality or separation
remain unresolved.

### Nested consuming bodies over runtime shifted and ordinary leaves

`MixedBodyLeaves`, `MixedBodyForm`, `MixedBodyStar`, `MixedBodySyntax`, and
`MixedBodyCompiler` connect the earlier guarded continuation and nullable
star normalization methods to runtime codeword shifts and mixed recursive
arguments. The source is now a tree of replay leaves, prioritized choice,
negation, consuming sequence, and ordinary star, with arbitrary nesting.
Its leaf list, continuations, control plans, global offsets, and recursive
source grammar are generated from that tree. A caller does not supply a
normal form or semantic replacement-body certificate.

The two ordinary source leaf shapes remain `param0;tail` and
`A;param0;tail`. Their tails are arbitrary supported mixed bodies, including
retained parameters, general recursive arguments, and calls back into the
original nested-body users. A codeword user's tree can mix both leaf kinds.
A general-capture user's tree has ordinary replay leaves only. The
`Ordinary` source-syntax check is preserved by normalization, and
`valid_of_source_kinds` automatically derives the generated control-family
kind and address conditions. There is no Consumer or Closed prerequisite
on a sequence or ordinary star operand.

Sequence distributes its continuation into selected output leaves while
retaining original leaves as guards. Thus a later failure or undefined
result cannot reopen a successful shorter alternative. Both runtime
shifted and ordinary leaves retain their entry kind when copied. The
same parameter environment is used throughout the inline continuation.

A negative output under star can succeed without consuming and therefore
make the original star undefined. `MixedOriginControl.Part` now also has a
synthetic `stuck` leaf, whose source and compiled syntax is the ordinary
expression `eps*`. It is evaluated directly at the origin, independently
of the actual captured word, rather than being forced through a replay
prefix that might fail. This preserves undefinedness even when the
captured word cannot be replayed at the current position. Argument
preflight still runs before the whole callee plan. The nullable-star
transformation freezes negative outputs through this divergence guard,
then uses the existing guarded greedy-star factorization. The zero-step
continuation is a predicate returning the current origin. Nested stars
and nullable positive replay leaves retain their original partial results.

Local full partial equality uses sound physical tables only to justify
valid endpoints and the guarded star rotation. Source and normalized
recursive grammars have identical arities; induction proves equality of
all ordinary Par tables, including calls within arguments. Stable
observation equality then composes with `MixedOriginControl` and the
mixed adjacent compiler. `source_eq_original` proves exact equality with
a grammar containing the original ordinary calls and the original nested
body before normalization. `source_language_translation` exposes the
fixed first-order Seq language translation on unchanged strings with
source entry-kind and call well-typedness checks only.

The main kernel example puts both leaf kinds in an inner star, sequences
that star with a delimiter replay, repeats the sequence in an outer star,
and finishes with a shifted replay outside both stars. Its actual mutual
recursion includes a shifted call inside a general parent-plus-colon
argument, another shifted child, and full general-parent and outer-parent
reuse on return. A second outer iteration takes zero inner iterations.
Both original Par and generated Seq accept; both reject a short outer
copy. Further executions check that a failed continuation does not retry
a longer shifted alternative, that a negative star operand may return at
the original origin or stay undefined, that argument failure is preserved,
and that nested stars remain undefined.

This closes arbitrary nesting of choice, negation, sequence, and star
**over these replay leaves**, not arbitrary Par body syntax. For example,
ordinary closed consumption followed by use of an unrestricted capture
is not automatically a replay leaf of either kind. Shifted arguments
still have the specified call-free `A;D` codeword-control shape; A is a
shared independent Pure prefix-code parser. Independent multiple original
captures, recursive headers for the parent-dependent adjacent method,
general inverse translation, and general class separation remain open.

### Partial final runtime codewords: an experimental fixed grammar

`PartialCodewordCapture` studies the previously uncovered argument
`B = (A;&A)*;a*`, with `A = a*;#`. For `u = a^k#` and
`w = u^n a^k`, consider the original strings `u w ! w`. The source has one
unary rule `A;param0;!;param0;EOF`, called with the actual argument B.
Unlike the last-codeword-only argument, B ends inside the last runtime
codeword. The same captured value is used after shifted replay and again
after `!`.

`argument_at` proves the actual B endpoint for every k,n at any matching
input suffix, arbitrary grammar, table, strategy, and caller environment.
`actual_capture` identifies the captured prefix as exactly w.
`captured_not_whole` proves that for k>0 it is not any whole power of u.
These are general Lean proofs; they do not prove the target translation.

A candidate fixed Seq grammar first captures `a*` in a lookahead call and
compares every following run with that value. Its comparison must end at
`!`. A prefix-only check was falsified by `#a#!#a`: the source rejects,
while the initial Seq candidate accepts. Both the false positive and the
corrected rejection are kernel-checked.

After the preflight, the long branch captures `a*` and
`#;(A;&A)*;a*` as two consecutive arguments. Its body is
`#;param0;!;param0;param1;EOF`. This reconstructs the original w from the
two pieces for later use. A separate guarded unary branch handles n=0;
the branch guards prevent fallback after a committed long-branch failure.
The grammars contain no length/count parameters. Lean checks six concrete
accepting executions, including empty, short, and multiword captures.

`scripts/experiments/partial_codeword_capture.py` evaluates these exact
fixed grammars independently, preserving the original caller environment
when evaluating successive Seq arguments. It compares both results with
the separate language description `u^(n+1) a^k ! u^n a^k`. Exhaustive
strings over `{a,#,!}` of length at most 9 (29,524 cases), plus 6,155 longer
generated/mutated strings for 0<=k,n<=8, pass. These checks are finite;
they do not establish the unbounded family or all-input equivalence.

The next obligation is the target's all-input result and exact split
capture, including malformed runs and copies. The preflight currently
uses the concrete `!` continuation to select the replay endpoint; an
arbitrary continuation or recursive user cannot simply replace it.
General shifted arguments, full observation preservation, recursive
integration, and the original class equality/separation goal remain open.

### Actual split captures and the entire unbounded positive family

`PartialCodewordExecution.split_arguments` now evaluates both actual Seq
arguments at an arbitrary matching suffix, with the same original caller
environment E for each. For positive source word count n+1, the first
capture is `a^k` and the second is `# u^n a^k`. Their concatenation is
exactly the original `u^(n+1) a^k`; neither the new first argument value
nor an assumed capture endpoint is supplied to the second argument.
`actual_split` applies this to the ordinary input origin.

`source_body_at` and `split_body_at` connect the actual replay endpoints
to the same continuation environment. The latter uses the existing
`wholeView` rebind theorem for two pieces. `bodies_eq` preserves complete
partial results for every first-order continuation, including undefined
or failing continuations. This is a local equality under the same
grammar, strategy, and table; it is not a recursive Par/Seq row theorem.

The actual preflight is now proved by induction for every k,n.
`input_rotated` relates the original input to `a^k (# a^k)^(n+1) ! w`;
`check_at` proves the greedy comparison endpoint and its final `!` test.
`preflight_execution` uses the real stage-one Seq table. Both the binary
long branch and the unary zero-count branch are connected to their
physical rule queries and later whole-capture reuse.

`source_execution`, `target_execution`, and `family_observations` prove
that the two single fixed grammars accept `input k n` for **all** k,n,
including zero/empty captures. This replaces the finite-only evidence
for the unbounded positive family. All 15 new public theorems have
standard-axiom or axiom-free guards.

What is still required is a converse on arbitrary input: ideally
`SObs source Par sourceRoot x (some [])` and the corresponding target
statement should each be equivalent to `exists k n, x = input k n`.
The converse must derive uniform runs and the final copy from actual
capture and replay behavior, and reject malformed runs, delimiters,
and copies. The present positive family and local body bridge do not
establish this. Full finite-failure/undefinedness correspondence,
arbitrary caller continuations through preflight, recursive integration,
general inverse translation, and class separation remain open.

### All-input language equality for the partial-codeword pair

`PartialCodewordClassification` closes both converses on arbitrary original
strings, with no supplied word length, word count, alphabet restriction,
or well-formed-input premise. Both `source_language` and `target_language`
are equivalent to `exists k n, x = input k n`, where `u=a^k#`,
`w=u^n a^k`, and `input k n = u w ! w`. Thus `language_eq` proves exact
accepted-language equality for these two fixed grammars. Malformed runs,
delimiters, and final copies cannot produce a complete successful parse.

On the Seq side, `check_inverse` extracts the count and marker endpoint
from the actual greedy checker trace. `run_shape` derives k from the real
first argument; the unary/binary body inverses validate the entire final
copy and EOF. `target_inverse` joins those facts through the actual calls,
including the guarded zero-word branch.

On the Par side, `source_body_inverse` derives the input equation from
actual scanner/replay/EOF success. The actual argument supplies its
captured prefix and, via `argument_stop`, a suffix that cannot begin with
another a. `stopped_overlap` applies the existing general periodic-overlap
theorem and proves that this greedy stop forces the final partial-codeword
phase to have length k. It therefore derives the same w and n without
assuming an intended argument shape or uniform codeword trace.

This settles accepted-language equality for this candidate, not full
finite-failure/undefinedness correspondence or arbitrary continuations.
The preflight still uses a concrete ! marker; the converse is not a
recursive row relation or a general inverse compiler. Removing that
marker dependence and composing real partial captures with recursive
user continuations remain central obligations for the original general
Par/Seq equality-or-separation goal. All 19 new public theorem guards
use only standard axioms (or a subset thereof).

### Marker-free preflight from actual source captures

`PartialCodewordPreflight` replaces the final `&!` comparison test with
`!A` before the final held a-run. The checker body is now
`('#';param0;&'#')*; '#';!A;param0`, with the same `A=a*;#`.
It tests the actual end of the maximal scanner run, independently of the
syntax of the continuation. In particular the continuation may start
with more a characters: those are allowed when the next scanner still
fails, and must not be excluded by a final `!a` test.

`source_prefix_shape` derives the uniform prefix, actual captured value,
and terminal scanner failure from the real original argument and initial
replay on any input and valid position. General periodic overlap and the
argument's greedy a-run stop yield the uniform shape; the last-preserving
capture endpoint yields the scanner failure. Neither fact is an input
assumption. `source_to_preflight` then proves the real stage-m+1 Seq call
succeeds to exactly the same endpoint, even in an unrelated grammar and
clock with the generated checker rule.

`check_inverse`, `preflight_inverse`, and `preflight_to_source` derive
the reverse direction. `preflight_iff_source_prefix` proves all-input,
same-endpoint equivalence between this physical Seq preflight and the
original Par capture followed by its initial scanner/replay. It includes
zero complete words and empty values. No alphabet restriction, uniform
input assumption, or semantic row oracle is supplied by the caller.

`argument_at`, `split_arguments`, and `bodies_eq` now work with an
arbitrary following suffix and actual terminal scanner failure. Both
sequential arguments still use the unchanged caller environment. The
body bridge preserves complete partial continuation results for every
first-order continuation under the same grammar, strategy, and table.
Kernel examples exercise a-leading continuations with whole-capture
reuse and undefined empty-star continuations; malformed prefixes fail
before the undefined continuation is reached. A finite differential
experiment compares five continuations on all 9,841 strings of length
at most 8 over {a,#,!}, for 49,205 complete-result comparisons.

This closes the concrete marker dependence of the entry verifier, but
is not yet an all-input recursive source/target user-row simulation.
The whole generated grammar family with arbitrary recursive
continuations still needs its ordinary-clock relation and both entry
branches integrated, including failures/undefinedness before the
continuation. The general inverse compiler and Par/Seq class
comparison remain unresolved. All 18 new public theorem guards use
only standard axioms or none.


### Partial-codeword captures through mutual recursion

`PartialCodewordTotality`, `PartialCodewordEntry`, and
`PartialCodewordRecursive` discharge the outstanding ordinary-clock
simulation for this concrete capture family. The source uses
`A=a*;#`, actual unary argument `B=(A;&A)*;a*`, and user bodies
`A;param0;tail`. A nullary call in a template means a fresh actual
source call with argument B. The fixed target has checker rule 0 and
a binary/unary rule pair for each source user. It does not depend on
the input or captured word/count.

The new totality proofs establish finite results for the actual source
argument, initial replay, and marker-free checker at every valid input
position. Each checker repetition consumes a #, so its totality does
not impose any termination condition on the following continuation.
Together with the earlier two success directions, this yields exact
failure correspondence before entering the continuation. Both actual
Seq capture branches are then reduced to the source whole-capture view.
A successful long-branch call whose continuation fails or remains
undefined cannot fall back to the short branch.

`PartialCodewordEntry.transfer` transports the complete partial result
between different source and target grammars and clocks, assuming only
the continuation evaluator relation and the actual generated rules.
The clock-zero theorem supplies the shared undefined seed.
`PartialCodewordRecursive.calls_agree` and `evaluator_eq` discharge the
continuation relation by simultaneous ordinary-clock and expression
induction. For every input, valid position, retained environment, and
ordinary clock, the rendered expressions have identical complete
partial results. Sequences, prioritized alternatives, predicates, and
stars preserve this relation, including undefined empty-consuming
repetitions. No semantic row oracle remains in `evaluator_eq`.

`stable_eq`, `observations_iff`, and `language_translation` connect those
iterates to all finite observations and one fixed first-order Seq
grammar on exactly the original strings. This includes finite failures
and absence of finite observations, rather than accepted strings alone.
The recursive examples run actual user 0 → 1 → 0 with captures a#a, aa,
and ##; both parents reuse their whole capture after returning. The same
grammars handle empty captures and reject short parent/child copies.
An empty-star continuation has no result at any ordinary clock on either
side, as proved with a quantified clock rather than finite sampling.

Scope remains explicit: this compiler handles the stated concrete A/B
and the mandatory initial scanner/replay, with one source capture per
call. Template nullary calls expand to exactly this B; they do not
represent arbitrary original nullary calls. Singleton template arguments
now denote recursive caller tests as described below. Higher-order and
three-or-more-argument template calls render as failure.
Arbitrary source arguments, bodies without that initial replay, mixtures
with the other capture compilers, and multiple independent captures are
not covered. The general Par/Seq equality-or-separation question remains
open. The next generalization must preserve the actual argument choice
and its failure/undefinedness, rather than assuming a periodic value
shape or a total checker for arbitrary parsers.


### Caller-dependent recursive tests inside the actual argument

The partial-codeword compiler now permits a singleton template argument:
`call i [test]` expands on the source side to the actual unary call
`call i [&render(test);B]`. The target evaluates `&render(test)` at the
same caller origin and environment, before its marker-free preflight and
capture branches. The test may consume internally, use parent parameters,
call any user (including the same user), nest guarded calls, and use
choice, predicates, or stars. It returns to the original position before
capturing B. The actual source argument may now fail or remain undefined;
its totality is no longer assumed by the complete recursive compiler.

`ArgumentGuard.call_eq` proves the extraction of that actual argument
test for any unary Par callee, any argument parser, table, environment,
and position. Its complete partial equality requires neither a pure nor
a total test or argument. The generated compiler uses B as that argument;
only B's earlier totality theorem, not the guarded argument's totality,
is used inside the capture entry transfer. The expression induction
translates the test at the current ordinary clock; the user-row induction
still handles the callee continuation at the preceding clock. Thus
`evaluator_eq` and all observation/language theorems now cover tests with
real user recursion without a new row or parser correspondence oracle.

Kernel checks show parent a#a selecting child a, child a selecting
grandchild aa, both returns with the original held values, and a nested
argument test that invokes user 0 before actually invoking user 0.
Changing only a caller's held a to b changes acceptance to finite failure
on the same input and callee in both grammars. An empty-star test stays
undefined for all inputs, valid positions, environments, and arbitrary
user tables, even when the following B/preflight would reject immediately.
The ordering of the test before entry checking is therefore essential.

This removes the total-argument and caller-independent-test restrictions
for the stated capture family. The captured value is still selected by B
when the test succeeds. Consuming arbitrary argument prefixes/suffixes,
independent multiple captures, bodies without the mandatory initial
scanner/replay, and a general Par-to-Seq compiler remain unresolved.


### Recursive tests at the actual capture endpoint

The same compiler now accepts `call i [before,after]` as template syntax
for one actual source argument `&render(before);B;&render(after)`.
The second test runs at B's selected endpoint with the unchanged caller
environment. It is not a second source argument or an independent capture.
On the target side, the tests are `&render(before)` followed by
`&(B;render(after))`, before the existing checker/capture branches.
Both previews return to the caller origin. A succeeding preview lets the
same pure B choose the same held word; no test is moved to the wrong
physical endpoint or supplied the callee's new capture environment.

`ArgumentGuard.suffix_call_eq` proves a more general normalization:
`call i [arg;&test]` and `&(arg;test);call i [arg]` have identical complete
partial results for every unary Par callee, argument, test, table,
environment, and position. Neither purity nor totality is required;
the repeated argument evaluation uses exactly the same environment and
table. `look_sequence_congr` then transports the preview and continuation
relations across strategies/grammars. In the concrete compiler, B's
context independence and endpoint validity let the expression induction
translate the after test at its actual endpoint. The existing ordinary
user-row induction closes the callee relation; the full evaluator,
finite-observation, and unchanged-string language theorems all cover
nested before/after tests and user recursion without extra semantic
premises.

New kernel executions pass captures a → aa → aaa#aaa through user
0 → 1 → 0 and restore the two parents after returning. Parent-held a
versus aa changes the actual endpoint test's result on the same input;
putting that test at the original caller position fails instead.
Another endpoint test parses a fresh user invocation before the real
outer call. Short endpoint copies and returned copies are rejected.
`undefined_after_capture` proves, for every input/valid position/caller
environment and arbitrary pair of tables, that an empty-star post-test
remains undefined even when the callee prefix would otherwise reject.
The target cannot run its preflight before that post-test.

The captured value after successful tests is still the value selected
by concrete B. Consuming changes to that value, general first-use
positions in the body, multiple independent captures, and the full
Par/Seq class comparison remain unresolved. These preview equations
supply exact handling of zero-consuming argument conditions; they do not
justify erasing arbitrary consuming parts of an argument.

### Caller-controlled lengths of partial codeword captures

`ControlledPartialCapture` replaces the fixed argument B with
`B_G = (A;&(A;G))*;a*`, where A is still `a*;#`. G is evaluated in the
original caller environment at the actual lookahead endpoint. It may
read retained parameters or invoke recursive users. Changing G or the
parent can change the successful captured value, rather than merely
rejecting the value selected by the old B.

`source_prefix_shape` derives the uniform partial-codeword shape from
the actual B_G capture and successful A/param replay on every input.
It does not require the later scanner to fail: G can stop earlier while
more, possibly unequal, codewords remain. `peel` preserves all partial
results after the first successful iteration. `split_arguments` uses
that equality to justify the actual Seq arguments `[a*, #;B_G]`, both
evaluated in the unchanged caller environment. Their captures concatenate
to the exact original value at the same selected endpoint. `entry` then
preserves arbitrary first-order continuations through the two-piece view
after a successful first iteration and source replay. Immediate failure
of the iteration selects the zero-iteration run; an undefined test
remains undefined rather than choosing a shorter capture.

`ControlledPartialPreflight` keeps G in the caller's traversal and checks
each consumed A against the immediately following input with a unary Seq
helper. A second unary helper captures the final a-run v and checks #;v.
This final rotated comparison replaces the old maximal-run condition.
The exact trace theorem derives the consumed codewords and final run
from execution, with comparison premises discharged by ordinary positive
Seq tables. `partial_decode` proves uniqueness of the complete-word and
partial-run decomposition; `physical_sound`, `physical_complete`, and
`physical_iff` identify filter success exactly with the actual source
scanner/whole-capture replay. `physical_result` also preserves finite
failure after successful capture, and `undefined` propagates argument
undefinedness before comparisons. The filter reports the original capture
endpoint; the subsequent replay has its separate endpoint.

Kernel executions on one input capture a#a#a or a#a solely by changing
the retained parent. On `a#a#a#aa#!?a#a`, the parent-dependent stopping
test leaves the later unequal aa# available to the continuation. The
original source and the candidate Seq grammar both accept and reuse a#a;
the old maximal-run preflight rejects the valid source prefix. Short
copies are rejected, and the candidate also handles zero full words and
an empty final run.

Scope at the local-preflight checkpoint: these all-input theorems compare the real argument
and replay in the same grammar/strategy/table context, using physical
Seq helper rows. The local entry theorem likewise uses one context.
The candidate's complete call executions above are finite kernel checks,
not a general Par/Seq translation theorem. A cross-grammar recursive row
relation translating G, complete call transfer including the zero branch,
and composition with the earlier compiler remain to be proved. Concrete
A, the B_G argument shape, one capture, and the initial A/param replay
remain restrictions. The recursive connection below closes this checkpoint's
call-transfer and row-correspondence gaps. General Par/Seq equality or
separation is unresolved.

### Recursive caller-controlled lengths and complete call transfer

`ControlledPartialEntry.transfer` now joins the physical preflight and
both actual Seq capture branches across different grammars, strategies,
ordinary clocks, and caller environments. The sole argument is the actual
B_G capture. The positive branch passes `[a*, #;B_G]` to a binary row and
restores the full captured value through `wholeView`; immediate iteration
failure passes the actual a-run to a unary row. The callee tail receives
exactly the original whole value at the original replay endpoint. Finite
prefix failure, undefined stopping tests, and arbitrary continuation
failure/undefinedness are preserved. The guarded branches cannot retry a
different capture after a continuation fails. `preflight_zero` and `zero`
prove the actual ordinary-clock-zero seed without supplying frozen rows.

`ControlledPartialRecursive` discharges both premises of that transfer.
It uses template `call i []` for a source call with G=eps and `call i [G]`
for a source call with `B_render(G)`. The latter is one actual captured
argument: G is a stopping test in the original caller environment, not an
additional capture. G can contain retained parameters, calls to the same
user or other users, nested controlled calls, choices, predicates, and
stars. The source user bodies are `A;param0;render(tail)`. Target rows 0/1
are the two unary comparison helpers; each user gets binary/unary rows at
2i+2/2i+3.

Structural recursion handles G at the current caller clock, while
ordinary-clock induction supplies the callee continuation at the previous
clock. `evaluator_eq` establishes complete partial-result equality at
every ordinary stage for all caller environments and valid positions.
`stable_eq`, `observations_iff`, and `language_translation` then preserve
all finite observations and the language of unchanged original strings
in one fixed first-order Seq grammar. No argument/replay/filter/recursive
row relation remains as an extra premise in these final theorems.

Kernel executions follow a real 0→1→0 chain with captures aa → a#a → aa
and reuse both parents after returning. In another example the stopping
test calls user 0 before the actual user-0 invocation: the first probe
succeeds and the second fails, selecting a#a, which the actual callee
reuses later. Parent-held two versus three codewords changes the returned
endpoint on the same input in both generated grammars. Short parent,
child, and grandchild copies are rejected. The recursive compiler also
accepts zero-full-word and empty captures. An empty-star stopping test
on two real headers remains undefined at every ordinary clock on both
sides.

The restricted recursive family is now proved, beyond the preceding
shared-context and finite-execution results. Concrete A=a*;#, the B_G
argument shape, one capture, and the initial A/param replay remain
requirements. Calls with two or more template arguments render as
failure; they do not express independent source captures. This compiler
has not been combined with the earlier before/after-test or mixed-body
compilers. Arbitrary consuming arguments, general initial body positions,
independent multiple captures, and general Par/Seq equality or separation
remain unresolved.

### Caller-selected fragments before the end of an a-run

`ControlledFragmentReplay` investigates the next boundary directly:
`B_(G,H) = (A;&(A;G))*;H`, with A=a*;#. H may select a proper prefix
of the final a-run, rather than consume its greedy maximum. The argument
can therefore end on an a, invalidating `argument_stop` and the old
immediate-# target body.

`linked_fragment_iff` proves a general prefix-code equivalence for a
complete-word trace followed by any fragment. `trace_replay_iff`
specializes it to an a-fragment followed by the remaining a-run and #;
it does not equate the fragment length with the initial run length.
`physical_tail_compare` implements the new local comparison using an
ordinary unary Seq helper with body A;param0. The actual H is evaluated
in the original caller environment; after capture the helper consumes
the remaining a-run and #, then compares the retained fragment.

`physical_preflight_iff` recovers the full-word trace from the actual
star execution and proves success equivalence of the physical Seq
filter and the original whole replay. This theorem assumes successful
star/H executions, an a-only captured fragment, and a remaining run
ending in #. It is a local conditional result: failed terminal scans
and a syntax-derived all-input condition on H have not been discharged.
Original argument failure and undefinedness are propagated before the
comparison, including a universally undefined empty-star H.

`split_arguments` proves that three consecutive real Seq arguments
`[a*, #;(A;&(A;G))*, H]`, on the positive first-iteration branch,
retain exactly the original whole capture. All three evaluate in the
unchanged caller environment. `wholeView_eval` restores that value
throughout any first-order continuation with complete partial results.
The three pieces represent one source capture, not independent captures.

Kernel executions select a or aa inside aaa, accept and later reuse
aa#a captured inside an aa run, and combine the earlier full-word stop
with an independently selected final fragment. They exercise zero-word
and empty fragments, longer traces, malformed/short copies, and show
that the old immediate-# body rejects at this actual early endpoint.
Both concrete grammars and the proposed entry are first-order.

The proposed entry's recursive call transfer, all-input failure cases,
and composition with the earlier recursive/mixed-body compilers remain
unproved. General Par/Seq equality or separation remains unresolved.

### All-input preflight for a syntax-selected final fragment

`ControlledFragmentPreflight` discharges the preceding local capture and
delimiter premises for H_J=(a;&J)*. J is a caller-side test, including
parent-dependent or recursive first-order expressions. Successful
iterations consume exactly one a; failing tests stop before consuming
that iteration's a. `fragment_shape` derives the actual a-only capture
from this syntax for arbitrary tables, without a capture-value oracle.

`block_prefix_after_fragment` and `terminal_of_replay` recover the
remaining a-run and # from an actual successful source replay. The
latter does not assume that the complete-word trace or the fragment was
maximal. Conversely `tail_result` and `physical_trace` recover the exact
physical helper result even when the terminal scanner fails. On a
successful original argument, `physical_range` excludes undefined or
shifted preflight results: only the actual capture endpoint or finite
comparison failure can result.

`physical_iff` now holds on every input after an actual argument success,
with no successful-star, a-only-value, delimiter, trace, or word-count
premise. `physical_result` includes every argument outcome. Original
argument None/failure is propagated first; after a successful capture,
preflight returns its endpoint exactly when the original A/whole-value
replay succeeds, and otherwise returns the same finite failure. This is
an exact caller-position result with ordinary Seq tables and the two
actual comparison rules, not a semantic helper-row assumption.

Kernel executions select a, aa, or empty inside aaa by changing only
the caller's retained word, and reuse the whole value afterward. Inputs
without a valid terminal word, including empty input and a fragment
consuming the entire input, fail finitely. An empty-star J on aaZ stays
undefined before the scanner's finite failure can replace it.

This closes the earlier local preflight premises for this H syntax.
The mandatory source body entry A;param0, one source capture, fixed
A=a*;#, and the specified full-word/fragment argument shape still limit
the construction. Transfer across source/target recursive user tables,
clock-zero seeds, complete call transfer, and a final fixed recursive
grammar language theorem for the new fragment family remain unproved.
General Par/Seq equality or separation remains unresolved.

### Recursive grammar preservation for both stopping controls

`ControlledFragmentEntry` connects the all-input filter to complete
calls. `star_congr`, `fragment_congr`, and `argument_congr` preserve
actual argument results across different grammars, strategies, clocks,
and caller environments when G and J correspond at the current caller
clock. `endpoint_state` derives the actual residual a-run, delimiter,
and retained final fragment at the original replay endpoint; the old
greedy boundary assumption is not needed.

The positive branch performs three actual captures, and its body
A;param2;wholeView(b) reconstructs the whole original value. The zero
full-word branch captures H alone and uses A;param0;b. `branches_eq`
preserves the complete partial result of the real continuation, with
first-iteration guards preventing a failed callee from selecting a
different capture. `transfer` places the continuation correspondence at
the previous callee clock, while both tests remain at the current clock.
`preflight_zero` and `zero` supply the real physical-clock-zero seed
using actual unavailable helper rows, including partial tests.

`ControlledFragmentRecursive` renders template calls with two arguments
G and J into a unary source call whose sole argument is
B_(G,J)=(A;&(A;G))*;(a;&J)*. A singleton template supplies G with J=eps;
an empty template supplies both eps. The generated Seq grammar installs
the actual two comparison helpers and a ternary/unary pair for each user.
The two templates are stopping tests, not independent source captures.

Structural induction treats both rendered tests at the current clock,
including parent parameters, calls to the same user, mutual recursion,
and nested controls. Ordinary-clock induction handles the previous-clock
callee continuation. `evaluator_eq` establishes every partial result at
every ordinary stage for all retained environments and valid positions.
`stable_eq`, `observations_iff`, and `language_translation` preserve all
finite observations and the language of unchanged original strings in
one fixed first-order Seq grammar. No capture-shape, delimiter, input
condition, semantic helper-row, or recursive continuation oracle remains
in these final theorems.

Kernel executions follow real 0→1→0 calls capturing a → aaa#a → aa,
with a recursive user-2 test selecting the middle fragment and both
parents reused after return. A same-user probe fails with a fresh aa
capture but succeeds with a fresh a, stopping the actual call's fragment
before its greedy endpoint. Other examples exercise recursive G probes,
both controls selecting one capture, parent-selected a/aa/empty fragments,
zero-full-word calls, and short parent/child/grandchild rejection.
An empty-star J on aaZ is undefined at every ordinary source/target clock,
before a scanner's finite failure could replace it.

This closes recursive grammar preservation for the specified fragment
family. Fixed A=a*;#, one source capture, B_(G,J)'s argument shape, and
the mandatory A;param0 body entry remain restrictions. Three or more
template arguments render as failure. This construction has not been
combined with earlier mixed-body or independent-header compilers.
Arbitrary consuming arguments, arbitrary initial body positions,
independent multiple captures, and general Par/Seq equality or separation
remain unresolved.

### Consuming control inside the final a-fragment

`FragmentConsumingSyntax.Syntax` removes the final `(a;&J)*` shape from
the local bridge. Its consuming leaves are `eps` and `chr 'a'`; sequence,
prioritized choice, and arbitrary nested star compose them. Positive and
negative tests may contain any first-order expression, including retained
parameters and recursive user calls. This is a syntax restriction on
consumption, not a totality premise. A fragment can fail, be undefined,
stop before the greedy a-run endpoint, or choose different consuming paths.

`shape` derives the actual a-only capture from successful evaluation for
arbitrary tables, strategies, inputs, and caller environments. The generalized
`ControlledFragmentPreflight.physical_iff_of_shape` and
`physical_result_of_shape` expose the comparison argument independently of
its original star shape. `FragmentConsumingSyntax.physical_result` discharges
the shape premise from syntax and preserves the full physical preflight
result on every input and valid position. The missing-delimiter and empty
fragment cases require no separate input-shape assumption.

`FragmentConsumingEntry` carries the actual H through the real three-piece
or unary Seq argument evaluation. Its endpoint and branch theorems recover
the original capture and replay endpoint; `transfer` preserves the complete
partial call result across different grammars, environments, and positive
ordinary clocks. The current-clock G/H correspondence and previous-clock
callee-continuation correspondence are explicit premises. Finite argument
failure is now possible and is handled before evaluating the callee.
`preflight_zero_success` uses the physically absent comparison-helper rows;
`zero` preserves argument failure as well as None at clock zero, provided
the actual source/target arguments correspond at that clock.

Kernel executions accept a mandatory `aa / a` fragment and reuse its entire
capture, reject the shorter-copy input without reopening the successful
`aa` branch, preserve mandatory-fragment failure even at clock zero, and
preserve a consuming fragment followed by an empty-star None before the
missing-delimiter comparison. A syntax certificate also covers nested
consuming choices with parent-dependent recursive tests.

The local call bridge retains explicit current-clock argument and
previous-clock continuation correspondence premises. The recursive compiler
below discharges them for its generated source family. Fixed A=a*;#,
only a-consuming H, one source capture, and the mandatory A;param0 body entry
remain restrictions. General Par/Seq equality or separation remains unresolved.

### Recursive compiler for consuming fragments

`FragmentConsumingRecursive` compiles normal template calls with two
templates G and H into one actual unary Par argument
`(A;&(A;G))*;H`. In contrast to the earlier G/J compiler, the second
template is the consuming fragment itself. A singleton template supplies
G and H=eps; an empty template supplies G=H=eps. Both source and target
are fixed grammars determined by the finite list of user tails.

The syntax-directed renderer has normal and fragment modes. In fragment
mode, eps, chr a, a-only literals, sequence, prioritized choice, and star
remain consuming operations. Tests switch their child to normal mode,
allowing caller parameters, calls to the same user, mutual recursion,
and nested controls. A-only literals are rendered as fixed a-sequences.
Other consuming fragment leaves render as failure. Unknown user indices,
three or more call templates, and higher-order forms also render as failure.
These are source-family restrictions, not equivalence claims for arbitrary
unsupported source expressions.

`render_fragment_syntax` derives the generated fragment certificate.
`evaluator_of_previous` proves normal and fragment partial correspondence
together by structural recursion at the current ordinary clock, and
`evaluator_eq` closes the previous-clock user continuation by clock induction.
At clock zero it uses actual argument correspondence and the fail-capable
zero seed, preserving finite argument failure before any missing callee
row. At positive clocks it applies the full real-call transfer theorem.

`stable_eq`, `observations_iff`, and `language_translation` then preserve
all finite observations and the language of unchanged original strings
in one fixed first-order Seq grammar. No capture shape, input delimiter,
word count, semantic helper-row, current-clock argument correspondence,
or previous-clock continuation correspondence is assumed in these final
theorems. The physical evaluators also agree at every ordinary stage for
every retained environment and valid position, in both renderer modes.

Kernel executions follow actual 0→1→0 calls with a → aaa#a → aa captures,
a mandatory middle fragment stopped by a recursive user-2 test, and
parent values reused after both returns. The real middle Seq arguments
are [aaa,#,a] at the same endpoint; the grandchild captures aa in its own
caller environment. Additional executions cover a same-user test inside H,
parent-dependent H together with a nontrivial G, shorter parent/child/grandchild
copies, successful and committed-failure aa/a choices, empty fragments,
and zero complete words. Mandatory argument failure and a-consuming H
followed by an empty-star None are preserved at every ordinary clock.

This closes recursive preservation for the consuming-fragment family.
The standalone compiler still uses a fixed A=a*;# header, an a-only
consuming fragment, one source capture, and mandatory A;param0 body entry.
The following origin-control extension relaxes that user-body entry shape.
General consuming arguments, arbitrary initial consuming body positions,
independent multiple captures, and general Par/Seq equality or separation
remain unresolved.

### Origin body control with consuming-fragment calls

`FragmentOriginRecursive` combines the consuming-fragment call bridge with
`ReplayControlFusion.Plan` and the generic call normalization from
`MixedOriginControl`. A logical user body is now a finite tree of prioritized
choice, negation, and positive guards over replay leaves. Each leaf has
body A;param0;b, with b an arbitrary normal template. The caller still supplies
one actual argument `(A;&(A;G))*;H`, with the same consuming-fragment syntax
and recursive caller-side tests as above.

The source grammar contains the logical users with these actual body trees,
followed by ordinary unary leaf rules. Generated source calls address logical
users only; the appended leaf rows support a same-clock normalization proof.
The target grammar contains the two comparison helpers and a ternary/unary
pair per leaf. At each target call, an actual-argument preview precedes the
body's origin-control tree of physical Seq entries. No captured value is
presumed at the original position: each leaf's call bridge derives the real
pieces, endpoint, and restored whole value.

`source_call` proves the actual source call equal to its guarded expansion
into source leaf calls at every ordinary clock. At clock zero every leaf row
is absent and the entire control plan remains undefined after successful
argument evaluation; finite argument failure is still preserved first.
The syntactic `Valid` premise only checks that each plan leaf index exists.
There is no input, capture-value, semantic table-row, or totality condition.

Structural induction again treats normal and consuming-fragment templates
together, while ordinary-clock induction handles user continuations.
`evaluator_eq`, `stable_eq`, `observations_iff`, and `language_translation`
preserve all partial results, all finite observations, and the language of
unchanged strings in one fixed first-order Seq grammar. No argument or
continuation correspondence is supplied to these final results.

Kernel executions use real 0→1→0 calls with negative origin guards and
prioritized fallback, retaining a → aaa#a → aa and rejecting short copies.
A distinct negative-body example on a! actually captures a yet returns the
original position; its continuation then consumes the original a! input.
On #, the mandatory argument fails, while omitting the outer argument
preview would let the negative target body succeed. Further executions
preserve undefined arguments before negative bodies, nullable rollback
inside a caller star, and both finite-failure and missing-row behavior at
clock zero.

A logical user no longer has to begin with a consuming A;param0. Its body
may inspect the capture through several origin branches and predicates and
return before the capture endpoint. The replay leaves still require that
entry shape. The next extension normalizes nested consuming sequences over
these leaves; arbitrary initial consuming expressions and general body stars
are still outside the compiler. The fixed header, a-only consuming H,
one source capture, and unsupported-template restrictions remain. This is
not a complete integration of `MixedBodyCompiler` or a general Par→Seq
translation, and no language-class equality or separation is claimed.

### Nested consuming body sequences from source syntax

`FragmentBodyForm.Body` represents actual nested user bodies built from
replay leaves A;param0;b, sequence, prioritized choice, and negation. The
suffix b is an arbitrary normal template, so it may call users recursively,
construct new consuming fragments, reuse the held value, or contain loops.
The body itself is not replaced by a supplied control plan.

`normalize` computes a finite plan and its leaf suffixes. Composition keeps
original leaves as queries and appends continuation copies. It uses
`ContinuationPlan.bind`: a successful alternative is guarded before its
continuation runs, while a negative zero-consuming output invokes the
right body at the unchanged position. The actual copied suffix b;C is
proved equal to sequencing the original leaf with C. `compose_eval` and
`evaluator_eq` preserve the full partial result in arbitrary grammar/table/
strategy/caller contexts, without a Consumer or totality condition.

`FragmentBodyCompiler` gathers these generated suffixes and shifts their
plans into one layout. Its source grammar retains each user's original
nested Body.syntax. `normalized_bodies` and `body_results` prove equality
with the actual generated plan bodies; `headers`, `tables_eq`, and
`evaluator_eq` lift that equality through every recursive grammar round.
The normalization requires no semantic table assumptions, input condition,
or user-supplied body-equivalence proof. Appended source helper rows are
preserved and have the same generated leaf bodies as the normalized grammar.

The generated bounds prove `FragmentOriginRecursive.Valid` automatically.
`observations_iff` composes this exact source normalization with the
recursive consuming-fragment compiler, and `language_translation` gives
one fixed first-order Seq grammar on unchanged strings for every source
user list. No layout, leaf-index validity certificate, capture-shape,
argument/continuation correspondence, or recursive row oracle is left as
a premise of these final results.

Kernel executions sequence a negative left body with a replaying right
body, and run real 0→1→0 recursion where user 1 consumes two separate replay
leaves before invoking user 0. The captures a → aaa#a → aa remain available
after returns, and a short grandchild copy is rejected. A source body
`(leaf(x) / leaf(xy));leaf(!;param0)` rejects a#axya#a!a because its x branch
has already succeeded. The naively distributed alternative of the two full
sequences accepts that input; the generated Seq grammar preserves the
source rejection. A right continuation's empty-star None is also retained
after a negative zero-consuming success.

This extends finite body normalization through arbitrary nesting of sequence,
choice, and negation for the consuming-fragment family. General stars over
these body controls, ordinary bare-param/closed leaf kinds, arbitrary consuming
prefixes before the first replay, unrestricted arguments, and independent
multiple captures remain outside this construction. The fixed A=a*;# header,
a-only consuming H, one actual capture, and per-replay-leaf A;param0 shape
remain restrictions. General Par/Seq equality or separation is unresolved.

### Capture-independent divergence and nullable source body loops

`FragmentStuckRecursive` extends the consuming-fragment origin compiler with
one distinguished leaf at index `tails.length`. Its source body is `eps*`,
independent of the captured value. Ordinary leaf indices still select
A;param0;b. Logical source rows and appended leaf rows agree at every clock,
including clock zero. The Seq expansion previews the actual argument before
executing the divergent leaf: a mandatory fragment's finite failure must
remain failure, rather than becoming undefined. `evaluator_eq`,
`observations_iff`, and `language_translation` cover arbitrary valid finite
origin plans mixing both leaf kinds, recursive argument tests, and normal
continuations. The only new layout premise is a finite index bound `j≤n`.

`FragmentNullableControl.Body` retains actual source `(!e)*` and `(e*)*`
constructors, nested with choice, guards, and negation. `negativeStar`
normalizes the former to a finite plan: a successful negative test diverges
at the unchanged position; a failed test yields zero iterations there.
Double stars normalize to the divergent leaf, using the generic nested-star
result. The local evaluator theorem needs no totality, Consumer, sound-table,
purity, valid-position, or input-shape premise. `tables_eq` proves equality
of all ordinary clock tables between the actual source grammar and its
normalized core; `observations_iff` and `language_translation` compose this
with the fixed Seq compiler on unchanged strings. Finite body-index validity
is checked separately, rather than assumed semantic correspondence.

Kernel examples distinguish origin divergence from a replay-wrapped loop:
on a! the actual argument captures a, but A;param0 fails; the source nullable
loop and generated Seq call are undefined, whereas the incorrect wrapper
finitely fails. On a#a a failed negative test returns the original position
with zero iterations. Mandatory argument failure at clocks 0/1/2 and an
undefined consuming argument precede the body. A real 0→1→0 example runs
these nullable stars inside recursive source rows and restores each parent's
whole capture after returning.

This supplies capture-independent divergent leaves and integrates two
nullable star forms with recursive consuming-fragment capture translation.
It does not yet normalize a general star whose operand alternates between
consuming replay outputs and zero-consuming predicate outputs. This new
compiler has not been composed with `FragmentBodyForm`'s arbitrary sequence
normalizer or with ordinary bare-param/closed leaf kinds. Fixed A=a*;#,
a-only consuming H, one actual source capture, and A;param0 replay entries
remain restrictions. Unrestricted Par/Seq equality or separation remains
unresolved.

### General nested fragment-body stars from actual source syntax

`FragmentStarForm` combines the previous finite sequence normalizer with
capture-independent divergent leaves. A local leaf is `some b` for
A;param0;b or `none` for eps*. Continuation copies append to b only when it
exists: a divergent leaf remains undefined at the original position.
`compose_eval` preserves prioritized branch commitment, including a negative
output followed by a consuming continuation.

For arbitrary control operands, `strict` redirects zero-consuming predicate
outputs to a guarded divergent leaf with `NullableStarControl.freeze`.
`strict_change` and `star_change` preserve the original star's partial result.
The first consuming replay output receives an inline continuation implementing
the remaining greedy iterations, guarded by the complete next iteration.
`loop_eval` discharges the local chain premises using actual generated leaf
expressions. `star_negative` proves that a terminating star already stops
where its operand fails, permitting a final negative test instead of a
special capture-independent epsilon leaf. No Consumer or totality condition
is imposed on the source operand. Its constructor may be any nesting of
leaf, sequence, prioritized choice, negation, and ordinary star.

The local `evaluator_eq` uses sound evaluation tables, a valid input position,
and a call-by-value strategy for the decreasing-parser rotation. These are
discharged in `FragmentStarCompiler.tables_eq` by the actual first-order
core grammar and its ordinary clock tables; they are not supplied as
semantic oracles by callers of `observations_iff` or `language_translation`.

The compiler computes all local suffix lists and plans from the source body.
`address`/`relocate` send local divergent leaves to the single global stuck
index and ordinary replay leaves to their generated helper rows. The
`placed_leaf` proof covers both cases. Source grammar user rows retain the
original nested Body.syntax, including its stars. Header equality, actual
body result equality, and ordinary-clock table equality connect it to the
normalized recursive core. The final fixed first-order Seq grammar preserves
all finite observations and the language on every unchanged input. Finite
layout validity is generated automatically.

Kernel executions cover a syntactically non-Consumer operand that chooses
consuming X branches twice and then finitely stops at Q, zero iterations,
reuse of the full capture after the star, a short final copy, undefinedness
when a negative branch succeeds after a consuming iteration, and nested
body stars. An actual 0→1→0 execution replays aaa#a twice in the child body
star, then captures fresh aa in the grandchild and restores both parents'
whole values after return.

This closes the general body-star and sequence-composition gaps for this
consuming-fragment family. It does not remove the fixed A=a*;# header,
a-only consuming H, one actual capture, or A;param0 entry for each ordinary
leaf. Ordinary bare-param and capture-independent consuming leaves, arbitrary
initial consuming prefixes, unrestricted arguments, and independent multiple
captures remain outside this compiler. General Par/Seq equality or separation
is unresolved.

### Bare and shifted replay leaves in one fragment-capture compiler

`FragmentMixedRecursive.Part` records whether a leaf begins with A;param0
or directly with param0 (a neutral eps is retained in the latter's source
syntax). Both kinds have an arbitrary normal continuation and use the same
actual consuming-fragment argument `(A;&(A;G))*;H`. The source may select
between these entries through origin guards and predicates. A bare leaf
becomes an ordinary unary Seq call evaluating the complete actual argument;
a shifted leaf uses the existing fragment preflight and three-piece/unary
entry. The compiler-generated divergent leaf remains independent of capture.

`bare_transfer` proves ordinary replay fusion for arbitrary first-order
source arguments and corresponding target arguments, including finite
failure, undefinedness, and the clock-zero empty table. Successful actual
argument evaluation determines the exact retained prefix and the same
endpoint reached by source param0. Its continuation receives the complete
value rather than only a fragment. In the recursive compiler, current-clock
argument equality and previous-clock continuation equality are discharged by
structural/clock induction for both leaf kinds together. All normal recursive
calls, including those inside fragment tests, use this shared translation.

`FragmentMixedForm` retains each leaf kind while copying continuations and
normalizing sequence, prioritized choice, negation, and general nested star.
Bare leaves may replay an empty value: the iteration remains undefined if
no progress occurs. `FragmentMixedCompiler` generates the mixed leaf layout,
kind table, relocation, and validity bounds automatically, retains the actual
nested source user bodies, and proves all ordinary call-by-value clock tables
equal to the normalized core. Its final observation/language translation
preserves every unchanged input without supplied semantic table, body,
argument, continuation, layout, or capture-shape assumptions.

Kernel runs switch bare→shifted→bare inside a star and reuse the original a
after its delimiter. A child capture aaa#a switches shifted→bare→shifted,
then makes a fresh aa grandchild capture and restores both parents' values.
Short whole-value copies and final copies are rejected. An empty bare replay
under star stays undefined. A short ordinary choice cannot reopen as a longer
shifted choice when its continuation fails; the naive distribution accepts
the same input rejected by the real source and generated Seq grammar.
Mixed predicate outputs also retain finite stopping versus empty-success
undefinedness after a consuming bare iteration.

This integrates ordinary replay leaves with the new consuming-fragment
argument compiler. The generic bare entry lemma permits arbitrary arguments,
but the final shared renderer still uses the specified fragment argument
family. Capture-independent consuming branches and arbitrary consuming
prefixes before replay are not covered: appending a capture-dependent
continuation to a closed branch requires retaining the capture through that
branch. The fixed A=a*;# header, a-only consuming H, and one source capture
remain restrictions. General Par/Seq equality or separation remains unresolved.

### General actual arguments routed to replay-only users

`FragmentMixedRecursive.replayOnly` checks every query and output leaf in a
logical body's generated finite plan. It accepts only bare replay entries
and the distinguished capture-independent stuck leaf. `replayOnly_sound`
turns that Boolean check into the corresponding finite structural property;
no semantic equivalence, termination, or input-shape condition is checked.

For a single-argument template call into such a user, `render` now passes
the rendered argument itself to the actual unary source rule.
`direct_source_syntax` proves this exact syntax equality. It no longer wraps
that argument as the G test of `(A;&(A;G))*;eps`. The target previews the same
actual parser and distributes its ordinary unary Seq calls across the body
plan. The original two-template calls still construct consuming-fragment
arguments, and users with shifted queries keep their fragment entry path.
Zero-template calls retain their earlier default fragment interpretation.

`direct_call_eq` uses the actual argument result and the existing generic
`bare_transfer` entry theorem to preserve success, complete captured values,
finite failure, undefinedness, and clock zero. The eligibility proof rules
out shifted leaf rows on this path, and the stuck leaf retains argument
preview before divergence. Current-clock structural induction handles the
arbitrary rendered argument parser, including old parameters, fresh literal
stars, and recursive calls to both user kinds. Previous-clock induction
handles each callee continuation. Existing generated-layout normalization,
all-clock source/core table equality, and final observation/language theorems
apply unchanged, without a new user-supplied eligibility premise.

Kernel examples route an actual literal ab into an ordinary user, then pass
through a fragment user holding aaa#a. That child constructs a fresh general
argument from its whole held value, ':', fresh b*, and an actual fragment-user
call consuming a#aY. The new captured value aaa#a:bbba#aY is replayed and
reused after '!', then both parent values return. A short grandchild copy is
rejected. A negative ordinary body returns at the original position even
though its actual ab argument advanced, while argument failure at clock zero
and an undefined empty star precede that body. A selected aa/a general
argument remains committed when its later copy is too short.

General arguments are now integrated for replay-only callees, in the same
recursive compiler as consuming-fragment calls. This does not yet provide
arbitrary arguments to a callee whose body queries shifted replay leaves.
Capture-independent consuming prefixes, unrestricted shifted captures, and
independent multiple source captures remain outside the construction. The
shifted branch still uses fixed A=a*;# and a-only consuming H. General
Par/Seq equality or separation remains unresolved.

### Caller-dependent tests at both ends of a fragment capture

`ArgumentGuard.window_call_eq` combines the origin and endpoint test
normalizations for any actual unary Par rule, arbitrary table/environment,
and arbitrary argument/test parsers. It moves an argument
`&before; a; &after` to caller-origin `&before; &(a; after); call[a]`.
The second preview executes `after` at the endpoint actually selected by a,
then restores the caller origin. No purity, totality, successful-capture,
or input-shape assumption is needed. Failure and undefinedness keep their
original order, and neither preview contributes to the held value.

`FragmentMixedRecursive` now accepts the four surface templates
`call i [before,G,H,after]`. These denote **one** real source argument
`&render(before); ((A;&(A;render(G)))*; fragmentRender(H)); &render(after)`;
`guarded_source_syntax` proves that exact source syntax. The target performs
the origin and actual-endpoint previews before using the existing mixed
bare/shifted fragment entry. Unknown users still reject. Three-template and
five-or-more-template calls remain unsupported. Existing zero/one/two-template
calls retain their meaning.

`guarded_call_eq` preserves the complete partial result at every ordinary
clock, including zero. Current-clock structural induction discharges both
test correspondences, fragment G/H correspondences, and arbitrary recursive
calls inside tests. Previous-clock induction handles callee continuations.
The existing nested-body compiler's source/core table equality and final
observation/language preservation apply unchanged; no caller-supplied guard,
body, table, continuation, or semantic shape oracle is added.

Kernel examples use old parent a in both tests of a child aaa#a. Its endpoint
test consumes parent a and probes an actual recursive user; that lookahead
restores the selected endpoint before capture finishes. The child body uses
mixed bare/shifted iterations, captures a fresh aa grandchild with its own
parent-dependent guards, and restores both parents' complete values. Changing
the old parent to aa makes the endpoint check fail on the same input even
though both origin tests succeed. Origin divergence precedes a failed
capture, endpoint divergence precedes a rejected body, and a finite endpoint
failure remains finite even at clock zero and before a negative body.
A successful aa alternative cannot be reopened as a after its endpoint test
fails; explicitly choosing a would accept that input.

This extends the actual argument syntax within the consuming-fragment
compiler, including parent-dependent recursive checks at both endpoints.
It does not resolve capture-dependent processing after an arbitrary consuming
prefix or arbitrary consuming shifted arguments. A remains a*;#, H remains
a-only consuming syntax, and logical users still have one source capture.
General Par/Seq equality or separation remains unresolved.

### Retaining captures through a stateful consuming prefix

`LoopCaptureSafety` replaces a character-set condition on captured words
with a finite-state loop condition. For a fixed partial deterministic scanner
M and initial state q, an admitted literal word must return M from q to q.
Arguments may combine these literals, old retained parameters, sequence,
prioritized choice, arbitrary nested star, and negative queries. Queries can
contain supported recursive user calls. The caller environment contains loop
words; this invariant is established again by actual successful argument
evaluation at each recursive call. `suffix_shape` and `capture_loop` derive
the captured word and exact scanner resumption equality, without a supplied
successful-capture or suffix-shape oracle. No consuming user call is admitted
outside queries in this argument syntax.

`StatefulLoopFusion` installs the actual compiled finite-state scanner rows
before the unary user rows. Each user body is `scan(M,q); tail`, so the first
use of the held value may occur after an unbounded, genuinely consuming
closed prefix. Tails have arbitrary sequence, choice, predicates, nested
star, parameter use, and recursive unary user calls with checked arguments.
All users share M and q. `Supported` reserves the helper addresses and checks
the finite literal-loop and argument-syntax conditions. No syntax conversion
or new input encoding is used: the very same generated grammar and start
expression work under both CBV strategies for this family.

The scanner rows stabilize at input length plus one independently of user
rows and captured environments. Their physical evaluation is frozen only
for analysis; `helpers_stable` discharges the actual installed-row condition.
Structural evaluator induction and user-clock induction preserve complete
partial results of the frozen tables, including clock-zero user rows.
Physical/frozen cofinality then gives `observations_iff` and
`language_translation` for every unchanged original string and arbitrary
success/failure observation. An empty-success loop remains undefined.

The two-state example alternates a/b transitions, also permits c loops, and
stops at the actual missing-transition boundary. Captures c → cab → cabab
are retained through consuming prefixes, including extra a characters beyond
the capture.
A child argument reads its old c value, runs a fresh `(ab/c)*`, and uses a
negative recursive user probe; the grandchild and both parents reuse their
complete values after returning. `StatefulScannerFastTable.eq_frozen` proves
an executable run-based helper table equal to the actual frozen table;
`physical` transfers its checked results to ordinary physical clocks. Kernel
examples use that equality rather than repeatedly unfolding scanner rounds.
The concrete grammar has an all-input language correspondence theorem, as
well as kernel executions rejecting
short parent/child/grandchild copies. A plain {a,b} scanner consumes past the
real stateful boundary and changes acceptance. A non-loop capture a gives a
Par/Seq difference for this unchanged grammar, showing why the loop check
cannot just be dropped; it is not a class-separation witness.

This supplies a further consuming-prefix family rather than an unrestricted
prefix construction. It is a separate compiler theorem from the mixed
fragment family. General state-changing captures would require carrying the
reached scanner state into the residual prefix; arbitrary PEG consuming
prefixes, general shifted arguments, independent multiple captures, and the
general Par/Seq equality/separation question remain unresolved.

### State-changing captures with checked finite transition actions

`CaptureActionSafety` records a word's action from **every** state of a
partial finite-state scanner, including undefined transitions. Concatenation
composes these finite actions. `Typed` is a syntax derivation for literal
words, param0, sequence, same-action choice, negative queries, and star with
identity-action operands. A successful actual execution derives both the
complete captured word and its exact action. Parent accuracy is needed only
for an actual retained param0 and is re-established after each real capture.
No preselected capture, successful execution, termination, or input suffix
shape is supplied to the final translation.

`infer` computes a candidate action from the actual argument syntax and the
caller's finite action type. `equal` compares actions by enumerating the
fixed finite states; `infer_sound` and `fits_sound` turn the Boolean check
into `Typed`. Unequal-action alternatives and non-identity-action star
operands are rejected by this checker. Negative queries retain the ordinary
parser and may contain checked recursive user calls. Positive consuming user
calls inside arguments remain unsupported.

`StatefulActionFusion` assigns one finite capture-action type to each source
user rule. All source user bodies start with the same compiled scanner
`scan(M,q)`. The generated target keeps the argument, complete captured value,
callee address, and tail, but resumes that prefix in `captureAction(q)`.
`Supported` checks actual calls against the callee's action type using `fits`;
`Valid` also requires the action to be defined at q. These are finite
syntactic/type checks, not semantic equivalence or captured-value oracles.
This removes the return-to-q condition for this typed family. It is a
complementary theorem to `StatefulLoopFusion`: the latter permits varying
full actions as long as they fix q, whereas this new theorem permits a
state change but fixes a full action for each user.

The actual argument action and prefix are derived by structural induction.
User-clock induction relates the source row at its original position to the
target row at the capture endpoint. `run_after_prefix` establishes exactly
the resumption state selected by the computed type. The held value enters
the callee unchanged; its full action supplies the parent information for
new nested arguments. Installed helper stability and physical/frozen
cofinality yield all finite observation correspondence and unchanged-string
language preservation for two ordinary first-order grammars. Neither
physical grammar receives a frozen table or an input-dependent annotation.

Kernel examples capture a → acca → accaa, whose actions require target scan
starts 1 → 0 → 1. A child uses the parent value, fresh c*, a final a, and a
negative recursive user probe. Extra b/ab prefix transitions run before body
uses and both parents' full values return. The concrete grammar has an
all-input language theorem. Short whole-value copies are rejected. On ab!a,
the corrected Seq grammar accepts while simply resetting the scanner to 0
rejects. The words a and ab reach the same state from 0 but differ from 1,
showing why retaining only one endpoint state cannot type later parameter
composition. Same-action a/ac choice stays committed after a later short
copy; explicitly selecting ac would accept. Empty captures and argument
failure/undefinedness ordering, including clock zero, are preserved.

The source user action types are fixed for the finite grammar. Calls whose
actual argument can select different actions need further finite dispatch or
normalization; this is not an unrestricted capture classifier. This family
also requires capture consumption within the source scanner frontier,
a shared finite-state consuming prefix, and unary source users. Integrating
these consuming-prefix families with the mixed fragment compiler, arbitrary
PEG prefixes, unrestricted shifted arguments, independent multiple captures,
and general Par/Seq equality or separation remain unresolved.


### Dynamic scanner capture observation (2026-10-25)

`DynamicScannerCapture` connects partial `StatefulScanner.Machine` transitions
to the existing total `DependentCaptureFilter` observer by adding one absorbing
missing-transition state. `observer_run` and `observer_result` identify the
observer result with actual partial advancement on the whole captured word.
A full observer profile determines the partial action from every scanner state;
`finite_action_cover` covers all actual captured words by finite profiles.

`filter_result` preserves the original Par argument's failure and undefinedness
and filters successful captures by the requested partial transition. Arguments
may have unequal-action choices, nonidentity star operands, retained parameters,
and recursive nullary helpers. `filter_success` derives the actual original
capture endpoint and transition; `filter_resumption` derives the exact original
prefix split and residual scan start from a successful generated filter.
No capture-shape or successful-scan premise is supplied to these conclusions.

`dispatch_result` enumerates finite observer endpoints and invokes just the
continuation for the actual original capture's endpoint. A continuation may
fail or diverge without choosing a different argument capture. It preserves
argument failure/undefinedness before continuation evaluation. The dispatcher
is ordinary first-order syntax when its continuations are first-order.
Kernel examples cover changing-action a*, committed a/aa choice, absorbing
missing transitions, retained ac reuse after a variable-action capture, empty
capture, failed arguments, empty loops, and divergent selected continuations.

This is a local classifier/continuation construction in the installed regular
helper-product grammar at its stable table. Accurate incoming observer metadata
remains a premise (existing environment/profile-guard theorems provide it).
It is not yet a complete stateful user-call compiler: binding new captures,
propagating dynamically selected full profiles through recursive user rows,
physical-clock correspondence for that compiler, and its all-input language
preservation still need to be connected. In particular, observing a missing
transition does not solve captures extending past the original scan frontier.
The general Par/Seq language-class equality or separation remains unresolved.


### Binding dynamic captures to installed residual scanners (2026-10-25)

`DynamicScannerBinding` installs one real unary Seq rule for every finite
observer profile and appends the actual partial-machine scanner block. Each
variant starts at the state decoded from its profile, followed by a
profile-specialized body. The callsite uses the existing actual profile guards
and binds the entire original argument, rather than a bounded proxy for it.
`resume_actual` identifies the decoded state with partial advancement on the
captured word from any scanner start state.

`entry_result` relates an actual Par argument in an independently extended
source grammar to the installed target row, at arbitrary source and target
user stages. `entry_step` unfolds that row: the environment is exactly the
singleton original capture, the selected scanner is the one obtained from
that capture, and the body is specialized by its complete observer profile.
Failure and undefinedness remain ahead of the callee. `recapture_step`
discharges incoming metadata accuracy for a parent specialized by its actual
profile, and repeats the actual binding step for a new child capture.
`scanner_physical` evaluates the selected installed scanner at an ordinary
physical bound; `scanner_prefix_eq` proves exact original/residual scan
agreement when the actual capture is inside the original scan frontier.
`physical` and `observations_iff` connect the installed grammar's user stages
to actual physical tables and all its finite observations. `entry_undefined`
proves undefined source arguments stay undefined at every physical target
clock, even when a specialized callee could reject immediately.

Kernel examples use a single fixed target grammar for odd/even a* captures,
whole child acaa capture followed by restored parent ac, short-copy rejection,
committed a/aa variants, and original-string observations. A recursive source
and generated recursive target execute a → aa → aaa captures with target
starts 1 → 0 → 1, extra scanner transitions, and whole child/parent reuse on
return. Grandchild, child, and parent short copies are rejected on both sides;
the successful recursive target run is transferred to a physical table and
ordinary SObs. This is a concrete recursive execution, not an all-input
language-equivalence theorem for the recursive pair.

The frontier boundary is verified on the actual grammars: capturing a! in
a!a! extends beyond the source scan's stopping point. The source accepts,
whereas the generated residual-entry grammar rejects. Thus this entry
construction cannot be claimed as an unrestricted translation. The next
missing proof is a syntactic guarantee of the scan frontier for dynamically
varying arguments, followed by all-input recursive row correspondence and
source/target language preservation. User calls inside positive argument
parsers, general PEG prefixes, independent multiple captures, and general
Par/Seq equality or separation remain unresolved.


### Checked dynamic captures through whole recursive grammars (2026-10-25)

`DynamicScannerCompiler` and `DynamicScannerCorrespondence` close the
whole-grammar connection for a new dynamic-capture family. Each source user
starts with the same actual partial scanner M/q followed by an arbitrary
body built from literals, primitives, retained parameters, user calls,
sequence, prioritized choice, negation and nested stars. Every user call
carries its own actual argument syntax. The generated target has one unary
rule per logical user and finite full observer profile, and starts its
scanner in the state actually reached by that capture. Incoming full profiles
select the next child's profile before its ordinary Seq capture binding.
Both grammars and both starts are fixed independently of the input.

`TotalCaptureSafety.check` is an executable finite syntax check. Literal
words must have defined transitions from every scanner state; parameters
preserve that property through the actual capture environment. The property
is closed under sequence, unequal-action choice and arbitrary star. Negative
queries consume no capture characters and may fail or diverge. Arguments in
this whole-grammar compiler contain no rule calls; their control may otherwise
mix retained values and new literals freely. `IndependentCaptureControl`
transports their full partial results and inline generated filters between
actual user grammars and clocks. It does not assume successful argument
results or total parsing behavior.

`capture_total` derives the exact physical capture, suffix split and defined
advancement from actual argument evaluation. Structural evaluator induction
and user-clock induction prove every source row at the original position
matches the generated profile row at the actual capture endpoint. Scanner
rows are actual installed helper rows stabilized at input length plus one;
physical/frozen cofinality removes the analysis clock. `checked_observations_iff`
and `checked_language_translation` require only the finite body/start checks.
They preserve all finite observations and the same unchanged original string
language on all inputs, including failure and undefinedness. `undefined_iff`
also identifies absence of a defined result at every ordinary physical clock.
No capture-shape, selected-action, metadata-accuracy, frontier, argument-result
or recursive-row oracle is a caller premise of these final theorems.

The generated mutually recursive example captures a → aa → aaa, chooses
residual states 1 → 0 → 1, consumes extra b transitions, and restores both
parent values. Its concrete ordinary source/target executions and three
short-copy rejections are kernel checked, and `language` covers every input
and every finite observation for this actual pair. The same generated grammar
also accepts even and empty captures. Unequal-action a/aa commits to a on
aa!aa and rejects rather than retrying aa after EOF failure; explicit aa
succeeds. A nullable empty-literal-star argument is undefined on every input
at every ordinary clock on both sides, and argument failure at clock zero is
preserved. The a! frontier-crossing argument from the previous section is
now rejected by the finite syntax check.

This is complementary to the earlier loop-safe and fixed-action families,
not their strict superset: requiring defined advancement from all states
excludes some partial actions those families permit. It removes the fixed
full-action-per-user restriction for this new family. Positive rule calls,
including independent nullary recursive helpers, inside arguments have not
yet been integrated into its whole-grammar proof (the earlier local binding
lemmas still support the independent helpers). Shared M/q, unary logical
users and source scanner-prefix form remain restrictions. General PEG
prefixes, mixed-fragment compiler integration, independent multiple captures,
and unrestricted Par/Seq equality or separation remain unresolved.


### Recursive helper arguments: actual capture safety and relocated scans

`RecursiveCaptureSafety` extends frontier safety to bounded nullary calls.
The finite consuming-path check on the original helper bodies and an
induction on actual physical tables prove `physical_rows`. Recursive calls,
mutual cycles and nullable stars are allowed: no parser-totality assumption
is made. `frozen_capture` derives the complete actual captured word and exact
suffix split at arbitrary frozen user stages. Negative queries retain their
original computation but contribute no characters to the captured word.
`TotalCaptureSafety.suffix_shape_calls` is the shared structural proof; the
previous call-free public theorems keep their statements.

`FrozenCaptureControl` transports retained-parameter control and inline
filters to actual canonical helper computations. Its product parser can be
a proper prefix of the frozen component. `RecursiveScannerHelpers` installs
original parser nodes, their observer products, and relocated scanner rules
in that order, before arbitrary user rules. It proves actual installation,
closed-component validity, stabilization-floor bounds and the relocated
scanner's ordinary run result. No helper result is supplied as advice.

`RecursiveScannerArguments.argument_eq` and `filter_correct` preserve full
partial results across distinct actual grammars and independent user stages.
`capture` derives all-state defined advancement from finite helper-body and
argument checks. `residual_scan` then proves that scanning from the original
position and scanning from the actual capture endpoint in the reached state
meet at the same position. The captured word and its length are not supplied
as separate premises; they come from the actual argument evaluation.

The kernel examples use H = a H c / empty, retain ac before the fresh
recursive capture, and consume acaacc or acaaaccc. Their complete scanner
actions differ. A successful empty alternative stays committed when its
later continuation rejects; using the explicit recursive helper accepts.
A safe self-cycle is undefined at every physical clock on every input.
`combined_residual` instantiates the all-input, all-user-stage residual-scan
theorem for the actual combined helper prefix and arbitrary user extensions.

This closes recursive helper capture safety, inline observer transport and
residual scanner alignment. It does **not yet** extend
`DynamicScannerCorrespondence`'s whole user-row induction, all-observation
or language theorem to these arguments. That composition, positive
parameterized user calls inside arguments, general PEG prefixes,
mixed-fragment integration, independent multiple captures and unrestricted
Par/Seq equality or separation remain unresolved.


### Whole recursive grammar preservation with recursive helper arguments

`RecursiveScannerCompiler` and `RecursiveScannerCorrespondence` now close
the user-row composition left open above. The source and generated target
install original nullary parser nodes, their observer products, relocated
stateful scanners and unary user rules in one actual finite grammar.
Original arguments invoke the original helper nodes; observer products are
queried only by generated target filters. Each user still starts with the
shared scanner from the shared state. Different callsites carry their own
actual argument syntax, including retained parameters, independently
recursive helper captures, sequence, prioritized choice, queries and stars.

`evaluator_of_rows` combines the actual argument and filter results from
`RecursiveScannerArguments` with successful-capture safety and real unary
capture binding. `tables_rows` is an induction on user rounds: each source
row at the original position agrees with its actual captured-word profile
row at the capture endpoint. The source header and generated residual
header reach the same endpoint. Successful captures provide the new
singleton environment and its exact observer metadata; returning to the
parent keeps the original environment and complete retained value.

`observations_iff`, `defined_iff`, `undefined_iff` and
`language_translation` remove the analysis clock using the installed closed
helper component's actual stabilization and physical/frozen cofinality.
The fixed generated Seq grammar preserves all finite observations and the
same unchanged original string language on all inputs. Physical clocks may
differ. The public `checked_observations_iff` and
`checked_language_translation` require only finite node-reference,
consuming-path, body and start checks. They require no helper-row, capture
shape, successful argument, metadata accuracy, scanner frontier or recursive
correspondence oracle. The all-state defined-transition condition on
consuming helper words remains a restriction; it is not parser totality.

The actual mutually recursive example executes users 0 → 1 → 0 and captures
ac → acac → acacac, with residual scanner states 1 → 0 → 1, extra b scans
and full parent-value reuse on return. Both ordinary source and target
tables are kernel checked. Another execution changes the fresh recursive
helper captures from ac to aacc to ac, retaining the whole resulting values
and restoring both parents. Three short grandchild/child/parent copies
reject, with actual target physical failures derived from the all-input
correspondence. An empty argument alternative stays committed on ac!ac and
rejects at EOF; explicitly using the recursive helper accepts. Empty
recursive capture and argument failure at clock zero are also checked.
Repeating H = a H c / empty is undefined at every physical clock on every
input in both generated grammars; the proof derives the absence of finite
helper failure and preserves nullable-success divergence.

`RelocatedScannerFastTable` computes only the installed scanner block
analytically; all other helper, product and user rows still use actual PEG
steps. Its table equals the corresponding actual frozen table and every
finite result is transported to an ordinary physical table. It is used to
avoid re-expanding scanner rounds during kernel examples, not as an oracle
in the language preservation proof.

This removes the no-positive-rule-call restriction for independently
recursive nullary helpers inside this scanner-prefix family. Positive
parameterized user calls inside arguments, general PEG prefixes,
mixed-fragment integration and independent multiple captures are still
unresolved, as is unrestricted first-order CBV-Par/Seq class equality or
separation. Shared M/q, unary users and source scanner-prefix form remain
restrictions. The earlier loop-safe and fixed-action constructions remain
complementary; no unrestricted normalization theorem is claimed.


### Parameterized capture safety and observed scanner handoff

`ParameterizedCaptureSafety` derives the scanner-frontier capture invariant
for calls with arbitrary finite argument lists, including parameterized
calls inside arguments and mutually recursive rules of different arities.
`grammarCheck` checks the actual rule bodies: consuming literals must have
defined transitions from every scanner state, retained parameters must
already be safe, and consuming calls and their arguments must pass the same
check. Queries preserve their original behavior and consume no output;
the check does not assume their termination. Arguments still evaluate in
the caller environment. `par_arguments` proves that all parallel captures
are safe at the unchanged caller position; `seq_arguments` additionally
derives the safe prefix consumed before the callee starts. Induction on
physical table clocks closes the actual rule-row invariant. The proof also
covers actual frozen tables for arbitrary row selections and floors,
without a stability or termination oracle.

`ObservedScanner` and `ObservedScannerDispatch` generate an actual scanner
product with an arbitrary total finite observer. The original scanner alone
determines the frontier: an observer's absorbing failure state does not stop
the scan. Relocated blocks choose the actual final scanner/observer pair,
then execute the corresponding continuation at the actual scan endpoint.
Later continuation failure or undefinedness cannot choose another stopping
point or final state. Both states advance through the whole captured word.
`physical_dispatch_resumption` now derives this handoff from a successful
capture in a finitely checked parameterized source grammar to real relocated
scanner rules in a different grammar, allowing independent clocks,
strategies, retained environments and arbitrary continuations. This is a
conditional local handoff after actual capture success, not yet a complete
call translation including argument failure.

`SequentialCaptureObserver` proves the one-call observer induction step for
actual unary Seq rules. The observer must advance across the actual
argument before evaluating the callee body. When that call itself occurs
inside a fresh argument, the selected profile must describe the entire
call's consumption, rather than only the word passed as its parameter.
The general call theorem still requires a callee product-row relation.
The concrete examples discharge that relation using actual installed
unary rules, uniformly on every input and physical clock, and execute a
nested call retaining `ab#ab` after observing an inner argument `ab`.
The whole value is reused after `!`, then the parent `a` is restored.
Resetting the observer at callee entry, or using the inner argument's
profile for the whole call, rejects in the corresponding kernel examples.

Additional kernel examples distinguish observer failure from the original
scanner frontier, preserve continuation failure and nullable divergence,
check two independent actual argument captures in both evaluation modes,
and prove an actual mutual unary cycle undefined on every original input
at every physical clock. A literal crossing the scanner frontier is rejected
by the consuming-path check, including inside a positive call argument;
the same literal in a query needs no consuming-path restriction.

These are building blocks for parameterized arguments in the scanner-prefix
translation. The new safety theorem requires checked consuming paths in all
rules of its actual source grammar; it does not claim that arbitrary user
bodies with scanner prefixes satisfy that condition. The general Seq call
observer step and scanner dispatch still need a simultaneous recursive
plain/product compiler and row proof for this family. That integration,
general PEG prefixes, mixed-fragment integration, independent multiple
captures in the translation, and unrestricted first-order Par/Seq class
equality or separation remain unresolved.


### Recursive Seq observer products and capture-first scanner fusion

`SequentialRecursiveObserver` closes the recursive row premise of the local
Seq call observer for a finite unary Seq grammar with literal/parameter,
sequence, prioritized choice, negation and ordinary star bodies. Actual
arguments are structurally nested expressions of the same syntax, so they
may themselves call any mutually recursive user and contain arbitrary
control and stars. A fixed generated grammar keeps the original user rules
and adds one unary product row for each user, retained-word profile and
observer entry/exit state. The actual retained word remains unchanged.

The structural evaluator proof advances the observer across each actual
argument before entering its callee, then observes the callee body using
the previous physical-stage row relation. Induction over physical clocks
proves all recursive product rows at once. There is no successful argument,
termination, product-row or metadata oracle in `filter_correct`,
`source_filter_correct` or `select_result`: their checks are finite call
bounds on actual source syntax. The observer is any total finite machine;
no scanner safety condition is needed for this observation construction.
The plain original rows are proved equal to the separate original Seq
grammar at every physical clock. Product rules do not change its partial
results. The same row proof supports installation in a larger first-order
grammar, with actual original and product rule lookups discharged by the
generated prefix.

`SequentialRecursiveScanner` installs those original users and recursive
observer products before actual relocated scanner/observer blocks. Its
`fusion_correct` composes the recursive observer proof, the finite
parameterized capture-safety check and actual scanner dispatch. On every
input it replaces an argument preflight followed by scanning from the
original position with profile selection, consumption of that same actual
argument, and scanning from its endpoint with both states advanced. The
full partial result is preserved, including argument failure/undefinedness,
continuation failure and continuation undefinedness. The continuation and
caller environment are kept. No successful-capture assumption or recursive
row oracle is supplied; the actual source argument result determines which
case applies. Physical scanner availability still requires clock >= p+1.

Actual ordinary source tables execute users 0 → 1 → 0 with retained values
a → ab → abb and both parent returns, then a third user captures the entire
inner call w and reuses it after !, before the original parent a is reused.
The generated physical observer table gives the correct full-call profile;
using only the initial argument a's profile rejects. Additional examples
observe successive calls inside a star with different actual arguments b
and bb, retain the greedy stopping point, and preserve the successful long
branch of an argument choice when its later continuation fails. Explicitly
selecting the short branch is separately checked to succeed. Empty-success
stars inside recursive arguments are undefined on every input at every
physical clock.

In the combined scanner grammar, the whole recursive w captures an odd
number of b's and changes both resumption states. The original scanner
consumes w!w, then ? and the parent's a are consumed. The capture-first
expression reaches the same physical acceptance. An all-input theorem also
keeps a nullable recursive argument undefined before scanning, at every
clock where scanner rows are available.

This closes the full recursive **Seq observer** construction and its local
capture-first scanner fusion. It does not yet close Par-to-Seq translation
for the scanner-prefix user family: that compiler must generate mutually
dependent translated plain rows and their observer products while relating
source Par entries at the original position to target Seq entries at actual
capture endpoints. The Seq observer construction starts from unary source
rules in the stated syntax; the fusion additionally needs checked consuming
paths in that source grammar and safe incoming retained values. It does not
show that arbitrary scanner-prefix user bodies satisfy those checks.
General PEG prefixes, mixed-fragment integration, independent multiple
captures in the translation, and unrestricted first-order Par/Seq class
equality or separation remain unresolved.


## Simultaneous products for mixed replay and scanner entries

`RecursiveScannerProductCompiler` and `RecursiveScannerProductCorrespondence`
close the Par-to-Seq row correspondence left open above. Each unary source
user has an explicitly configured entry: either `param 0; body`, or
`scan(M,q_i); body` for its own initial scanner state. Replay and scanner
users can call each other, including inside actual arguments. Bodies and
arguments permit literals, retained parameters, sequence, committed choice,
negative queries, stars, and structurally nested unary user calls. The
compiler generates both plain and observer-product user rows, indexed by
user number, the complete transition profile of the actual captured word,
and an optional observer entry/exit pair.

Plain scanner blocks and relocated scanner/observer blocks form a common
closed helper prefix. `RecursiveScannerProductHelpers` proves actual
lookups, frozen/physical stability, and capture-endpoint resumption.
`RecursiveScannerProductHeader` either resumes the configured scanner or
removes the exactly replayed prefix; in both cases the product observer
advances through the entire captured word. Structural argument induction
and user-round induction close both target row modes simultaneously. Source
Par rows begin at the original caller position; target Seq rows begin at
actual capture endpoints and retain the complete captured values.

The capture safety check now selects actual rules rather than requiring
every rule in a contiguous initial grammar component to be safe.
`SelectedCaptureSafety` proves successful capture safety for any finite
checked selection, on physical tables and frozen analysis tables, with
arbitrary-arity recursive calls. Every consuming call and its arguments
must stay in the selected set; queries preserve their actual computations
and may use unselected rows. The compiler selects a designated initial
segment of user rules, structurally safe helper blocks, and individually
certified plain scanner states. Its separate structural check
also validates calls nested inside queries.

This avoids requiring unused scanner helpers to consume words defined from
every M state. A partial scanner can have different readable characters in
different states while certified replay users build safe arguments.
Consuming calls into an uncertified scanner user remain rejected when
proving safety of their output. Replay users can now retain arbitrary words,
including characters outside M and profiles reaching the total observer's
sink. Only arguments to scanner entries or explicitly safe replay entries
need the finite selected-rule and literal checks. Root language preservation
starts with an empty environment.

`observations_iff` preserves all finite observations, including failure,
on every unchanged original input. `language_translation` supplies one fixed
first-order Seq grammar and root for the whole source language.
`defined_iff` and `undefined_iff` connect ordinary physical tables with
potentially different clocks. Actual helper stabilization removes the
frozen analysis clocks. None of these final checked results assumes a
recursive row, argument-success, termination, capture-shape, or metadata
oracle.

Kernel examples retain the original scanner-entry cases, including actual
parameterized argument calls, ab/aab state changes, retained ab plus fresh
b captured as abb, parent restoration, short-copy rejection, empty-first
argument commit, clock-zero argument failure, and all-input/all-clock
nullable-argument divergence. Mixed examples follow replay → scanner →
replay calls, create new arguments from retained values inside a positive
parameterized replay parser, query another scanner user, consume an extra
b beyond the argument, and restore all parent values after return.

A partial machine reads b only in state 1. Its helpers fail the old
all-prefix capture check, while the selected user argument paths pass.
The actual mixed grammar captures a → aa → aaa and accepts through the
state-1 scanner's extra b. Configuring that user to start in state 0 instead
stops before b and rejects the same original input. The fixed generated
Seq grammar preserves the correct source language on all inputs.

`ScannerLanguageSafety` additionally certifies entire scanner languages.
A finite relation between states is refined for n² rounds, then explicitly
checked to be a simulation. The soundness proof does not assume that the
iteration converged. When the checked relation relates an initial scanner
state q to every M state, any word whose path from q is defined is defined
from every state. Induction on the actual scanner run derives this property
for its exact consumed word, without inspecting a successful capture first.

`RecursiveScannerProductCapture` connects these certificates to actual
plain scanner rows at every physical clock and retained environment.
Successful short-clock rows lift monotonically to a sufficient clock,
where the actual installed scanner block computes the exact run.
`SelectedCaptureSafety.certified_frozen_rows` combines these concrete
primitive rows with structurally checked recursive user rows. The compiler
now treats individually certified plain scanner states as primitives and
checks every other selected body. The final language and observation
results still require only finite checks; they receive no primitive-row
oracle.

A synchronizing partial machine has only a from state 0 and both a and b
from state 1, with a moving every state to 1. A b word is unsafe, while
every word scanned from 0 is safe. The whole helper block fails structural
safety and state 1 fails the scanner-language certificate, but state 0
passes. An actual positive parameterized scanner call inside an argument
now captures ab, then receives its parent's ab plus fresh a and captures
the longer abaab. Both full values are reused after return. The original
physical grammar accepts and short copies fail; the fixed Seq translation
preserves the whole source language on all inputs. Earlier mixed-entry and
partial-scanner examples remain checked.

`CaptureInputSafety` removes the global safe-environment requirement for
replay users. Entries are `replay`, `safeReplay`, or `scan q`; the first two
have the same actual replay prefix, while `safeReplay` additionally requires
checked safe arguments. A body's check uses its own entry's input-safety
flag. Every nested call is checked, including calls inside queries, but only
callees requiring safe inputs demand a capture certificate. The
open-environment correspondence likewise makes the retained-value safety
premise conditional on the entry. Whole-capture observer profiles remain
accurate for arbitrary words, including sink profiles.

When checking an argument in an arbitrary replay environment,
`CaptureInputSafety.withoutParams` forbids consuming uncertified retained
values while allowing their actual use in zero-output queries. Its
`suffix_shape` theorem derives safe output without assuming that the
incoming environment is safe. In a safe environment the existing selected
capture checker remains available. Thus safe values can still be forwarded
through `safeReplay` users into scanner calls; arbitrary values can be
constructed, passed between replay users, and reused after return. The
final all-input observation, language, definedness, and undefinedness
results take only finite checks, without a new semantic safety oracle.

A mixed example captures an input-dependent z*# through a positive
parameterized replay call, retains z#, constructs z#z for a recursive child,
and reuses both complete values after returning. Those words fail M's
all-state word check. The same arbitrary retained value is queried in the
argument `!param 0; a` to a scanner call, whose new capture is safe. The
scanner consumes an extra b and then reuses its own a; the parent query
cannot be erased, as different retained values change its actual result.
Directly consuming the arbitrary retained value as a scanner argument is
rejected by the finite check. Kernel examples verify longer initial
captures, three short-copy failures, and all-input/all-clock nullable
argument divergence, and instantiate the fixed-Seq all-input language
theorem for this grammar.

The remaining restrictions include unary source users, the stated argument
syntax, replay or scanner entry forms, a common machine M, and finite
capture checks for calls requiring safe inputs. Arbitrary PEG prefixes, mixed-fragment compiler
integration, independently captured multiple source arguments, and
unrestricted first-order Par/Seq class equality or separation remain
unresolved.


## Exact entry-state scanner frontier certificates

`ScannerFrontierCertificate.readable_iff_endpoint` identifies the exact
resumption condition for an arbitrary captured word w and arbitrary suffix:
w is readable from the actual scanner entry q iff the original scan reaches
at least the end of w. `check` tests this condition using the whole-capture
profile already selected by the generated filters. `check_position` expresses
it at actual input positions. `RecursiveScannerProductHeader.argument_frontier`
connects it to every actual source argument success, with arbitrary retained
values and without a capture safety check.

Both `plain_body` and `product_body` now require readability only from the
configured entry, rather than Total M w. The generic entry lemmas use
`entryCheck` on that finite profile; replay entries require no scanner
frontier. The existing complete compiler derives this weaker certificate
from its current stronger checks through `entryCheck_of_safe`.

`covers` separately checks a finite simulation between one scanner start
state and one required target state. Its soundness transports every defined
source word, and `covers_consumed` transports the exact whole word of an
actual scan. It requires neither all-state coverage nor convergence of
relation refinement. `RecursiveScannerProductCapture.scanner_frontier_physical`
derives this certificate for actual installed scanner rows at every physical
clock and arbitrary retained environment, by lifting successes monotonically
to the exact run. No primitive-row safety oracle is an input. A machine that reads b only from state 1 certifies its
state-1 scanner language for entry 1 while rejecting entry 0 and failing
the old all-state scanner-language certificate.

This removes an unnecessary hypothesis from the resumption proof and gives
an exact executable entry certificate. The full recursive compiler's
argument checks still enforce the stronger Total condition for scanner
calls. Replacing those checks with entry-indexed recursive capture safety,
while tracking retained values through every consuming call, remains open.
No broader all-input compiler theorem or class equality/separation is claimed
from the local frontier results.


## Checked profile sets close state-specific recursive capture safety

`RecursiveCaptureProfiles` and `ProfileCheckedScannerCorrespondence` close
the entry-indexed recursive argument-check gap described above. They reuse
the same actual source and generated target grammars, with a different
finite certification path. No Total M condition is used for captured words
or incoming retained values in this path.

Finite annotations describe possible scanner output profiles H(q), possible
user output profiles C(i,P) for each actual argument profile P, and admitted
user input profiles A(i). `scannerCheck` checks identity and closure under
every actual scanner arc. `grammarCheck` checks actual user bodies for every
finite input profile; parameters use their full actual profile, sequence
composes output sets, choice takes their union, and queries output identity
while retaining their actual computations. Stars use a finite candidate
closure with an explicit identity/composition check. If that check fails,
the abstract result conservatively falls back to the finite profile universe;
no convergence or termination assumption enters soundness.

Structural argument induction and user-round induction derive actual new
capture profile membership from these finite checks. In particular,
`frozen_rows` and `capture` do not take a semantic recursive-row or
argument-success oracle as an input. Captures may vary across iterations,
include nested stars, and invoke positive parameterized or mutually recursive
users. Source headers have their actual original-position behavior.

The call checker requires every possible argument profile to be admitted by
the callee and to satisfy that callee's exact `entryCheck`. Body checks only
need the admitted profiles; every nested call, including calls inside
queries, retains its own check. Actual profile accuracy connects these finite
checks to the source captures. The resulting simultaneous plain/product row
correspondence preserves every finite observation on every unchanged original
input, supplies one fixed first-order Seq grammar for the entire language,
and preserves physical definedness and all-clock undefinedness. The final
theorems require only the finite scanner, grammar, body, and root checks.
Annotations are checked finite sets, not assumed semantic invariants; no
completeness or automatic discovery of successful annotations is claimed.

A partial machine reads a from both states and b only from state 1. Its
state-1 whole scanner language fails the old all-state certificate. The new
finite checks nevertheless certify positive parameterized scanner calls:
an a/b star is captured as ab, the parent ab plus fresh b is passed into
another scanner inside an argument and captured as abb, and both complete
values are reused after return. The initial capture is input-dependent and
unbounded. The star's a and b operands have different full profiles. Kernel
examples verify the real physical source execution, generated target
acceptance, four short-copy failures, and all-input/all-clock nullable
argument divergence. The grammar instantiates the all-input language theorem.

This closes the state-specific safety integration for this compiler family.
Unary source users, the stated syntax, replay/scanner headers, one common
machine, and existence of successful finite profile annotations remain
restrictions. Arbitrary PEG prefixes, integration with other fragment
compilers, independent multiple source captures, and unrestricted Par/Seq
class equality or separation remain unresolved.

## Actual zero-return callees before retained parent continuations

`ParReturnEffects` adds a finite return-effect certificate for actual Par
rules. `dead` excludes success but permits failure and divergence; `zero`
permits only successes at the original call position; `any` is unrestricted.
Sequence, ordered choice, predicates, repetition, actual rule lookup and
arity checks have sound structural transfer rules. Simultaneous induction
on the real recursive tables closes a checked set of zero/dead rows for
all inputs, environments and physical clocks. In particular, a non-consuming
recursive cycle is not replaced by finite failure.

Candidate inference prunes finite sets of rule identifiers, checks the final
candidate, and falls back to empty sets if validation fails. Soundness does
not assume that pruning converges or finds every possible certificate. To
certify an empty-bound call without asserting that the ordinary retained-word
row is zero width, `emptyEffect` applies the analysis to the existing actual
nullary-clone specialization. Its previously proved same-clock correspondence
transfers the result back to the original expression and grammar. Captured
words have no finite palette, length bound or global empty-value premise.

`CheckedOriginCompiler` interprets source Plan guard sites as real sequences
`Q;B`, rather than lookahead. It checks that the actual source query Q has a
zero/dead return effect, then proves `Q = &Q` at the same physical clock on
the actual source tables. Structural Plan correspondence and a delay-zero
body rewrite connect the original mutually recursive grammar to the existing
mixed forwarding/growth/origin compiler. The resulting fixed Seq grammar
preserves the unchanged input language, all residuals, finite failure and
all-clock undefinedness. The final language theorem requires only a finite
check. With n users and b parts its size is n(n+1)+b; physical bounds remain
source k <= Seq k <= source (n+2)k. The preparatory normalization adds no delay.

The executable example is definitionally a raw Spec grammar whose factor-zero
parent calls the actual R(empty) before a parent-dependent replaying tail.
R's ordinary retained-word row consumes input, while its empty clone returns
at the original position when the next character is a or b, and recurses
without returning otherwise. Inference certifies clone 3, rejects ordinary
row 1, and the old syntactic zero checker rejects the real call expression.
A fixed root captures b;c-star; recursive children capture a;c-star and later
restore both retained values. Kernel executions verify two different old/new
capture lengths in a nine-rule Seq grammar and reject a short restoration.
For every suffix and every clock, the header on X followed by that suffix is
undefined in the original and compiled grammars. A consuming query fails the
finite checker; omitting that check changes a concrete residual. This last
example is a transformation boundary, not a language-class separation.

This closes zero-return actual callees, including recursive empty-bound
callees, before retained parent continuations within the mixed Plan schema.
A separate gate still requires growth heads to point to growth users; parts
must satisfy the existing Closed/replay restrictions. Consuming queries with
uncertified endpoints, recursive producers, continuations outside these
control forms, independent multiple captures, and unrestricted Par/Seq class
equality or genuine language separation remain unresolved.

## Recursive producers: reusing the actual argument evaluation

`RecursiveProducedCompiler` removes the call-free `Pure D` restriction from
the mixed producer compiler. A produced client still has the original Par
body `D;B(w)` and every call to it must syntactically use D as its argument.
D must be closed with respect to its caller environment, but may contain
arbitrary first-order calls allowed by the checked source family. In
particular, it may invoke recursive users, other produced clients, or the
very client whose prefix is being normalized. A finite check validates
closedness, source bodies, all nested call arguments, and the existing mixed
backend. No separate producer grammar, termination premise, or successful
recursive-row oracle is supplied.

The proof uses actual finite stabilization rather than same-clock equality.
`StablePar` derives fixed-row unfolding and information-order bounds from the
existing first-order CBV decision procedure. Row unfolding is restricted to
actual substring-valued environments, the exact domain of that proof.
`RecursiveProducedSimulation` transports conditional rows through ordinary
expressions, choice, negation and consuming repetition. At a produced call,
the structural argument induction supplies an actual successful evaluation
of D; the capture invariant is established there, rather than assumed for
the whole grammar. Ordinary rows and conditional producer rows then close
simultaneously over real recursive tables in both directions.

For the forward direction, any successful original prefix and actual
argument capture agree at the original stable table, by closedness and
determinism. For the reverse direction, the already evaluated source
argument supplies the prefix that was removed. These facts prove equality
of the original and normalized stable results and connect to the existing
fixed mixed Seq backend. They preserve the original string language, all
residuals, finite failure and all-clock undefinedness. Explicit physical
cofinality uses the existing input-dependent finite bounds: any source
clock refines target clock iterBoundV(normalized,x), and any target clock
refines source clock iterBoundV(source,x). These bounds are proof devices;
no input-specific table or bound is installed in the generated grammar.
The target size remains n(n+2)+b.

A real recursive producer R(empty) recognizes every a^n b. Its arbitrary
length argument captures are proved as actual DerivesArgsPar judgments for
every n and every following suffix, in one fixed source grammar. A
sixteen-rule Seq grammar also executes a retained-word growth client and
recursive produced clients with old/new lengths (0,3), (3,0) and (1,2),
restoring both values and rejecting a short parent copy. Another example
has R call the transformed produced client itself, so this is not just
closure over disjoint unchanged helpers. Direct source/target executions
and the full original-language theorem are instantiated for that cycle.
A non-consuming recursive producer stays undefined on every input at every
clock after compilation. A successful small example differs at clock 1
and agrees after the original prefix spends another call level; therefore
same-clock equality would be false here. Wrong producer arguments and open
producer expressions are rejected, and a concrete wrong-argument example
shows why the argument check is necessary.

This closes recursive closed producers with matching actual arguments in
the mixed schema, including producer/client dependency cycles. It does not
yet cover a consuming prefix different from the captured argument parser,
a prefix depending on the old caller environment outside the existing
replay forms, unrestricted continuation/control forms, or independent
multiple captures. The existing growth-head and Closed/replay backend
conditions remain. General Par/Seq class equality or genuine language
separation remains unresolved.

`RecursiveProducedOrigin` composes this normalization with certified actual
zero-return queries in the same original grammar. Its origin guard sites
start as real sequences, and effects are checked in that raw source grammar,
including its produced clients. A delay-zero rewrite prepares those sites
before recursive-producer normalization. A 27-rule Seq execution combines
a real recursive consuming producer, a real recursive zero-return header,
fresh parent/child captures, and restoration of the old parent value.
Replacing the zero header by a consuming character is rejected by the finite
check. Both frontends thus share one original-language theorem rather than
requiring the grammar to choose one of the two behaviors globally.


## Different argument parsers with certified common success endpoints

`EndpointSupport` and `CanonicalProducerCompiler` lift the matching-parser
restriction when a finite check certifies a common successful endpoint.
For an original actual declaration F(w) := D;B(w), the local transformation
is F(A) -> &A;F(D). Both parsers may have different successful inputs,
failures or divergence. The check only implies that if A and D both
succeed, they capture the same input prefix. Original A evaluation remains
first, and D is retained as the actual canonical argument; its failure and
divergence are therefore not erased.

The finite support checker derives a successful run of a common closed core
from each successful parser run on the actual source tables. It supports
exact syntax, character/range widening to any, actual zero-return wrappers
before or after a core, sequences of supported components and alternatives
whose successes share a core. Zero-return facts use ParReturnEffects in the
original source grammar. The core may itself call real recursive users.
Actual first-order CBV stabilization and closedness then identify successful
endpoints across different source clocks and retained environments. This
is not a semantic equality premise, a word palette, or a totality oracle.

`ProducerArgumentRewrite` proves a same-clock forward refinement and a
one-round reverse refinement for each changed call. The extra round is
necessary: moving a failing prefix into argument evaluation can expose a
failure before the original callee row has been unfolded. A structural
renderer keeps already canonical calls and inserts the ordered preflight
at other calls. It leaves canonical producer declarations unexpanded, so
recursive producers do not cause infinite syntax expansion. Original D
must be closed and its own immediate call syntax must already satisfy the
canonical argument condition; called rule bodies may themselves contain
noncanonical calls and are transformed as part of the same grammar.

Finite checks validate every original body, core annotation, emitted
canonical source, and emitted body shape against the structural renderer.
The latter is an AST check, not a hypothesis about evaluation tables.
A computed sum of body costs supplies the uniform FiniteBodyRewrite delay.
For body budget d and root cost c, original clock k refines prepared clock k,
and prepared clock k refines original clock (d+1)k+c. This composes with
RecursiveProducedCompiler's physical cofinality and fixed Seq backend.
`checked_language` requires only the finite grammar and root checks and
preserves the original input string. No rules are added by canonicalization;
the final target still has n(n+2)+b rules.

The main fixed grammar has a recursive argument C recognizing a^n b (and
a^n z), and a distinct prefix D consisting of a real zero-return callee
followed by C. The zero callee succeeds on a, fails on b, and loops on other
characters. All a^n b argument captures, for every n and suffix, are proved
as actual DerivesArgsPar judgments; their lengths are unbounded. The child
argument additionally tests the parent's retained value before running C,
so caller-dependent predicates are retained in the generated preflight.
Par and the generated 26-rule Seq grammar execute old/new a-prefix lengths
(1,4), (4,1), (2,3), restore both values, and reject equal child values and
short parent copies. The original-language theorem is instantiated.

When C succeeds on z but D loops, the original and generated calls stay
undefined at every clock for every following suffix. Omitting the producer
preflight would accept z!zgz. When C fails finitely on X and D loops, the
ordered preflight preserves the original failure; reversing it stays
undefined at every clock. A separate example uses distinct consuming
parsers, a wildcard actual argument and a canonical character a: the same
captured a is retained and replayed on aa, while bb fails. Omitting the
gate accepts bb incorrectly. A clock-0 failure versus clock-1 original
failure proves that the reverse local delay cannot be zero. An argument
that consumes an extra ! after C is rejected by the endpoint checker.
These are transformation boundaries, not language-class separation claims.

This closes checked noncanonical producer arguments, including actual
recursive parsers and caller-dependent query wrappers, in the mixed unary
schema. It still requires a certified common successful endpoint and a
closed canonical prefix; arbitrary different endpoints, other prefix or
continuation forms, independent multiple captures, and general Par/Seq
class equality or genuine language separation remain unresolved.


## Selected recursive producers with retained-word position shifts

The fixed-literal rotation and finite profile product already exist in
`BlockCapture`, `ScannerReplayResidual` and the recursive scanner backend.
This extension connects real recursive producers to that backend in one
original grammar. It does not claim a new general solution for arbitrary
position differences.

`SelectedProducerNormalization` takes an ordinary first-order grammar and a
finite list of selected positive-arity declarations D;B(W). Every syntactic call to
a selected declaration must use the matching D as its last argument; D is
closed in the caller environment. Finite checks verify the actual arity and
body, closedness, first-order source bodies and nested call conformance.
Selected bodies become param(arity-1);B(W), keeping the full argument tuple. Unselected declarations retain their
original arities and bodies. The source need not belong to a mixed-entry
DSL: ordinary nullary and multiple-argument rules are covered directly.

The mutual structural evaluator/argument simulation preserves actual Par
argument order for arbitrary ordinary arities. Conditional producer rows
and ordinary rows close simultaneously over the original and normalized
physical tables against their actual finite stabilization tables. The
capture condition is derived from actual argument evaluation. Stable
results, all residuals, finite failure, finite definedness and all-clock
undefinedness are preserved, including under arbitrary retained environments
at valid source positions. No helper row meaning or totality premise is
supplied. A multiple-argument example retains distinct values, and an
argument-order example distinguishes early failure from nullable divergence.
Selecting an actual nullary declaration as a producer is rejected.

`ProducedScannerCompiler` validates that this emitted ordinary grammar is
syntactically identical, arities included, to the existing profile-checked
scanner compiler's source. Existing scanner/grammar/input profile checks
then connect it to the fixed Seq product. Both interfaces are finite syntax
or finite profile checks, not semantic table or language-equality oracles.
The original nullary scanner helper declarations remain present at their
original arities throughout producer normalization.

The concrete source has a real recursively defined a-star producer. Actual
DerivesArgsPar capture judgments are proved for every length n before an !
delimiter and every subsequent suffix, with unbounded captured lengths.
Another user has the actual body a;param0;":";param0. Its argument consumes
n characters from the original position; its literal head consumes exactly
one. For every n≥2, the actual remaining-input positions are respectively
2 and n+1 on a^(n+1)? and thus differ by n-1. The existing rotation moves
the literal residual after the Seq argument endpoint, retaining the same
whole value for the continuation. A parent keeps its own value through this
call, recursively captures a new child value, and restores its old value
after a separator. The finite certificates admit all observer profiles;
an unreadable ab capture is checked and fails finitely, rather than being
excluded by a word-shape or length premise.

The generated grammar has 65 rules. Direct kernel executions verify a
length-two capture with the shorter literal head, a parent/child capture
of lengths one and three, and short parent/child rejection. Original
executions cover (1,3), (3,1), (2,4); corresponding actual target executions
also follow from the general finite-definedness theorem. The all-input
original-language theorem is instantiated. A separate nullable producer
stays undefined on every input at every clock in both original and generated
grammars. None of these failures is used as a language-class separation.

The scanner Seq backend retains its unary user/header/body syntax, one common
finite scanner and checked profile conditions. Generic producer preparation
preserves multiple-argument ordinary rules, but this does not translate
arbitrary multiple-capture source grammars to Seq. Prefixes outside the
existing replay/rotation/scanner conditions, unmatched producer arguments,
other continuation forms, independent multiple captures, and unrestricted
Par/Seq class equality or genuine language separation remain unresolved.


## Multiple retained values with an actual recursive producer

The selected producer simulation now handles every positive arity. Its
conditional row invariant keeps the complete actual argument tuple W; only
the final slot is required to be the captured successful result of the
closed producer D. A mutual argument_capture theorem derives that capture
from the actual Par argument evaluation and the checked last AST. Ordinary
and selected rows close simultaneously over the real recursive tables.
An indexed replay lemma replaces the former singleton-only replay proof.
Argument order, finite failure and all-clock undefinedness remain preserved.

ProducedPrefixFamilyCompiler checks that the normalized grammar is exactly
the existing PrefixFamilyFusion cumulative-capture source, including every
rule arity and body. It composes their observation correspondences to one
fixed first-order Seq grammar with an unchanged original string language;
finite definedness and all-clock undefinedness are also proved. The
cumulative argument rendering and parameter-view reconstruction are reused
from PrefixFamilyFusion, not claimed as new general difference synthesis.

The concrete three-rule recursive grammar has arities [2,0,0]. Actual Par
arguments capture a^n and a^n b^m from the same position, while actual Seq
arguments capture the consecutive chunks a^n and b^m. Both operational
argument judgments hold for every n,m and every suffix after a ! delimiter.
Both chunks have unbounded lengths. The original selected body starts with
a real closed recursive producer, not a longest-value parameter replay.
The continuation observes both values, recursively obtains distinct child
values, then restores both parent values. Direct kernel runs cover empty
chunks, several nonempty lengths, nested distinct values, and rejection of
short parent, wrong first, and short child copies. A nullable recursive
helper remains undefined for all inputs and clocks in both grammars. A
nonmatching last argument is rejected by the finite source check.

This extends the actual producer frontend beyond unary retained users.
It still requires cumulative source argument syntax for this Seq backend
and a matching closed last-argument producer. Arbitrarily specified Par
argument parsers, arbitrary successful endpoint orders, parameter-dependent
producers, other body shapes, and the unrestricted language-class question
remain unresolved.


## Independently specified recursive arguments at scanner frontiers

FrontierArgumentNormalization adds a source argument frontend rather than
a new scanner-difference algorithm. Each descriptor names a finite alphabet
A, an actual nullary helper prefix, and a parser P. Its real argument is
P;!choice(A). A finite syntax check validates the actual helper arities and
bodies and their consuming paths, together with P, using the existing
ScannerAbsorption safety invariant. Negative queries retain their real
semantics. Recursive parsers need not be total. A successful actual argument
must end exactly at the maximal A-run: the safety invariant preserves the
scanner remainder, and the actual negative frontier query stops the scanner.
This is proved on original physical tables for arbitrary caller environments.

For any fixed-arity call with checked argument descriptors, the original
argument tuple is replaced by an ordered sequence of lookaheads followed by
a call with the corresponding scanner arguments. The original arguments are
all evaluated from the original position, in their original order. A finite
failure or undefined argument prevents the scanner call from running. On
full success, the canonical scanner argument tuple is exactly the original
tuple. Neither a successful-evaluation premise nor an endpoint-equivalence
oracle is part of the compiler input. The local call equality holds at the
same physical clock.

FrontierArgumentCompiler applies this rewrite to matching calls throughout
actual source rule bodies, alternatives, negations and stars; calls whose
argument ASTs do not match remain intact. It preserves every declaration
arity, and closes a BoundedBodyRewrite over the real recursive tables.
Observation and all-clock undefinedness correspondence include a transformed
root. The global finite source check includes first-order bodies. The
framework does not accept the final language correspondence as a certificate.

FrontierCaptureCompiler then composes this ordinary-grammar normalization
with selected closed-producer normalization and the existing nested-scanner
compiler. Finite AST equality checks the entire emitted grammar, arities
included, and the prepared root. A finite scan recognizer and alphabet
inclusion check validate every backend template call. The final grammar and
root are fixed before the input, with the original input alphabet and string
unchanged. The final observations theorem preserves all residuals, finite
failure and hence language recognition; all-clock undefinedness is proved
explicitly.

The actual source example has two independently written argument parsers:
a recursive a-star followed by b, and the actual recursive rule R <- a R c / b.
Frontier tests use alphabets {a,b} and {a,b,c}. For every n and every suffix
after !, actual DerivesArgsPar judgments capture a^n b and a^n b c^n. Both
source values have unbounded length. The generated Seq grammar has three
rules of arities [0,0,2] and captures adjacent a^n b and c^n chunks; the body
observes the original tuple through prefix views. The original body begins
with a real alphabet scanner, which the selected producer frontend replaces
with the replay of the last captured value before backend fusion. Source
and target acceptance of the entire positive family, with every suffix, are
proved through actual derivations and the general correspondence, not just
finite tests. Direct executions cover n=0,1,2,4 and nested distinct parent/child
values. Unbalanced counts are rejected on both sides. Omitting the original
preflight accepts a b c c and its copy payload incorrectly. A nullable first
argument remains undefined on all inputs and clocks in both grammars.
Checks reject unsafe helper consumption, incorrect actual helper layout and
a root missing its frontier queries. A finite failure before an unresolved
helper call is distinguished from the reversed, undefined order.

The new frontend removes the requirement to write these arguments themselves
as cumulative parser expressions or as greedy scanners. It does not remove
the canonical scanner endpoint restriction, nested alphabet order, checked
closed-producer body shape or backend control syntax. In particular, it does
not derive residual parsers for arbitrary differently stopping Par arguments.
Unrestricted Par/Seq class equality or a genuine language separation remains
open.


## Independent frontier pairs with opposite runtime orders

The consuming-path checker no longer requires every helper in the declared
prefix to fit every argument alphabet. MaskedScannerAbsorption computes a
finite candidate mask by pruning unsafe helper bodies, then independently
checks its length and closure under consuming nullary calls. Physical row
safety is proved only for enabled helpers. Inactive helpers keep their actual
bodies and may still be evaluated under negative queries; queries always
retain their original semantics. No semantic helper invariant, fixed-point
convergence or termination premise is supplied to the compiler. Unsafe
consumption propagates through recursive calls; a safe mutually recursive
component is retained. The original full helper layout remains checked.

MixedScannerPairFusion extends the existing ScannerFrontier pair algorithm
to actual grammars mixing nullary recursive helpers and two-argument users.
Each source entry emits two fixed target slots. Nullary helpers retain zero
arity and call their translated helper rows; user variants reconstruct the
two original captures from adjacent chunks, selected by the existing runtime
first-stopping test. The source helper-row and shifted pair-row relations
close together over the actual recursive tables at every physical clock.
This is a whole-grammar theorem, not an assumed user-row contract. All
residuals, failure and undefinedness are preserved, without alphabet inclusion.
The existing intersection scan, endpoint-order guard and prefix-view equations
are reused rather than claimed as new difference-parser algorithms.

FrontierPairCaptureCompiler connects the original recursive-argument
preflight normalization to this mixed backend by finite equality of the
whole emitted grammar and rendered root. It produces a fixed first-order
Seq grammar recognizing the same original strings. Original expressions
must pass the finite first-order check. All-clock undefinedness is explicit.
The source pair body retains the existing branch selecting and replaying
the longer captured value before its tail; no arbitrary body normalization
is claimed here.

IndependentFrontierExamples installs a shared a-star helper, a recursive
balanced a/b helper and a separate recursive balanced a/c helper. The two
argument alphabets are {a,b} and {a,c}, neither included in the other. Their
checked masks are [true,true,false] and [true,false,true]. Each original
argument independently attempts its balanced parser with a frontier test,
then the shared a-star fallback. Both original helpers remain present with
their actual nullary declarations. At n=1,2,4 actual original argument tuples
have the a/b capture longer on a^n b^n, and the a/c capture longer on a^n c^n.
Source and eight-rule Seq executions are checked in both orders. The target
arities are [0,0,0,0,0,0,2,2]. An additional recursive user obtains a child
whose endpoint order is the reverse of its parent's, then restores both
parent values; both directions and an empty-capture child execute directly.
The all-input source/target observations theorem is instantiated for both
ordinary and recursive users. A b-count mismatch fails on both sides,
while removing preflight wrongly accepts a b b and its copy payload.
A nullable first argument stays undefined on every input and clock in the
original and generated grammars. Direct access to an unsafe helper, and a
cycle reaching unsafe consumption, are rejected by finite checks.

This removes uniform helper-alphabet and static endpoint-order conditions
for this two-capture frontend. Maximal scanner-frontier success endpoints,
two source captures and the replay-shaped body remain required. The
unrestricted Par/Seq language-class question remains unresolved.


## An actual consuming head instead of longest-value replay

ScannedPairFusion uses the same mixed helper/user entry data and the same
fixed Seq target as MixedScannerPairFusion, but changes the source pair body.
It begins with maxScanner(A,B);tail. maxScanner branches on the existing
closed stopping-order query, then actually runs scan B or scan A from the
source position. It contains no retained parameter and reaches the longer
actual scanner endpoint for every input, table and environment.

The source-to-target row invariant is now restricted to actual scanner
argument values and their actual endpoints. The earlier replay-shaped row
relation, which allowed arbitrary hypothetically aligned values and suffixes,
would not justify replacing a real parser by a parameter. The new invariant
relates the real reconstructed source tuple at p to the two target chunks at
the actual finalPos. Nullary helper rows and these pair rows close together
at every physical clock. The structural evaluator proof and fixed-point
observations theorem then preserve both captured values and all residuals.
No actual row behavior or successful capture assumption is accepted from
outside the proof.

ProducedFrontierPairCompiler connects original independent recursive
arguments to this source by the existing ordered preflight normalization
and a finite equality check of the entire emitted grammar, including helper
arities, plus a checked rendered root. The language theorem uses one fixed
first-order Seq grammar on the unchanged original strings. Finite failure
and all-clock undefinedness are preserved explicitly. This closes the
leading-replay restriction for these specified actual consuming heads;
it does not infer arbitrary prefix/body rewrites.

ProducedFrontierPairExamples keeps the a-star, balanced a/b and balanced a/c
actual recursive helpers. The original pair user consumes its head by the
closed maxScanner before observing either retained parameter. Direct source
and target executions cover n=1,2,4 in both stopping orders, parent/child
order reversal in both directions, restoration of the parent's two values,
and an empty-capture child. All-input observations are instantiated for the
ordinary and recursively calling variants. A general all-input correspondence
with the earlier replay-shaped original is also derived through their shared
fixed Seq target. A nullable first argument stays undefined on every input
and clock in both new original and target.

The union of scanner alphabets is not a valid implementation of the maximum
endpoint: on abc!ab:a the {a,b}/{a,c} source captures ab and a, so its real
maximum head stops before c and the continuation fails. A union scanner
incorrectly consumes abc and accepts the remaining payload. Both behaviors
and rejection of the wrong source head by the finite grammar check are
kernel verified. Running the unmodified new source under Seq on the n=2
b sample leaves two characters, while the generated Seq target consumes all;
this is an operational distinction used to validate the translation, not
language-class separation.

The actual consuming head must still be this closed maximum-scanner parser,
and successful original arguments must end at their certified scanner
frontiers. Arbitrary PEG prefixes, other body entry endpoints, general
independent argument differences and the full Par/Seq class question remain
unresolved.


## Recursive origin queries before independent pair consumption

The new guarded-pair backend supports source bodies
&Q;maxScanner(A,B);tail. Q is a real closed source parser rendered in the
same grammar; it may call nullary recursive helpers or the pair users,
including the current user. No totality, successful-query or table-behavior
premise is supplied. Finite closure checks validate both query renderings,
so the source query's evaluation under captured values equals its evaluation
under the empty caller environment. The query may consume internally;
its enclosing lookahead restores the original source position.

GuardedPairSyntax emits a nullary header plus two fixed capture/body variants
for each entry. The header runs the translated query at the original input
position before dispatch captures adjacent chunks. Helpers remain nullary.
GuardedPairSimulation provides structural refinement in either direction;
GuardedPairCorrespondence closes the actual source and target row relations
by physical-clock induction, invoking the expression refinement on the
actual query at the preceding stage. This handles recursive query/user
cycles without assuming their outcome. Source clock k refines target clock
2k, while target clock k refines source clock k. Existential finite results,
all residual observations, finite failure, language and all-clock undefinedness
follow from these bounds and actual stabilization, not equal same-clock runs.

FrontierArgumentCompiler additionally proves exact equality of its actual
ordinary-grammar table approximants and a same-clock expression translation.
Its existing ordered preflight rewrite is therefore exact at every physical
clock, rather than merely cofinal. GuardedFrontierPairCompiler uses that
stronger result to expose the k-to-2k and k-to-k bounds for the original
pre-normalization grammar and root. Whole prepared-grammar/root equality,
first-order syntax and closed queries are checked finitely. The final grammar
and root are fixed before the unchanged original input string is supplied.

GuardedFrontierPairExamples installs the existing balanced a/b and a/c
recursive helpers in an origin query, together with an initial a test, so
running that query at the captured endpoint would fail. Both orders at
n=1,2,4 and recursively reversed parent/child orders execute directly on
the original and twelve-rule Seq grammars. The target arities consist of
ten nullary entries and two two-argument cases. Source and target gate
failure are checked separately from undefinedness. A query that calls the
same pair user forever is proved undefined on every input at every clock
in the actual source and target tables, even though the canonical scanner
arguments themselves always succeed.

An undefined first actual argument is still evaluated before a failing
origin query. The full original and target stay undefined for every input
and clock; prematurely invoking the target header instead yields finite
failure on a concrete input. A tiny empty-capture example succeeds at source
clock 1, remains undefined at target clock 1 and succeeds at target clock 2,
confirming that the extra header layer is operationally real. A query with
a free retained parameter is rejected by the finite closure check.

This removes the total-head restriction for the closed recursive query
part of this two-capture construction. It does not translate an arbitrary
consuming prefix, an arbitrary capture endpoint or a query depending on the
parent's captured environment. Maximal scanner-frontier successes and the
specified maxScanner continuation entry remain required. General Par/Seq
class equality or genuine language separation remains unresolved.


## Retained-value origin queries with checked closed continuations

CapturedOriginQuery adds a checked plan language for origin tests. A leaf
is a closed test or &(param_k;C), with k selecting one of the two actual
captures and C checked closed under both renderings. The original query may
therefore depend directly on its retained values. Plans compose using seq,
ordered choice, negation and star. Every successful component returns to
its original input position; nullable success under star remains undefined.

Actual scanner argument evaluation derives the two stored words, and sound
source tables derive their successful prefix alignments. Replaying the
selected parameter at the common origin reaches the same endpoint as its
scanner. After that point, C's checked closedness removes dependence on the
parent environment. Structural plan induction proves equality with a closed
canonical test using the corresponding scanner instead of the parameter,
including failure and undefinedness. The proof deliberately does not assert
scanner/parameter equivalence at arbitrary later positions.

CapturedOriginNormalization constructs raw and canonical query lists in the
same mixed source grammar. Its table relation is restricted to the actual
capture tuple at the actual source position. Helper and pair rows close
simultaneously at the same physical clock, invoking the structural expression
simulation on the canonical query and continuation. Actual source-table
soundness and finite plan checks discharge the alignment conditions; no
row semantics or successful-capture premise is accepted as compiler input.
The result is exact same-clock expression translation for rendered roots,
not equality of arbitrary artificially supplied capture environments.

CapturedOriginCompiler composes ordered original-argument preflight,
this query normalization, and the existing guarded Seq header backend by
finite whole-grammar/root checks. Source clock k refines target clock 2k;
target clock k refines source clock k, starting with the original grammar.
All residual observations, failure, unchanged-string language and all-clock
undefinedness follow. The target grammar and root are fixed before input.

CapturedOriginExamples uses &(param0;'c') / &(param1;'b') so the short
capture is observed at its following character in either runtime order.
On the same ab input prefix, swapping retained ab/a to a/ab changes the
query from success to failure. The earlier closed-query checker rejects
this original query; the new canonical header query passes. Direct original
and twelve-rule Seq runs cover n=1,2,4 in both orders, parent/child order
reversal and parent value restoration. Another checked leaf calls the real
recursive a-star helper after replay and a literal. A continuation that
reads another parent parameter is rejected.

For a star of a successful retained replay test, actual canonical scanner
arguments always produce a nullable success. The raw parameter-query source
and Seq target are proved undefined for every input and clock. Separately,
an undefined original first argument remains undefined before the dependent
query in both original and generated grammars; bypassing that preflight
incorrectly accepts a concrete payload. The all-input original-language
correspondence is instantiated for the independently specified argument
frontend, beyond these finite direct runs.

This extends the earlier closed-origin-query restriction to the checked
retained-replay test plans. It does not support an arbitrary parent-dependent
continuation after replay, arbitrary capture endpoints or arbitrary consuming
body prefixes. Maximal scanner-frontier arguments and the designated actual
maximum-scanner head remain required; the full language-class comparison
is still unresolved.


## Nested tests of other retained values after replay

Plan.follow k q compiles the original query &(param_k;q), where q is
another query plan rather than an arbitrary closed expression. It may
therefore inspect either old retained value after the first replay, and
may nest further replays. The existing test and after leaves keep their
closed-expression checks. Every plan component still restores its starting
position, including partial stars, so parent-dependent tests do not drift
through arbitrary consuming continuations.

ScannerFrontierValues proves the semantic condition behind the new compiler.
After a nonempty maximal run of a stateless character-set scanner, every
nonempty prefix captured from the same origin starts with a character that
the current frontier cannot match. An empty word remains replayable. The
other word need not itself be a scanner capture for this local prefix lemma.
For the compiler's two actual scanner arguments, exact capture/word equations
identify their empty bits with the source's first-character membership tests.
No finite enumeration of possible captured strings is used.

A canonical follow query branches at the original position on those two
empty bits. If the selected capture is empty, replay consumes nothing and
translation continues at the original position. If it is nonempty, the
corresponding scanner advances to its actual frontier, where nonempty old
parameter replays specialize to failure and empty ones to zero success.
Closed query leaves retain their actual computations. Structural induction
includes seq, ordered choice, negation, nested follow and nullable star;
source and canonical results agree at the same clock. The existing actual
recursive-table normalization and guarded Seq header compiler then preserve
original observations/language and the k-to-2k / k-to-k bounds without changes
to their public input assumptions. The target remains twelve fixed rules.

NestedCapturedOriginExamples verifies both nonempty captures in either order
at n=1,2,4, recursive parent/child order reversal, and current-parent value
restoration. Scanner-argument variants check first-only, second-only and both
empty captures, including a nested query that first replays an empty value
and then a nonempty one. On the same input, changing actual ab/a captures to
foreign a/b values changes the nested query result; the compiler's same-origin
capture invariant is essential and is proved rather than assumed.

For &(param0;&(param1;eps)), a symbolic evaluator theorem on every input and
table gives failure exactly when both original captures are nonempty, and
zero success otherwise. Its star therefore remains undefined at every clock
on every input with at least one empty scanner capture, in the full original
scanner-argument program and generated Seq grammar. A both-nonempty input
instead exits the star through finite failure and is accepted. Replacing the
innermost eps by eps-star checks that a nonempty second replay fails before
entering the divergent continuation, while an empty second replay enters it
and stays undefined.

The current-frontier limitation is explicit: the state-changing scanner
with transitions a from its initial state and then b-star consumes ab from
abab and stops before another ab, which the retained value can replay.
This kernel counterexample rules out applying the stateless empty-bit
specialization to general stateful scanner frontiers. It also does not claim
that nonempty values remain dead at all later input positions. Arbitrary
consuming dependent continuations, arbitrary capture endpoints and the full
Par/Seq language-class equality or separation remain unresolved.


## Exact empty-result observations for independent recursive arguments

EmptyResultObservation compiles an arbitrary nullary recursive PEG into two
nullary rule channels per original rule. At every actual physical clock,
the normal Seq channel agrees with the original Par result; the empty
channel keeps empty success, finite failure and undefinedness, and maps
only consuming success to finite failure. Source recursive structure may
include left/mutual recursion, priority, negation and nullable repetition.
No termination or semantic nullability oracle is required.

A full original-expression lookahead gate precedes the zero-only candidate
for sequence, choice and repetition. Without it, discarding a consuming
prefix could skip a divergent continuation and incorrectly yield finite
failure. Choice also retains the original earlier-branch failure condition,
so a consuming success never falls through to a nullable alternative.
Star tests first-body failure only after its complete original evaluation;
nullable repetitions therefore remain undefined.

EmptyCaptureDecision applies these observers to arbitrarily many independent
nullary recursive argument expressions. Ordered preflight preserves actual
Par failure/undefinedness order before a finite decision tree selects a leaf
from the exact isEmpty view of the real captured-word tuple. The chosen leaf
may consume input, and the emitted expression is first order when its leaves
are. The physical theorem relates that actual Seq expression to evParArgs
at the same original position and clock. It does not reconstruct captured
contents or yet compile an arbitrary parameterized callee body. In particular,
it does not by itself remove the scanner-frontier conditions of the earlier
whole-grammar compiler. General language-class equality/separation remains open.

Kernel examples cover independent balanced a/b and a-star producers plus an
empty argument, distinct nonempty captures, a consuming selected leaf, all
empty captures, failure before divergence and divergence before failure,
out-of-range calls, and incomplete versus completed recursive clocks.
All-clock proofs retain divergence after a consumed prefix and preserve
nullable-star undefinedness on every input. Concrete omissions of sequence/
star gates, choice priority and original argument preflight give different
results and are explicitly rejected as alternative constructions.


## Whole-grammar elimination of EOF-observed retained values

EmptyObservedSyntax/Dispatch/Evaluation/Correspondence/Compiler extends the
previous independent-nullary emptiness observers to mutually recursive user
rules and argument expressions of arbitrary arity. The explicit restriction
is that every direct retained-parameter replay has the source form
(!any);param_k. Such a replay succeeds precisely for an empty retained value
at EOF. Queries may reach EOF under lookahead and restore the caller's
position, so both callee bodies and actual arguments can inspect the parent's
empty/nonempty state before further consumption or user calls.

The fixed target enumerates finite empty-bit patterns for each declared
arity and generates normal/empty-result nullary rows. Ordered preflight
retains original actual-argument failure/undefinedness order, then emitted
observer expressions select a concrete row number from the real captured
word tuple. Normal and empty-result channels close simultaneously against
the actual Par and Seq tables at exactly the same physical clock. The row
invariant quantifies over every retained environment of the declared arity,
without a finite word palette, source-input encoding, helper termination
oracle or supplied semantic row table. No scanner-frontier restriction,
producer alphabet or bound on captured length is used by this backend.

The source and target syntax are first order; all target rules are nullary.
The complete declaration/root equality checks are finite AST comparisons.
The final theorems preserve every original-string observation and residual,
finite failure, all-clock undefinedness, and the fully consumed language.
Structural mutual recursion makes the emitter and original lowering directly
computable by the kernel, including the normal/zero pairs used in arguments.

The concrete four-rule source has arities [0,2,2,1]; its generated Seq target
has exactly 22 fixed nullary rules. Kernel executions cover balanced recursive
a/b producer captures at n=1,2,4, reversed parent/child empty-state patterns,
restoration of both parent values, parent-dependent actual-argument queries,
parameterized user calls inside actual arguments, and nested lengths (1,3)
and (3,1). A separate symbolic argument theorem captures any input word at
every clock, so the real retained values have no finite length palette.
Parameter-dependent recursive actuals and nullable parameter repetition
retain all-clock undefinedness on empty input. Preflight order, skipped arguments on wrong
arity/out-of-range calls, and wrong acceptance after bypassing preflight are
checked. These executions support the translation, not class separation.

The EOF guard is essential to this finite view: actual source captures a and
ab from the same ab!a input are both nonempty, yet after consuming ab! only
a replays successfully. The checker rejects an unguarded parameter rule.
The unrestricted content-dependent replay problem and the full Par/Seq
language-class equality or genuine separation remain unresolved.


## Exact finite-content replay beyond EOF

FiniteSuffixReplay/Body/CallCompiler supports actual consuming retained-word
replay when the current remaining input belongs to a fixed finite dictionary
R. The original source guard tests exact suffix membership and preserves the
current position. The suffixes(alphabet,bound) constructor covers every word
within a finite alphabet and length bound. Neither total original input
length nor captured-word length is bounded by the compiler.

The observation dictionary is generated from all prefixes of R. Captures in
that dictionary retain their exact literal contents; every other actual
capture receives an overflow/other view. An other capture is not rejected at
call entry: it is known to fail only behind the original suffix guard.
Negation, choice, partial star, arbitrary consuming body prefixes and
independent recursive helper calls preserve that distinction. Specialization
can therefore retain distinct nonempty a/ab values and consume only a from
a later ab suffix, leaving b to a continuation.

ExactWordCaptureMachine generates strict finite-word output automata,
including the empty word. Reading one extra character after the candidate
reaches a dead state, unlike periodic summaries. The existing machine-family
sum and RegularCaptureProduct backend supply real independent recursive
parser output tests. FiniteWordCaptureSelection probes equality with each
candidate rather than enumerating every transition profile. Preflight retains
actual argument failure and undefinedness, and guarded branch commitment
prevents a failing continuation from retrying a different capture class.

The whole-program frontend has independent nullary recursive helper nodes,
one arbitrary-arity source callee, helper-call actuals and helper-only body
calls. This is a complementary backend: it does not yet cover the mutually
recursive parameterized users or parent-dependent actuals of the separate
EOF-observed frontend. Source helpers stay as declared, while only the Seq
target receives output-product rows. Finite declaration/root/range checks
connect actual source syntax to stable physical table equality. All original
string observations, residuals, finite failure, finite-run existence and
all-clock undefinedness are preserved. No same-clock or constant clock-ratio
claim is made for this backend.

The primary nine-rule source yields a fixed 656-rule nullary Seq grammar.
Direct source/Seq kernel executions distinguish a/b contents, preserve actual
common-origin a/ab captures, and preserve failures on wrong copies. A separate
ab-suffix instance directly verifies partial replay leaving a nonempty b
remainder and consuming it afterward. Balanced recursive a/b arguments have
actual captures checked at n=1,2,4 and a direct generated Seq run at n=2.
A longer captured value remains usable through negative replay tests; its
actual target finite run is obtained by the definedness correspondence.
Nullable retained replay on nonempty remaining input is undefined at every
clock. An undefined leading argument is undefined for every original input
and clock, while reversing it with a failing argument fails finitely.
Empty dictionaries, alphabet boundaries and omission of the source replay
guard are checked, with unguarded raw source rules rejected by the frontend.

Arbitrary unguarded replay can match an overflow word and cannot be replaced
by this finite view. General replay locations, arbitrary parameterized user
control and the unrestricted Par/Seq equality or separation remain open.


## Mutually recursive users with exact finite-suffix views

The FiniteSuffixRecursive modules extend the single-callee backend to any finite family of
mutually recursive users with arbitrary, mixed arities. Each direct replay retains the explicit
finite remaining-suffix guard. Actuals remain calls to independent nullary recursive helpers;
parent-dependent actuals and parameterized calls inside actuals are not yet supported.
Generated fixed nullary rows are indexed by user and exact candidate/other tuple. Ordered original
argument preflight and strict equality probes select the new tuple without overwriting the
parent view in its continuation. Invalid calls lower to failure before evaluating actuals.

The helper prefix is frozen at actual physical stabilization; simultaneous induction over user
stages proves rows for every retained environment of the declared arity. Physical finite-run
cofinality then gives all original-string observations and accepted languages, residuals, finite
failure and all-clock undefinedness, without a same-physical-clock claim or semantic helper oracle.
Complete raw declarations and root expressions are checked by finite AST comparison.

The eleven-rule source has arities [0,0,0,0,0,0,0,0,2,2,1] and its fixed target has 844 nullary rules.
Direct kernel executions at nesting depths 0/1/2 distinguish nonempty a/ab parent and reversed
ab/a child tuples at nonempty remaining suffix ab. On return the outer rule consumes its own
retained ab. Leaking the child tuple or reversing actuals fails. Balanced captures at n=1/2/4,
long other-view negative replay success versus short ab failure, all-input/all-clock undefined
user cycles, nullable retained repetition on a nonempty suffix, ordered failure/divergence,
preflight bypass and malformed-call behavior are verified. The unchanged source under Seq fails
on an accepted example; this operational contrast is not a class separation.

The general original-string Par/Seq equality or separation remains unresolved. The existing EOF
backend permits parent-dependent recursive actuals but restricts direct replay to EOF; this backend
relaxes that replay region to finite exact-content observations while retaining independent actuals.


## Finite-view congruence with parent-dependent recursive actuals

FiniteSuffixDependentView removes the independent-actual syntax restriction for a separate
shared-table expression theorem. Actuals may inspect parent retained words using guarded replay
and invoke users inside actuals. Specialization replaces the current parent's guarded references
by finite-view literals/failure. It preserves the entire actual captured-word tuple for Par,
and the tuple and final position for Seq, over any shared table with the ordinary position-range
invariant. Calls then consult the same original table at identical real actual words.
Equal parent views consequently give equal expression results at every actual tblV clock;
rows_factor proves this for every user row of an arbitrary mutually recursive source in this syntax.
Direct executions check a parent-dependent negative query, a user inside an actual, capture of a,
subsequent replay, and a different result when an other-view parent becomes the candidate ab.
Two distinct other-view parents have symbolically equal results at all clocks.

This lemma alone shares the original parameterized callee table. The generated observer for fresh
captures of arbitrary dependent actuals and elimination of that table are now supplied by
FiniteSuffixObserved below. The earlier FiniteSuffixRecursive compiler itself continues to require
independent helper actuals. The unrestricted class question remains open.


## Whole-grammar finite-suffix translation with dependent recursive actuals

The FiniteSuffixObserved modules connect the shared-table finite-view lemma to a complete fixed
nullary Seq grammar. Source users may have arbitrary/mixed arities and mutually recursive bodies
and actuals. Any actual may inspect parent retained values and call parameterized users inside
actuals. Control includes sequence, prioritized choice, negation, partial star, literals, characters,
ranges and any. Every direct retained replay still has the explicit finite remaining-suffix guard.
No independent-helper, scanner-frontier, captured-length, input-alphabet or termination premise
is needed; the original parameterized table is absent from the generated grammar.

Rows are indexed by user, exact candidate/other tuple, and either normal mode or a state pair of
one strict candidate-word DFA. Normal lookahead precedes exact output probes for each actual;
committed branches preserve its real output even when later continuations fail or diverge.
All calls are nullary, so the selected body starts at the original Par origin. Parent views remain
lexical in the caller continuation. Simultaneous normal/filter induction gives equality at every
same physical tblV clock. GeneralStarFilter handles arbitrary partial repetition, all intermediate
DFA states include sinks, and character/range filters handle arbitrary outside-candidate characters
without enumerating Unicode. Invalid calls skip their actuals as in the original semantics.
Finite raw-declaration/root equality checks yield all original-string observations, accepted languages,
residuals, finite failure, finite-run existence and all-clock undefinedness.

The five-rule source has arities [2,2,1,1,0], and its fixed Seq grammar has 1,230 nullary rules.
Direct source and generated executions at clock8 check nesting depths 0/1/2, actual parent-dependent
child tuples, an argument containing a parameterized wrapper with a real recursive balanced producer,
reversed a/ab and ab/a views, return to the parent, and actual consumption of the outer retained ab.
Leaked child views reject. Balanced actual captures are checked at n=1/2/4. Other evidence includes
any/star and range/star captures of X outside the candidate alphabet, an actual repeating the parent's
empty retained word at nonempty suffix ab remaining undefined at all clocks, all-input/all-clock
undefined cycles through user calls inside actuals, ordered failure/divergence, malformed-call
argument skipping, and rejection of omitted guards. The same unchanged source under Seq fails
on a source-accepted example; this remains an operational contrast, not language-class separation.

The finite remaining-suffix replay guard is still essential to this construction. Unrestricted
retained-word replay and the general Par/Seq class equality or separation remain unresolved.


## Carrying an unbounded retained word alongside finite views

SubstringCaptureView and the RetainedViewFusion modules retain the actual first captured word
in a fixed unary Seq grammar while erasing the other values into finite metadata. Raw replay of
the first word has no finite-suffix guard and may occur in arbitrary control or dependent actuals.
Source declarations of positive arity must start with param_0 followed by the residual body;
nullary declarations start with eps. Mixed arities, mutual recursion and users inside actuals are
allowed. Every other direct retained reference still uses guard(R);param_i, where R is the suffix
closure of fixed seed words. This source shape is not claimed to normalize all Par grammars.

All seed substrings form the finite observation dictionary. A substring view determines every
state transition of each strict candidate-word DFA, including transitions from intermediate
states; words outside the dictionary reach a sink but remain real payloads for raw replay.
Normal/filter generation observes all actuals in the original order, then retains the first
actual parser as a real unary argument. The intermediate Par rules have the form param_0;tail.
Composing ReplayFusion removes that leading replay in Seq, matching actual consumption at the
call boundary. Root specialization is closed by literal substitution. All physical-clock results,
original-string observations/languages, residuals, finite failure and all-clock undefinedness are
preserved after finite raw-declaration/root checks, without semantic helper or termination inputs.

The source arities are [2,0,1] and the fixed target has 182 unary rules. Direct kernel source/target
runs at clock8 for (initial length, nesting depth)=(1,0),(2,1),(4,2) check a parent a^n, a newly
captured child a^(n+1) through a parameterized call inside an actual, another overlapping actual
through a nullary user, restoration and replay of the parent after return. Parent aa and child aaa
have equal Other metadata but different real payloads. Leaking the child or replacing the payload
by empty changes the result. Raw replay consumes lengths 2/4/7 outside the finite suffix region.
Another accepted source/target example retains length1 while the other actual captures lengths2/4,
so no longest-first or scanner-frontier condition is needed. Symbolic scanner evidence proves the
actual tuple [a^(n+1),a] for every n and clock. Nullable raw-payload repetition stays undefined on
every input at every clock, and missing leading replay is rejected by the complete checker.
Prefix-only b/c metadata for candidate ab is shown insufficient at intermediate state1; the actual
composed a;payload filter succeeds with the correct substring view and fails with the wrong Other.

The remaining restrictions are the leading first-word replay in positive-arity source rules and
finite-suffix references to other captured words. Arbitrary replay of multiple independent
unbounded retained words, and general original-string Par/Seq equality or separation, remain open.


## Independent original-origin projections of two unbounded captures

The DelimitedCopy modules translate a source two-argument rule with body
param_1;d;param_0;d;param_1;d, consuming a v d u d v d block for real actual captures u/v.
Neither value is replaced by finite metadata and neither replay has a finite suffix guard.
Actuals may be arbitrary closed expressions over an independent nullary mutually recursive PEG
library. Finite capture-mask and closure checks establish that consumed data uses an alphabet
excluding the delimiter; they require no maximal scanner endpoint, parser factorization, capture
length bound, finite word palette or termination assumption. The library cannot call the copy rule.

Two unary Seq users retain u and v separately. The u pass starts after capturing u, skips the
rest of the first word to d, checks u, and skips the third word to d. It runs in lookahead.
The v pass starts from the original position, captures v, skips the middle word and checks v.
Original left-to-right actual preflight runs before either projection. Unique delimiter splitting
proves that both passes select the same boundaries and return the actual source suffix after the
final d. Block suffix transformers, actual physical tables at every same clock, finite failure,
finite-run existence and all-clock undefinedness agree. Raw declaration/root AST checks compose
these blocks under ordinary helper, seq/choice/not/star and character control. The source input is
unchanged, including all text after a block; there is no input encoding or full-input alphabet bound.

The example has A=a* b and B←a B c / b. Source arities [0,0,0,0,2] become fixed target arities
[0,0,0,0,1,1]. Actual DerivesArgsPar captures [a^n b,a^n b c^n] are proved for every n and arbitrary
continuation, with both values exceeding every fixed length bound. Both grammars accept v#u#v#
for every n. Direct kernel runs at clock12 cover n=0/1/2/4, copy/balance rejection, residual !X,
star over blocks with different n, and choice/negation/literal continuation contexts. A's successful
endpoint is strictly before the alphabet scanner frontier. Later-actual cycles stay undefined for
all inputs/clocks; early failure still precedes them. Counterexamples establish why ordered preflight
and delimiter safety are checked, and malformed actual declarations are rejected. Pure actuals
retain the precise unresolved/resolved distinction at physical clocks0/1.

The earlier no_finite_summary theorem concerns only the bare suffix c^m and prefix-selected finite
control plus opaque a^n b. This construction instead reruns complete parsers from the original
position and checks later copies; it is not a contradiction of that interface theorem or a language
class separator. Arbitrary two-retained-value bodies, parent-dependent actuals and callbacks from
the independent library are not covered here. The general original-string class question remains open.


### Arbitrary-arity delimited word patterns

The DelimitedWordPattern and DelimitedPatternPasses lemmas replace the fixed two-word layout with any nonempty finite list of in-scope retained-parameter indices. The source body is a sequence of those parameters, each followed by the separator. Repeated and unused indices and empty captured words are allowed. Each unary Seq projection checks all occurrences of its own actual captured word, skips the other segments, and adjusts its first segment for the already-consumed Seq argument. Delimiter-free captures and common source origin synchronize every projection boundary and the actual returned suffix. The finite ordered conjunction equals the source partial suffix transformer, not only its whole-input acceptance test.

DelimitedPatternEvaluation connects actual argument evaluation, source rows, generated unary rows, ordered preflight, and physical clock zero. DelimitedPatternCompiler checks the complete raw source grammar/root, helper independence, capture effects, nonempty arity/pattern and reference scope; its physical, observations, language, definedness and undefinedness theorems have no semantic oracle as compiler input. The four-argument example produces six Seq rules from three source rules. Symbolic source derivations capture a^n b c^n, a^n b, a^n and the empty word for every n and every following suffix, and both fixed grammars accept every corresponding seven-segment block. All three nonempty capture lengths are simultaneously unbounded. Direct kernel examples include n=0/1/2/4, reordered indices, copy failure, suffix preservation, real later-argument divergence and the necessity of preflight.

This frontend uses independent nullary helper libraries, closed actuals, delimiter-free captured outputs and one source copy call at the root. RecursivePattern above combines these arbitrary-arity patterns with transformed client callbacks and general expression contexts. Arbitrary parameter-dependent actuals and arbitrary multi-value bodies, and hence the unrestricted Par/Seq class question, remain open.


### Recursive arbitrary-arity word patterns

DelimitedPatternCallTransfer relates calls whose source and target actual-expression lists differ. RecursivePattern then transforms every actual and nullary client body, allowing copy calls nested inside actual queries and client/copy/actual mutual recursion for arbitrary positive copy arity and arbitrary nonempty occurrence lists. Mutual expression/argument induction and simultaneous actual-table clock induction discharge the local correspondence premises. The compiler checks complete raw declarations/root, recursive client scope, copy arities and source capture effects, and preserves original-string observations, residuals, language, finite definedness and all-clock undefinedness at the same physical clock. It does not use independent helper semantics, frozen rows, termination advice or a bounded captured-word palette.

The eight-rule source compiles to eleven fixed Seq rules. Each of its four actuals queries the following block before returning the real tuple [a^n b c^n, a^n b, a^n, empty]. Symbolic derivations cover every n and every following block-length list; both grammars accept arbitrary finite streams of these blocks. Direct kernel runs check different block lengths, actual tuples, residuals, invalid later blocks, direct nested copy queries, transformed client syntax and rejection by the older independence check. Genuine same-position copy/actual cycles stay undefined on every input and clock; omitting preflight exposes finite failure before a divergent later actual. Invalid arities, references, delimiter captures and raw source declarations are rejected.

Clients remain nullary, actuals closed and captured outputs delimiter-free. Copy occurrences share one chosen arity, separator and finite parameter-occurrence list; the body consists of retained-word segments followed by separators. Positive inner-copy outputs containing that separator cannot themselves be captured by an outer copy; nested lookahead is supported. General parameter-dependent actuals, arbitrary multi-value callee bodies and the unrestricted language-class equality/separation remain unresolved.


### Parent-dependent actuals with a real retained payload

ParentPatternTransfer generalizes capture safety and arbitrary-arity copy-call transfer to an arbitrary caller environment. RetainedPattern combines that transfer with unary leading-replay clients: the source rule is param_0;tail and the Seq rule contains the transformed tail. Parent-dependent actual queries may call unary clients with the parent's real word and choose different consumed producer results. Client bodies and unary actuals can consume the retained word directly, capture a new concatenated word for a recursive child, and use the original parent after return. Actual evaluation retains the caller environment; each generated copy pass receives its own fresh captured word. Simultaneous actual-table clock induction relates the source replay origin to the Seq argument endpoint without abstracting the retained parent into a finite view.

The full raw-grammar/root checker validates the independent nullary helper prefix, client and parent scope, copy arity/occurrence indices and capture effects. Observations, original-string language, all residuals, finite failure/definedness and all-clock undefinedness correspond at the same physical clock. Five source rules with arities [0,0,1,1,4] become eight fixed Seq rules. On the same current input, actual capture tuples differ under parents a and aaa. A parent containing the separator a# is allowed; only fresh copy-captured outputs exclude the separator. Direct runs cover real recursive child doubling, parent restoration, empty parents, child-prefix failure and leaked-child-value rejection.

Symbolic source derivations establish the actual tuple [a^n b c^n,a^n b,a^n,empty] after substituting the retained parent a^n for every n and every following suffix. Both grammars accept every initial parent length and every recursive nesting depth, with children capturing ww from the actual argument w;w and parent continuations replaying their own original w. True parent/copy-actual cycles and nullable retained-parent stars stay undefined on every input and clock; preflight omission gives finite failure before a divergent actual. Invalid root parent scope, client addresses and source declarations are rejected.

Unary clients still require leading replay. The copy header still has one selected separator and parameter-occurrence list; positive fresh-capture paths must be checked delimiter-free. Parent replay or unary clients inside such positive paths are currently rejected, while zero-width queries and query-driven producer choices are supported. Independent nullary helpers remain available for consuming producers. Arbitrary multi-parent clients, arbitrary multi-value callee bodies and the full language-class equality/separation question remain unresolved.


### Positive parent consumption and recursive returned-word effects

RetainedCaptureEffects proves checked source consumption effects for real unary clients. Under an alphabet-safe actual captured word, an enabled client replays that word and its tail consumes only alphabet characters. Candidate return flags are computed from source tails and independently checked for recursive closure; actual source rows satisfy the certificate by physical-clock induction. Successful output can be empty or unbounded, and clients can diverge. ConsumingPatternChecks validates selective parent-alphabet requirements on every client call, including initial root captures. Copy actuals may positively replay the parent or call certified unary producers with safe actuals. Unmarked clients still accept arbitrary parent words, including the separator, in ordinary calls.

The existing fixed source/target grammar builders are reused. Parent-word preconditions are propagated through actual captured values in the source/target row correspondence. Complete raw declaration/root, scope, argument, capture and return-effect checks preserve all original-string observations/languages, residuals, finite failure/definedness and all-clock undefinedness at the same physical clock. No runtime word/endpoint advice, termination assumption, finite word palette, maximal scanner frontier or input encoding is supplied.

The five-rule source compiles to eight Seq rules. For a retained parent a^n, its actual tuple [a^(2n)b c^(2n),a^n,a^(2n),a^(2n)b] contains direct parent consumption and the actual returned word of a parameterized recursive producer. Symbolic derivations cover every n and following suffix; both grammars accept every parent length and nesting depth with child doubling and parent restoration. All four capture lengths are simultaneously unbounded. With an empty argument the same producer recursively captures a^m for every m. A return-certified divergent client is allowed as a positive actual and stays undefined on every input and clock; omitting preflight produces finite failure. Kernel checks reject missing parent requirements, an unsafe marked seed and a separator-consuming producer actual, while allowing a separator-containing parent for an unmarked ordinary producer call. Earlier query-only validation rejects this grammar.

Independent nullary helpers, leading replay in unary clients and shared delimited parameter-list copy bodies remain restrictions. Marked parent values must satisfy the finitely checked alphabet condition. General multiple-parent clients, arbitrary multi-value bodies and unrestricted Par/Seq class equality/separation remain unresolved.

## Controlled retained-word body translation (latest extension)

CopyBodyControl/Evaluation/Projections/Emission and ControlledCopySyntax/Correspondence/Compiler extend flat delimited parameter lists to finite bodies of param_i;d atoms, epsilon, failure, sequence, committed ordered choice, negation and structurally zero-width repetition. Finite syntax histories are tested from the original copy origin; captured words remain unbounded. Separate CPS continuations preserve committed choice. Original-order actual preflight and a nullary initialization gate preserve failure/divergence and clock-zero behavior, even for empty bodies.

ControlledCaptureEffects connects the actual grammar's recursive return-effect certificates, positive parent consumption, parameterized recursive producers and parent restoration to the same-physical-clock proof. Complete source/root and finite scope/effect checks yield original-string language and residual preservation, finite failure/definedness and all-clock undefinedness. The five-rule example generates 97 fixed Seq rules. Symbolic proofs cover every parent length and recursion depth with actual unbounded captures and child doubling. Kernel cases cover alternative post-consumption choice paths, incorrect continuation distribution, missing initialization/preflight, early argument failure, value-dependent nullable repetition and malformed scope/body rejection.

Validation: full lake build including Audit passes (1,310 jobs). All 3,075 related public dependency reports use only standard axioms (3,014) or no axioms (61); the 97 new reports are guarded in Audit. The PR has 1,443 new guarded dependency checks across 134 new Lean modules. Consuming body repetition, general header recursion, arbitrary body atoms, multiple-parent clients and the unrestricted Par/Seq class comparison remain unresolved.

## Consuming delimited repetition through EOF (latest extension)

RepeatedWordPattern synchronizes arbitrarily many repetitions of any fixed nonempty parameter-index pattern, with arbitrary positive arity, occurrence order and repetition, and unbounded delimiter-free retained words (including empty words). Each unary pass checks its own retained word and skips other segments. Successful full-input passes have the same delimiter count, hence the same unbounded iteration count. The first pass starts after its actual Seq argument endpoint; later iterations use the whole fixed pattern. DelimitedRepeatEvaluation derives the real greedy evStar semantics from strict progress and finite traces, with no iteration bound or language oracle.

RepeatedWordTransfer preserves actual Par/Seq calls at every physical clock in arbitrary caller environments, conditional on local actual correspondence and checked capture freedom. RepeatedCopySyntax/Correspondence/Compiler discharge those premises using complete raw-source/root checks, parent requirements, return effects and simultaneous client-table induction, including positive parent consumption and parameterized producer calls inside actuals. Original-string languages, residuals, finite failure/definedness and all-clock undefinedness are preserved.

The five-rule source generates nine fixed Seq rules. Symbolic proofs cover every parent length and every positive consuming repetition count with real captures. Kernel checks include recursive positive producers, 0/7/21 separator inputs with empty actuals, excess input, invalid scope/patterns, initialization/preflight omissions, early argument failure and true cycles undefined on every input and clock. Without EOF the two real unary passes on ab#a#ab#b# stop after different iteration counts; this is a limitation of the proposed transformation, not a class separator. General stopping frontiers, arbitrary bodies and unrestricted Par/Seq class equality/separation remain unresolved.

Validation: full lake build including Audit passes (1,319 jobs). All 3,167 related public theorem dependency reports use standard Lean axioms (3,100) or none (67); the 92 new reports have matching Audit guards. This extension adds nine Lean modules.

## Exact general stopping frontiers (evaluator theorem, not a new grammar compiler)

SynchronizedStarFrontier proves that greedy iteration of a synchronized conjunction stops at the maximum remaining-input position among the independently iterated component evaluators. The premises concern one actual finite consuming step, not iteration bounds or a termination oracle. RepeatedWordFrontier discharges them for arbitrary nonempty delimited parameter patterns and delimiter-free retained tuples, with arbitrary input, residual and valid source/view tables. An arbitrary continuation runs at that calculated frontier in the original environment. No EOF or finite suffix guard is used.

RepeatedFrontierTransfer connects this formula to actual Par calls and actual unary Seq calls at their differing argument endpoints, in an arbitrary caller environment, when actuals and the first complete iteration succeed. Zero iterations are handled separately. The two real examples with a/ab captures show that either component can stop first; neither fixed consuming component is correct on all inputs, and using the other frontier loses the original continuation.

The maximum operation is an explicit Lean calculation on evaluator results, not an MExp, a grammar closure assumption or a general Par-to-Seq construction. Selecting that frontier in a Seq grammar remains unresolved, as do unrestricted class equality/separation. The established EOF compiler retains its stated scope.

Validation after this addition: full lake build including Audit passes (1,323 jobs). All 3,193 related public dependencies are standard (3,125) or axiom-free (68). This addition has 26 public theorem guards in four new modules; PR69 totals 118 new guards across 13 new Lean modules.

## Finite status-only selection cannot repair the frontier (restricted compiler obstruction)

FrontierStatusSelector compiles arbitrary finite branching selectors into actual first-order expressions. Guards may combine whole-projection lookahead with sequence, ordered choice, negation and zero-width repetition, including undefined nullable loops. Leaves select one of the two original consuming projections, fail or diverge. When both probes succeed, the selected leaf is independent of their returned endpoints.

FrontierSelectorObstruction proves that every such selector fails to preserve the original residual on one of the two fixed a/ab examples. All positive evaluation clocks give the same output; no clock and no alternative finite derivation recovers the correct residual observation. The fixed projection grammar and all generated roots are first-order. This excludes this status-only selector compiler, not arbitrary Seq grammars or language-preserving translations. Input-sensitive guards, additional recursive selector rules and different retained-word representations are outside the theorem.

Validation: full lake build including Audit passes (1,325 jobs); all 3,210 related public dependency reports are standard (3,140) or axiom-free (70). This addition has 17 guarded public theorems in two modules; PR69 totals 135 new guards across 15 new Lean modules. General frontier selection and unrestricted class equality/separation remain unresolved.

## Whole-block recapture removes the EOF restriction for fixed copy periods

RecapturedCopyBlock/Transfer and RecapturedCopySyntax/Correspondence/Compiler translate a bare greedy star of any fixed nonempty delimited parameter pattern. After original-order actual preflight, finite origin projections test the first complete block. Failure gives zero-iteration success at the original position. On success, a fixed delimiter skeleton captures the entire real first block B and calls one new unary Seq row whose body is param_0*. The Seq argument has consumed the first block, so the body consumes only subsequent copies. Source pattern evaluation equals literal B; the scanner's actual captured span is proved to equal B. No comparison of individual projection endpoints, EOF guard, synthetic input or endpoint oracle is used.

The local theorem preserves all physical clocks, arbitrary caller environments and transformed actuals. Full raw grammar/root, scope, original capture effects, parent requirements and recursive return-effect closure are checked. Simultaneous client-row induction preserves original-string languages, residuals, finite failure/definedness and all-clock undefinedness in arbitrary checked control contexts. The older status-only selector obstruction remains valid: this construction captures a different composite word and uses a new consuming row.

The former a/ab frontier counterexamples now return the correct five/four-character residuals and admit their original continuations. Actual Seq capture is ab#a#. The five-rule recursive source generates nine fixed unary/helper Seq rules. Symbolic proofs cover every parent length, every positive block repetition count and every recursion depth with child doubling and parent restoration. Kernel runs also cover zero iterations, failed preflight, removed first-block verification, empty original captures consuming delimiters with a partial-block remainder, recursive consuming producers and true cycles.

Validation: full lake build including Audit passes (1,332 jobs). All 3,274 related public dependencies use standard Lean axioms (3,204) or none (70). This extension adds 64 guarded public theorems in seven modules; PR69 totals 199 new guards across 22 new Lean modules. The period remains a fixed delimited parameter list. General PEG iteration with varying per-iteration consumption, arbitrary bodies, multiple-parent clients and unrestricted Par/Seq equality/separation remain unresolved.

## Input-dependent iteration control after a recaptured anchor

CopyPeriodControl and ControlledPeriodTransfer/Syntax/Correspondence/Compiler translate `(P(W); T[P(W)])*` where P is a fixed nonempty delimited parameter pattern and T is arbitrary finite PEG control over a complete-block atom, terminals and independent nullary recursive helpers. T includes sequence, committed choice, negation and consuming/nullable stars, so different iterations may consume different words and arbitrarily different amounts of input.

After checked actual preflight and a first-anchor test, a unary probe captures the real anchor block B and evaluates T[B]. Failure rolls the whole first iteration back to zero consumption; undefinedness propagates. On success another unary call captures B and executes T[B];(param_0;T[B])*. Source and target use the same physical helper-row clock. Helper prefix scope/closure and all source/root/capture/parent/return-effect checks are finite. The source tuple is related to the real singleton B environment throughout control and helper returns; whole-source language, residual, finite failure/definedness and all-clock undefinedness are preserved.

The five-rule source generates ten fixed Seq rules. Symbolic proofs cover every parent length, every nonempty Boolean branch sequence and every recursive nesting depth, with child doubling and parent restoration. Kernel executions cover consuming inner repetition, negative retained-block tests, rollback after committed-choice failure, omitted-probe errors, recursive balanced helpers followed by retained-block replay, exact helper clocks and value-independent nullable divergence at every clock.

Validation: full lake build including Audit passes (1,339 jobs). All 3,335 related public dependency reports are standard (3,262) or axiom-free (73). This addition has 61 guarded public theorems in seven modules; PR69 totals 260 new guards across 29 new Lean modules. General body control that uses tuple components separately, parameterized calls inside the iteration tail, anchor-free iteration and unrestricted Par/Seq equality/separation remain unresolved.
