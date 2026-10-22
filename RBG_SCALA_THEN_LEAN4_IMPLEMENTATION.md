# Region-Borrowing Grammars: Scala → Lean 4 Implementation Plan

> **For agentic workers:** 利用可能なら `superpowers:executing-plans` または `superpowers:subagent-driven-development` を使い、下記のタスクを順に実施する。チェックボックスは実際に検証を通してから更新する。別タスクを並行実装する前に、共有するADTと意味論を固定する。

**Goal:** 入力区間と明示的な借用参照を持つ研究用文法体系を、まずScalaの純粋なEvaluatorとParser Combinatorで実装・検証し、そのScala実装を構成要素ごとにLean 4へ移して主要性質を証明する。

**Architecture:** 文法はホスト言語の関数を保持しない有限のfirst-order ASTとする。メモ化なしのScala参照Evaluatorを基準に、Combinator、例題、依存解析、メモ化版を積み上げる。Scala側の仕様と回帰テストが固定されてから、同じデータ構造・分岐・状態遷移をLeanへ移す。

**Tech Stack:** Scala 3.3.8 LTS、JDK 21、sbt 1.11.7、MUnit 1.2.1、Lean 4.31.0 / Lake。Scala本体は標準ライブラリのみ。Leanはまず標準ライブラリとStdのみ。

**Spec:** 本書の「Part I — 仕様」を規範仕様とし、「Part II — 実装計画」で実装する。実装先では本書を `docs/RBG_SCALA_THEN_LEAN4_IMPLEMENTATION.md` に保存し、仕様変更は差分と理由を残す。

**Status:** 研究用の提案仕様・実装指示書。現時点でこの文法のScala実装やLean証明が完成しているという主張ではない。作成日: 2026-10-05。

## Global Constraints

- 進め方は **naive-functional Scala → Scalaで実験・仕様固定 → 対応するLean実装 → 証明** とする。Scalaの実装前に別アーキテクチャのLean証明を作り始めない。
- ADT、immutable data、pattern matching、小さい純粋関数、明示的state threadingを優先する。Cats、ZIO、汎用effect framework、過度なtypeclassは導入しない。
- 研究名は暫定的に **Region-Borrowing Grammars (RBG)**、packageは `com.github.kmizu.rbg`、Lean namespaceは `Rbg` とする。
- 新規の独立プロジェクトとして実装する。既存のMacro PEG、pal-peg、lean4-pegを無断で変更しない。既存checkoutを指定された場合はその作業規則と未コミット差分を先に確認する。
- 本書ではバージョンを再現性のため固定している。「最新」という意味ではない。導入時に依存解決を実行し、変更が必要なら理由・新旧バージョン・検証結果を記録する。[R5–R9]
- 入力はバイト列。座標はUTF-16 indexでもUnicode code point indexでもなく、常にバイトoffsetである。
- 文法選択はordered choice。通常の不一致、fuel切れ、実行上のfaultを混同しない。
- 参照Evaluatorは不変の全入力を保持する。ストリーミング、物理的な入力回収、Cut、AST生成、コード生成、高階文法はv0に入れない。
- Combinatorのラムダは構築時だけ実行する。完成した文法やEvaluatorにホスト言語のclosureを残さない。
- 数値を扱うv0拡張は入力中の十進長さフィールドだけ。任意計算、semantic predicate、`flatMap`による実行時文法生成を入れない。
- メモ化前後で同じfuelに対する意味上の結果を一致させる。高速化のために失敗の定義を変えない。
- 有限テスト、Lean内の定理、Scala/JVM実装の形式検証を別々に表示する。差分テストはScala/JVM実装の形式検証ではない。
- 線形時間、一般停止性、新規性、PEGへの包含・分離は、証明または根拠のないままREADMEに書かない。

## Review Focus

1. **右端消費後の失敗:** ordered choiceは左境界だけでなく右境界も復元する。Task 2で検証する。
2. **両端消費のキャプチャ:** 左右から消費した二つの区間を一つの連続Spanとして扱わない。Task 3で検証する。
3. **fuel切れと否定:** `not`やordered choiceが`OutOfFuel`を通常の不一致に変換しない。Task 2で検証する。
4. **同じ位置・違う文脈:** 借用Spanや右境界が異なる結果を誤ってメモ再利用しない。入力間のcache再利用もしない。Task 7で検証する。
5. **内部区間とバイト長:** 内部の`Empty`はローカル終端であり、UTF-8文字を文字数で数えない。Task 5で検証する。

---

# Part I — 仕様

## 1. 研究の位置づけと今回の範囲

RBGの核は「入力の担当区間」と「その外を含めて参照できる借用区間」を区別し、解析結果への依存を文法ASTから追えるようにすることである。

ただし、区間を扱う文法、文脈依存パターン、状態を含むメモ化は既存研究にある。特に **Interval Parsing Grammars (IPG)** は入力区間・属性・ファイル形式解析を扱う直接の比較対象である。[R1] Nezの記号管理、Principled Stateful Parsing、バックリファレンスの計算量研究も比較する。[R2–R4]

このプロジェクトの最初の成果は「新しい言語クラスを確立すること」ではない。次を動かして確かめ、必要な性質を形式化する。

- 左右の境界を持つ決定的な認識器。
- 連続した入力区間の字句的な束縛と、明示的な引数渡し。
- 規則や式が必要とする参照だけを使うメモ化キー。
- 上記の実行可能な意味論と依存解析の健全性。

### v0の完了対象

Scalaの参照Evaluator、AST構築Combinator、PAL / 区切り付きCOPY / 簡易タグ / 長さ付きフレーム、依存解析、full-environment / projected-environmentメモ化、Scala→Leanのfixture出力、Leanの主要証明、再現手順を含む。

### 後続研究へ分離するもの

実際の入力解放とメモ表回収、Cut、一般的な停止性判定器、left recursionの特殊処理、fuelをキーから外す最適化、実用XML準拠、任意の属性計算、高階Macro PEG、SCA/PEGへのコンパイル、LLM constrained decodingは後続とする。特に寿命・回収は、依存解析ができたという理由だけで「解決済み」にしない。

## 2. 入力と状態

### 2.1 入力

Scalaではimmutableな`Vector[Byte]`を用いる。外部の`Array[Byte]`は入口でコピーする。文字列入口は明示的なUTF-8変換とする。

Scalaの`Byte`の符号付き表現は実装上の都合であり、アルファベットは0〜255。集合の正規化やfixture出力では`b & 0xff`を使う。Lean側は`List UInt8`を用い、値とoffsetの対応を明記する。LeanのListによる参照実行の速度をScalaのVector実装と同じと仮定しない。

### 2.2 区間

`Span(lo, hi)`は半開区間`[lo, hi)`であり、有効条件は`0 ≤ lo ≤ hi ≤ input.length`。

実行中の担当区間も同じ構造を使う。成功後の残余区間は`[lo', hi')`であり、次を満たす。

```text
lo ≤ lo' ≤ hi' ≤ hi
```

両端から消費すると、空になった時点の一致位置は区間の中央でもよい。完全消費は **`lo' == hi'`** であり、`lo' == 元のhi`ではない。

### 2.3 環境

`Env = Map[SlotId, Span]`とする。Spanは常に同じ不変入力に対する参照で、文字列コピーではない。

環境はimmutableであり、`Success`に変更後環境を含めない。束縛は本体の内側だけで有効。借用先は担当区間の外にあってもよいが、入力全体の範囲内でなければならない。

v0は物理的なメモリ所有権システムではない。「borrowing」は読み取り専用の入力参照を指す。任意の有効Spanを渡すlow-level APIも扱うため、参照と担当区間が非交差であることを一般前提にしない。

### 2.4 型の契約

以下はインターフェース契約であり、ここにない型を暗黙に導入しない。実装担当はこの契約を実際のコンパイルで確認する。

```scala
final case class ExprId(value: Int)
final case class RuleId(value: Int)
final case class SlotId(value: Int)
final case class Span(lo: Int, hi: Int)
type Env = Map[SlotId, Span]

final case class Rule(name: String, params: Vector[SlotId], body: ExprId)
final case class Grammar(
  nodes: Vector[Node],
  rules: Vector[Rule],
  entry: ExprId
)

enum EvalResult:
  case Success(rest: Span)
  case Failure
  case OutOfFuel
  case Fault(kind: EvalFault)

enum EvalFault:
  case InvalidCursor, InvalidBorrow, MissingSlot
  case InvalidExpr, InvalidRule, ArityMismatch
  case NonLeftCapture, NonProgress
```

`EvalFault`は意味上の分類だけを持つ。呼出しstack、全環境、実行順依存のログを`EvalResult`に含めない。診断情報は別レイヤーにする。

公開入口には`ValidationError`と`InputError`も用意し、構築時の誤り・不正な入口引数・解析中のfaultを区別する。負のfuelは`InputError`。core関数の前提は非負fuelとする。

## 3. 文法の有限表現

### 3.1 Node

文法を有限のnode arenaとして保持し、子式は`ExprId`で参照する。AST上の循環は許さず、再帰は`Call`からだけ表す。

```scala
enum Node:
  case Eps, Reject, Empty
  case AnyL, AnyR
  case LitL(bytes: Vector[Byte])
  case LitR(bytes: Vector[Byte])
  case ClassL(bytes: Vector[Byte])
  case ClassR(bytes: Vector[Byte])
  case Seq(first: ExprId, second: ExprId)
  case Choice(first: ExprId, second: ExprId)
  case Not(body: ExprId)
  case Many(body: ExprId)
  case BindL(slot: SlotId, capture: ExprId, body: ExprId)
  case ExactL(slot: SlotId)
  case ExactR(slot: SlotId)
  case Call(rule: RuleId, args: Vector[SlotId])
  case Within(length: Int, body: ExprId)
  case WithinDec(lengthSlot: SlotId, body: ExprId)
```

`Within`と`WithinDec`は長さ拡張のnodeであり、Task 5で追加する。それ以前のCoreの性質と、追加後に再確認する性質を区別する。

集合はunsigned byteの昇順・重複なしに正規化する。空literalは`Eps`へ構築時に正規化し、空classは`Reject`へ正規化する。fuel比較では正規化後の同じGrammarを使う。

### 3.2 node ID、rule ID、slot ID

- arena内では子ExprIdが親ExprIdより小さいことを要求し、有限な構文のDAGにする。
- ruleは先に宣言して後でbodyを定義できる。再帰は`Call(ruleId, args)`で表す。
- paramとBindLのSlotIdは、異なる宣言ごとに一意に発行する。名前の文字列を同一性に使わない。
- 同じBindL nodeの再帰的実行は問題ない。実行時環境が呼出しごとに分かれるからである。
- 引数なしのstart ruleへの`Call`をentry nodeとして生成する。entryの自由変数は空である。
- 規則名重複、未定義規則、不正ID、arity不一致、scope外参照をValidatorで拒否する。

## 4. 評価結果とfuel

### 4.1 通常の失敗と実行未完了を分離する

`Failure`だけがordered choiceの次の候補を試す理由となる。

`OutOfFuel`と`Fault`はそのまま上位へ伝播する。以下を禁止する。

```text
OutOfFuelをFailureに変える
!OutOfFuelを成功にする
Faultをmanyの正常終了にする
再帰中の同じ状態を見つけたというだけでFailureにする
```

文法`A = A / Eps`は有限fuelでは`OutOfFuel`になる。右の`Eps`を試して成功させてはならない。

### 4.2 fuelの定義

v0のfuelは **評価導出の深さ上限** であり、全体の命令数予算ではない。

```text
evalFuel(0, ...) = OutOfFuel

evalFuel(k + 1, node, state):
  primitiveはこの深さで結果を返す
  直下の子評価はすべてfuel = kで実行する
```

Seqの第二項、Choiceの第二候補には、第一項と同じ`k`を渡す。第一項の「残fuel」は存在しない。Manyの繰返しも、後述する再帰規則に従って`k`へ減らす。

nodeごとに条件チェックを行う順序も固定する。`fuel == 0`を最初に処理し、その後にcursor・node IDなどを検査する。各operatorが参照を読む時点で該当Spanを検査する。未使用の環境全体を毎回走査する検証を意味論に混ぜない。

この定義なら、「一度`OutOfFuel`以外で確定した結果は、fuelを増やしても変わらない」を証明対象にできる。ただし深さfuelは実行node総数や時間の上限を直接意味しない。計測用のnode visitsやbyte comparisonsは別に数える。

### 4.3 公開関数

```scala
def evalFuel(
  fuel: Int, grammar: Grammar, expr: ExprId,
  input: Vector[Byte], cursor: Span, env: Env
): EvalResult

def parseAll(
  grammar: ValidatedGrammar, input: Vector[Byte], fuel: Int
): Either[InputError, FullResult]
```

`ValidatedGrammar`はValidatorが成功したGrammarを包む型。`FullResult`は`Accepted`、`Rejected`、`OutOfFuel`、`Fault`を持つ。

`parseAll`はentryを`[0,n)`・空環境で評価する。Successで残余が空ならAccepted、残余があればRejected、FailureならRejected。他の二つはそのまま返す。残余があったからといって過去のordered choiceに戻らない。

利便関数`accepts`を提供する場合も、`Either[RunIssue, Boolean]`とし、OutOfFuelを`false`に潰さない。

## 5. Coreの操作的意味論

以下はすべて、同じ入力・同じGrammarのもとでの評価である。失敗結果は部分消費後のcursorを持たない。

### 5.1 primitive

| Node | 意味 |
|---|---|
| Eps | 現在区間を変えず成功 |
| Reject | Failure |
| Empty | `lo == hi`のときだけ成功 |
| AnyL / AnyR | 非空区間の左端 / 右端を1byte消費 |
| LitL(s) | `s`が現在区間のprefixなら左から消費 |
| LitR(s) | `s`が現在区間のsuffixなら右から消費 |
| ClassL(S) / ClassR(S) | 対応する端の1byteがSに含まれれば消費 |
| ExactL(x) / ExactR(x) | 借用Spanのbyte列を通常順でprefix / suffix照合して消費 |

右から読む場合もliteral自体を反転しない。

```text
LitR("ab")                  は "ab" に成功し、"ba"には失敗する
LitR("a") ~ LitR("b")      は "ba" に成功する
```

照合前に長さが担当区間内に収まることを検査する。左右の境界を越えて同じbyteを二重消費しない。Exactの比較対象は同じ入力内の有効Spanであり、照合はhashだけで判定しない。空SpanのExactは無消費成功になる。

### 5.2 SeqとChoice

`Seq(p,q)`はpのSuccessの残余区間でqを評価する。pがそれ以外ならその結果を返す。qが失敗しても、外側に部分的に変更された状態は返さない。

`Choice(p,q)`はpがFailureのときだけ、**Choice開始時と同じ左右境界・同じ環境** でqを評価する。pがSuccessならqは試さない。

```text
("a" / "ab") ~ Empty           は "ab" に失敗する
("a" ~ Empty) / ("ab" ~ Empty) は "ab" に成功する
```

### 5.3 Notと派生lookahead

`Not(p)`はpがSuccessならFailure、pがFailureなら元の区間でSuccess。OutOfFuelとFaultは伝播する。

内部評価が消費した左右境界も局所束縛も外へ出さない。`and(p)`は`Not(Not(p))`への構築時展開とする。fuelの消費もその展開後のASTどおりであり、primitive1個として数えない。

### 5.4 Many

`evalFuel(k+1, Many(p), s)`は次の規則にする。

1. `evalFuel(k, p, s)`がFailureなら、sでSuccess。
2. Success(s')かつ`length(s') < length(s)`なら、`evalFuel(k, Many(p), s')`を返す。
3. Successしたが区間長が減っていなければ`Fault(NonProgress)`。
4. OutOfFuel/Faultなら伝播。

greedyかつpossessiveであり、後続失敗を理由に繰返し回数を減らさない。

`optional(p) = Choice(p,Eps)`、`plus(p) = Seq(p,Many(p))`とする。nullableなpをManyに入れるのは、暗黙の終了ではなく明確な問題として報告する。一般的なnullable解析をv0の完了条件にはしない。

### 5.5 BindL

`BindL(x,p,q)`を元区間`[lo,hi)`で評価する。

1. pを元環境ρで評価する。xはpのscope内にはない。
2. pがSuccess(`[mid,hi)`)なら、捕捉Spanは`[lo,mid)`。
3. qを残余区間`[mid,hi)`と`ρ[x ↦ [lo,mid)]`で評価する。
4. qの結果だけを返し、外側環境はρのまま。
5. pがSuccessしたが右境界が変化していた場合は`Fault(NonLeftCapture)`。
6. p/qの通常失敗、OutOfFuel、Faultはそれぞれ区別して伝播する。

**任意の両端消費式を一つのSpanとしてcaptureしてはならない。** BindLのpには、後述する`mayConsumeRight(p) == false`をValidatorで要求し、参照Evaluatorにも動的guardを残す。

Notの内部で右端を読むことは許される。Not自体は右境界を変えないからである。同様に、Within内部の両端消費は、Withinが外側では左側の一つの領域を消費するならBindLに入れられる。

### 5.6 Call

`Call(A,[x1,...,xm])`は、現在環境から対応するSpanを取得し、Aの仮引数だけを含む新しい環境を作ってA.bodyを評価する。

規則本体は呼出し元の任意の局所変数を暗黙に参照できない。借用が必要なら引数で渡す。動的scopeやホスト言語closureによる参照を禁止する。

v0はすべての実引数を解決してから呼び出す。依存射影はメモ化キーだけに適用し、実行環境そのものから未使用引数を削除しない。この区別はMissingSlotの扱いを変えないために必要である。

## 6. 長さ拡張

### 6.1 Within(n,p)

元の区間を`[lo,hi)`とする。nは非負整数で、`n ≤ hi-lo`を先に検査する。

pには内部区間`[lo,lo+n)`を渡す。pがSuccessし、その残余が空なら、外側の結果を **`Success([lo+n,hi))`** とする。内部の一致位置が中央であっても、この外側の更新は変わらない。

内部で未消費部分が残るかFailureなら、Within全体はFailure。OutOfFuel/Faultは伝播する。内部の局所束縛を外へ出さない。

pの通常の読み取りは内部区間に制限される。ただし明示的に渡した借用Spanの参照は許す。「明示的借用を含めて外の入力を絶対に読まない」という意味ではない。

### 6.2 WithinDec(x,p)

xの捕捉Spanを、非空のASCII十進数字列として解釈する。先頭ゼロは許可、符号・空文字・非数字は不許可。不正な数字列や残区間より大きい値はFailureとする。参照自体の欠落や不正SpanはFault。

数値は`cap = hi-lo`を上限として読み、上限超過を加算・乗算の前に検出する。ScalaのInt overflow、`String.toInt`例外、無制限なBigInt構築に依存しない。

```text
acc < cap / 10
または
acc == cap / 10 かつ digit ≤ cap % 10
```

を次の桁を取り込める条件にする。すべての桁を取り込んだnについてWithinと同じ処理をする。数値解釈自体はprimitive内部の有限走査であり、fuelは追加消費しないがbyte比較・走査回数は計測する。

### 6.3 必須の境界例

- `Within(0, Empty)`は成功する。
- `Within(0, AnyL)`はFailure。
- 内部で左と右から消費して中央で出会った場合も、外側ではn byteを消費する。
- `2:é,`はUTF-8の2byte payloadとして受理する。`1:é,`は拒否する。
- length-fieldが数百桁でも例外やoverflowではなくFailureになる。
- 内部の`Empty`を入力全体の終端判定へ置換しない。

## 7. Combinator API

### 7.1 目的

Parser Combinatorは **文法ASTを組み立てる薄いAPI** とする。`Input => Result`というホスト言語関数の合成を意味論の本体にしない。

`P`はExprIdへのhandle、`Borrow`はSlotIdへのhandle、`RuleRef`はRuleIdとarityへのhandleである。handleにはbuilder所有者の識別を持たせ、別GrammarBuilderのhandleを混ぜたら構築時に拒否する。

```scala
final class GrammarBuilder:
  def declare(name: String, arity: Int): RuleRef
  def define(rule: RuleRef)(body: Vector[Borrow] => P): Unit
  def build(start: RuleRef): Either[Vector[ValidationError], ValidatedGrammar]

  def eps: P
  def reject: P
  def empty: P
  def anyL: P
  def anyR: P
  def litL(text: String): P             // UTF-8 literal
  def litR(text: String): P
  def bytesL(bytes: Vector[Byte]): P
  def bytesR(bytes: Vector[Byte]): P
  def classL(bytes: Vector[Byte]): P
  def classR(bytes: Vector[Byte]): P
  def call(rule: RuleRef, args: Vector[Borrow]): P
  def bindL(capture: P)(body: Borrow => P): P
  def exactL(ref: Borrow): P
  def exactR(ref: Borrow): P
  def within(length: Int)(body: P): P
  def withinDec(length: Borrow)(body: P): P

extension (p: P)
  def ~(q: P): P
  def orElse(q: P): P
  def many: P
  def optional: P
  def plus: P
  def not: P
  def and: P
```

`~`と`orElse`の優先順位に依存する曖昧な例を避け、例題では括弧を明示する。`map`、`flatMap`、任意の値生成actionはv0では提供しない。

builder内部のID採番とarena組立てに限り局所的mutable collectionを許す。`build`後はimmutableにfreezeし、Evaluator・依存解析・Leanへ移す核には可変状態を持ち込まない。

### 7.2 再帰とhygiene

自己再帰をScalaの`lazy val`の無限展開で表さず、`declare`と`call`で表す。`define`や`bindL`のラムダは構築時に実行して終了し、最終Grammarには残さない。

捕捉したBorrowをScala変数へ退避し、scope外で使うことを型だけで完全禁止する必要はない。ただし`build`時のscope検査は必ず検出する。

## 8. 必須例題

以下の表面記法は説明用であり、v0でこのテキストを読む文法Parserを作る必要はない。実例は上記Combinatorで定義する。

### 8.1 PAL

```text
Pal = (L("a") R("a") Pal)
    / (L("b") R("b") Pal)
    / (optional(L([ab])) Empty)
```

全入力受理言語は`{ w ∈ {a,b}* | reverse(w) = w }`。

空列、1byte、偶数長、奇数長を扱う。左右照合の不一致後には両境界が元へ戻る。規則サイズはこの文法のnode数として報告し、plain PEGの規則数と同じ単位だと扱わない。

### 8.2 区切り付きCOPY

```text
Copy = bindL([ab]*) as x in (L("#") ExactL(x) Empty)
```

全入力受理言語は`{ w # w | w ∈ {a,b}* }`。`#`を含まない`{ww}`とは明確に区別する。

```text
#       accepted
a#a     accepted
ab#ab   accepted
ab#ba   rejected
ab#abx  rejected
```

### 8.3 簡易タグ

```text
Element = L("<") bindL(Name) as name in (
            L(">") (Element / Text)*
            L("</") ExactL(name) L(">")
          )
Name = [A-Za-z]+
Text = (!L("<") AnyL)+
```

`Element`は引数なしの規則とする。子Elementは親のtag名に依存しないことを依存解析で確認する。Tag本体をパラメータ化した補助規則を別に作り、必要な引数を渡すテストも用意する。

```text
<a><b>hello</b></a>   accepted
<a><b>hello</a></b>   rejected
<a></aa>              rejected
<a></a>x              parseAllではrejected
```

これはXML準拠パーサではない。属性、entity、コメント、namespace、空要素記法は対象外。

### 8.4 長さ付きフレーム

```text
Frame = bindL(Digit+) as n in (
          L(":") WithinDec(n, AnyL*) L(",") Empty
        )
```

payloadは任意のbyte。カンマを含んでもよい。

```text
5:hello,   accepted
4:hello,   rejected
0:,        accepted
2:a,,      accepted     # payloadは "a,"
2:é,       accepted     # UTF-8
1:é,       rejected
```

BigIntや直接的なbyte slicingを使った独立oracleをテスト側に置いてよい。Evaluator本体へoracleを組み込まない。

## 9. 静的解析

### 9.1 scopeと整形式性

Validatorは最低限、ID範囲、構文DAG、規則定義、引数数、SlotId宣言の一意性、scope、start arity=0、非負のWithin長を確認する。

rule bodyの初期scopeはそのruleのparamsだけ。BindLのcaptureは外側scope、bodyは外側scope+xで検査する。Callの実引数は呼出し地点でscope内でなければならない。

共有nodeを異なるscopeで検査するとき、単にExprIdだけをvisitedにしてscope検査を省略しない。検査結果をcacheするならscopeを含めるか、自由変数集合との包含検査に還元する。

整形式性は一般停止性を意味しない。v0では、全入力に対する停止を検証していない文法もfuel付きEvaluatorで扱える。

### 9.2 外側右境界を動かす可能性

`mayConsumeRight : ExprId -> Boolean`とrule要約を求める。

- 非空LitR / ClassR / AnyR / ExactRはtrue。
- 左primitive、Eps、Reject、Emptyはfalse。
- Seq / Choiceは子のOR、Manyは子の値。
- **Notはfalse**。内部の読取方向ではなく、成功時の外側境界への効果だからである。
- BindLはcaptureとbodyのOR。ただしcaptureがtrueならValidatorは拒否する。
- Callはcalleeの要約。
- **Within / WithinDecはfalse**。内部の両端消費を含めても外側では左から領域を消費する。

rule要約はfalseから単調反復し、固定点を求める。有限なrule数に基づく反復上限を設け、未収束をfalse扱いしない。

証明目標は「falseと判定された式がSuccessしたら、元のhiが保存される」。一般的な消費方向の完全判定は要求しない。

### 9.3 借用依存集合

式eの評価に必要な、現在環境のSlotId集合を`Deps(e)`とする。入力、左右境界、fuel、Grammarは別の固定引数である。

```text
Deps(primitive)          = ∅             # Exact以外
Deps(ExactL(x))          = {x}
Deps(ExactR(x))          = {x}
Deps(Seq(p,q))           = Deps(p) ∪ Deps(q)
Deps(Choice(p,q))        = Deps(p) ∪ Deps(q)
Deps(Not(p))            = Deps(p)
Deps(Many(p))           = Deps(p)
Deps(BindL(x,p,q))       = Deps(p) ∪ (Deps(q) \ {x})
Deps(Within(n,p))        = Deps(p)
Deps(WithinDec(x,p))     = {x} ∪ Deps(p)
```

Callはcalleeの **必要仮引数位置** から実引数へ写像する。calleeが第二引数を使わないなら、それに対応する実引数のSpan値をキーに含める必要はない。

ruleの必要仮引数集合を空から単調反復する。総仮引数数をPとすると、真に増える更新は高々P回なので、P+1回の全体反復で固定点を確認できる。最終結果が固定点条件を満たすことも機械的に検査する。

保存する式依存集合は固定点到達後に再計算し、SlotId昇順に正規化する。先頭候補の失敗が後続を選ばせるので、Choiceの第二候補だけでなく第一候補の依存も落としてはならない。

### 9.4 依存定理の前提

目標は、整形式のGrammar・有効cursor・scopeで要求される参照が存在しすべて有効な二つの環境について、Deps上の値が一致すれば、同じfuelでEvalResultが一致することである。

必要参照の欠落を許した不正環境まで、同じ定理で無条件に同一視しない。特にCallは未使用の実引数も解決するため、未使用参照の欠落と、存在するが値が違う場合は別である。

## 10. メモ化

### 10.1 実装順

1. `ReferenceEvaluator`: メモ化なし。
2. `MemoEvaluator`のFullEnv mode: 全環境をキーに含める。
3. 同じ`MemoEvaluator`のProjectedEnv mode: Deps上の環境だけをキーに含める。

参照Evaluatorとメモ化版を別のファイルに置き、メモ化版が参照版の完成結果を呼ぶだけの実装にしない。入力検査やbyte比較などの小さなpure helperの共有は許す。

### 10.2 v0のキー

```text
FullEnv:
  (ExprId, lo, hi, fuel, sorted full Env)

ProjectedEnv:
  (ExprId, lo, hi, fuel, [(slot, span) for slot in sorted Deps(expr)])
```

tableは **一つのGrammar・一つの入力・一回の公開run** に閉じる。公開runごとに必ず新しいtableを作る。低水準の複数呼出し試験では同じsessionであることを明示する。

**fuelを省いてはならない。** 小さいfuelでのOutOfFuelと、大きいfuelでのSuccessは同じ結果ではない。v0ではfuelをキーに含めることで、参照版との厳密一致を優先する。

保存するのはSuccessとFailureだけ。OutOfFuel、Fault、計算中の印は保存しない。再入の検出を通常のFailureとして処理しない。

### 10.3 tableと診断

最初はimmutableなMapを明示的に受け渡す。scopeから戻ってもtable自体は再利用できるが、環境の値は各キーに正しく反映されること。

```scala
enum MemoMode:
  case FullEnv, ProjectedEnv

final case class Stats(
  nodeVisits: Long,
  byteComparisons: Long,
  memoHits: Long,
  memoMisses: Long,
  memoEntries: Long,
  maxDependencyWidth: Int
)

final case class RunReport(result: EvalResult, stats: Stats)
```

statsは意味上の結果に含めない。FullEnvとProjectedEnvのstatsは異なってよい。比較すべきはEvalResultと残余区間である。参照版にも同じ定義の計測入口を用意し、計測の有無でEvalResultが変わらないことを回帰テストで確認する。測定のためのcounterを隠れたglobal stateにしない。

### 10.4 計算量について書ける範囲

最大k個の借用Span、入力長n、固定Grammarという前提なら、燃料を除く候補状態を`O(|nodes| n^(2k+2))`と数える見通しはある。ただしこれは停止性や実装時間の証明ではない。

v0のメモ化キーはfuelを含むので、fuel上限Fについて候補キー数の見通しには **F+1の因子** が加わる。さらに、ExactとWithinDecの入力走査、Map操作、環境構築の費用を別に数える。メモ化なしの参照版にこの多項式上界を付けない。

一般の線形時間は主張しない。fuelなしキーと必要導出深さ証明書による再利用は後続課題に置く。

## 11. テスト方針

### 11.1 必須の意味論回帰テスト

| 項目 | 期待 |
|---|---|
| EpsとEmptyの違い | 非空区間でEpsはSuccess、EmptyはFailure |
| fuel=0 | Epsを含めOutOfFuel |
| 正のfuelのprimitive | 条件どおりSuccessまたはFailure |
| LitR("ab") / LitR("a")~LitR("b") | 右向き照合の順序を区別 |
| 両端消費後に第一候補が失敗 | 第二候補は両境界が復元された状態で動く |
| Choiceの局所commit | `("a"/"ab")~Empty`は`ab`を拒否 |
| Notの内部消費 | Success時に左右境界を保存 |
| Many(Eps) | 十分なfuelでFault(NonProgress) |
| Many(Reject) | 十分なfuelで元区間のSuccess |
| A=A/Eps | OutOfFuel。Epsへfallbackしない |
| Not(A), optional(A) | OutOfFuelを成功へ変えない |
| captureに右消費 | Validatorが拒否、raw評価でもNonLeftCapture |
| Not内の右消費をcapture | 無消費captureとして許可 |
| BindLのscope外参照 | Validatorが拒否 |
| 必要なSpanが異なる同位置呼出し | ProjectedEnvが混同しない |
| 不要なSpanだけ異なる呼出し | 結果一致、ProjectedEnvの再利用を確認 |
| 右境界だけ異なる呼出し | cache keyを共有しない |
| 異なる入力の公開run | tableを共有しない |
| Withinの中央での完全消費 | 外側では長さnを正しく消費 |
| UTF-8 payload | byte長で判定 |
| 不正cursor/Span | out-of-boundsアクセスではなくエラー |

両境界rollbackの具体例は次とする。

```text
((L("a") R("b") L("z")) / (L("a") R("b") Empty))
input = "ab"
expected = Success(empty interval)
```

### 11.2 独立oracleと全列挙

PALはbyte列のreverseとの等価性、COPYは区切りで分割した二つのbyte列の等価性をoracleとする。タグは別の素朴なstack/再帰処理、Frameは直接的な長さ検査をoracleとする。oracleの実装でRBG Evaluatorを呼ばない。

- 通常テスト: PALの`{a,b}`上の全列挙を長さ8まで。
- 拡張検証: PALを長さ12まで。空列を含む8,191入力を比較する。
- COPY: 長さ0〜6の全wについて`w#w`を確認し、片側変更・余分な区切り・末尾付加を拒否する。
- Tag: 深さ0〜4の生成例と終了タグ改変例を比較する。
- Frame: 長さ0〜64の任意byte payload、長さ±1、UTF-8、非ASCII byte、長い数値fieldを含める。

### 11.3 性質ベースのテスト

追加のproperty-test依存は必須にしない。MUnit内でseedを固定した生成器を作ってよい。

デフォルトはseed `20261005L`、1,000組の `(Grammar, input, cursor, env, fuel)`。文法は小さいscope-correctなもの、入力長0〜12、fuel0〜32とする。任意の巨大な再帰木を生成してテスト時間を暴走させない。初期のランダム文法はacyclic call graphとし、再帰は既知のguarded例・発散例で別に試す。

比較対象は以下。

- Reference = FullEnv memo = ProjectedEnv memo。
- Successなら境界包含。
- OutOfFuel以外なら、fuelを増やした結果と一致。
- Deps上の値を保ち、不要な参照だけ変えたときの結果一致。
- Combinatorから作ったGrammarと手作りGrammarの認識結果一致。

Evaluator間の厳密比較は、必ず同一の正規化済みAST・同一fuelで行う。手書きASTとCombinator出力の構文形が異なる場合、同じ有限fuelで結果が異なること自体は反例ではない。AST一致を確認するか、両方が確定する十分なfuelで認識結果を比較する。

失敗時はseed、case index、Grammar、入力hex、cursor、env、fuel、三実装の結果を保存する。未知結果を比較対象から黙って落とさない。

---

# Part II — 実装計画

## 12. ディレクトリ構成

```text
rbg/
  build.sbt
  project/build.properties
  README.md
  docs/
    RBG_SCALA_THEN_LEAN4_IMPLEMENTATION.md
    SEMANTICS.md
    VALIDATION.md
    RELATED_WORK.md
    THEOREMS.md
    EXPERIMENTS.md
  src/main/scala/com/github/kmizu/rbg/
    Model.scala
    Node.scala
    Grammar.scala
    ByteOps.scala
    ReferenceEvaluator.scala
    GrammarBuilder.scala
    Combinators.scala
    Validator.scala
    DirectionAnalysis.scala
    DependencyAnalysis.scala
    MemoEvaluator.scala
    examples/PalGrammar.scala
    examples/CopyGrammar.scala
    examples/TagGrammar.scala
    examples/FrameGrammar.scala
    cli/Main.scala
  src/test/scala/com/github/kmizu/rbg/
    ModelSuite.scala
    EvaluatorSuite.scala
    BorrowSuite.scala
    CombinatorSuite.scala
    ExampleSuite.scala
    RegionSuite.scala
    AnalysisSuite.scala
    MemoSuite.scala
    PropertySuite.scala
    Oracles.scala
    tools/ExportLeanFixtures.scala
    tools/ValidationMain.scala
    tools/MeasureMain.scala
  scripts/
    verify-scala.sh
    verify-all.sh
    audit-axioms.sh
  proof/
    lean-toolchain
    lakefile.toml
    Rbg.lean
    Rbg/
      Model.lean
      Syntax.lean
      WellFormed.lean
      ByteOps.lean
      Eval.lean
      Semantics.lean
      Fuel.lean
      Bounds.lean
      Direction.lean
      Dependency.lean
      Memo.lean
      Region.lean
      Examples/Pal.lean
      Examples/Copy.lean
      Fixtures/Generated.lean
      FixtureCheck.lean
      Audit.lean
  artifacts/
    fixtures/manifest.txt
    reports/.gitkeep
```

この構成は段階的に作る。Lean関連ファイルをTask 1で空のまま大量に生成しない。各ファイルは責務が必要になったタスクで作る。

## 13. 段階ゲート

| ゲート | 条件 | 次へ進めること |
|---|---|---|
| A | Scala Coreの意味論回帰テストが通る | Combinatorと例題を積む |
| B | 四つの例題・長さ拡張・独立oracle比較が通る | 依存解析とメモ化を評価する |
| C | 同じfuelで三実装が一致、仕様とfixture生成が固定 | Leanプロジェクトの実装開始 |
| D | Lean EvalとScalaのfixture比較が通る | 基本定理と依存定理を証明 |
| E | メモ化一致・PAL/COPY・長さ拡張の必須定理と公理監査が通る | v0を完成として報告 |

Leanのインストール確認は先に行ってもよいが、C以前に意味論や証明を別設計で実装しない。途中で意味論を変更した場合は、Scalaの失敗テスト→修正→fixture更新→Lean更新の順にする。

## Task 1: データモデルと最小の実行可能プロジェクト

**Files:** `build.sbt`、`project/build.properties`、`Model.scala`、`Node.scala`、`Grammar.scala`、`ByteOps.scala`、`ModelSuite.scala`。

**Consumes:** Part Iの型契約。

**Produces:** Span/ID/Grammar/Result型、byte入力変換、範囲内比較helper、`sbt test`で動くMUnit環境。

- [ ] JDK/Scala/sbtの固定値を設定し、`show scalaVersion`と依存解決が成功することを記録する。
- [ ] 空区間・逆転区間・範囲外区間、非ASCII byte、UTF-8長について失敗テストを書く。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.ModelSuite'`を実行し、未実装の理由で失敗することを確認する。
- [ ] 型とpureな入力・byte操作を実装する。index加算前の境界検査を徹底する。
- [ ] 同じコマンドを通し、byte座標の仕様を`docs/SEMANTICS.md`へ記録する。
- [ ] 差分をレビューし、このタスクだけのcommitを作る。既存の未コミット作業を巻き込まない。

## Task 2: メモ化なしCore Evaluator

**Files:** `ReferenceEvaluator.scala`、`EvaluatorSuite.scala`、`docs/SEMANTICS.md`。

**Consumes:** Task 1のGrammar、Span、Env、EvalResult。

**Produces:** `evalFuel`、公開`parseAll`に必要な結果変換。Bind/Call/Withinはそれぞれ後続Taskで追加する。

- [ ] Eps/Empty、左右primitive、Seq、Choice、Not、Manyの失敗テストを先に書く。
- [ ] Review Focus 1と3の具体例、右literalの順序、Many(Eps)のNonProgressを固定する。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.EvaluatorSuite'`でredを確認する。
- [ ] Part Iどおりの深さfuelとimmutable state threadingで実装する。
- [ ] 同じsuiteをgreenにし、故意にrollbackを壊すと該当テストが落ちることを一度確認して変更を戻す。
- [ ] finite fuelでも無制限のJVM stackを保証しているわけではないことを記録する。参照版を高速VMへ置き換えない。
- [ ] commitし、ゲートAのCore部分を記録する。

## Task 3: 借用、明示的Call、整形式性

**Files:** `ReferenceEvaluator.scala`、`Validator.scala`、`DirectionAnalysis.scala`、`BorrowSuite.scala`、`AnalysisSuite.scala`。

**Consumes:** Task 2のEvaluator。Task 1の有限Grammar。

**Produces:** BindL/ExactL/ExactR/Call、`ValidatedGrammar`、`Validator.validate`、`mayConsumeRight`。

- [ ] 連続する左capture、空capture、ExactR、ネスト、scope外参照、arity不一致のテストを書く。
- [ ] 右消費captureを拒否し、Not内だけの右消費は許すテストを書く。
- [ ] A=A/EpsのOutOfFuelテストを追加する。一般再帰を無限ループさせない。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.BorrowSuite com.github.kmizu.rbg.AnalysisSuite'`でredを確認する。
- [ ] Callの環境構築を仮引数だけに限定し、direction summaryを単調固定点で実装する。
- [ ] captureのstatic検査に加え、raw EvaluatorにもNonLeftCaptureのguardを残す。
- [ ] suiteを通し、ゲートAを完了する。ここまでの意味論を文書と一致させてcommitする。

## Task 4: Parser CombinatorとPAL/COPY/簡易タグ

**Files:** `GrammarBuilder.scala`、`Combinators.scala`、`examples/PalGrammar.scala`、`examples/CopyGrammar.scala`、`examples/TagGrammar.scala`、`CombinatorSuite.scala`、`ExampleSuite.scala`、`Oracles.scala`。

**Consumes:** ValidatedGrammarと参照Evaluator。

**Produces:** Part IのCombinator API、三つの名前付きGrammar、独立oracle。

- [ ] 手書きASTとCombinatorの等価例、borrow hygiene、異なるbuilderのhandle混在拒否をテストする。
- [ ] 再帰定義の構築が有限であることをテストする。ASTにclosureを保持しないことを型構成で確認する。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.CombinatorSuite com.github.kmizu.rbg.ExampleSuite'`でredを確認する。
- [ ] Combinatorを実装し、PAL、区切り付きCOPY、簡易タグをこのAPIだけで組み立てる。
- [ ] 三例題を独立oracleと比較する。認識器内に例題専用の分岐を作らない。
- [ ] PALは`{a,b}`外のbyteを拒否するテストも含める。COPYを区切りなし言語と表記しない。
- [ ] suiteと全体テストを通し、例題の使い方をREADMEへ追加してcommitする。

## Task 5: Withinと十進長さ拡張

**Files:** `Node.scala`、`ReferenceEvaluator.scala`、`ByteOps.scala`、`Validator.scala`、`DirectionAnalysis.scala`、`Combinators.scala`、`examples/FrameGrammar.scala`、`RegionSuite.scala`、`Oracles.scala`。

**Consumes:** CoreとCombinator。

**Produces:** Within/WithinDec、bounded decimal decoder、FrameGrammar。

- [ ] 0長、内部未消費、中央での消費完了、外側境界復元、借用アクセスのテストを先に書く。
- [ ] UTF-8の`2:é,`と`1:é,`、payload内のカンマ、数百桁長さ、符号・空長さ・非数字を固定する。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.RegionSuite'`でredを確認する。
- [ ] `decodeBoundedDecimal(input, span, cap)`をpure helperとして実装し、Int overflowなしで境界を処理する。
- [ ] 内部Successの一致位置に依存せず、外側を`[oldLo+n, oldHi)`へ更新する。
- [ ] Frameの直接oracleとの比較を通し、ゲートBを完了する。仕様更新とともにcommitする。

## Task 6: 借用依存解析

**Files:** `DependencyAnalysis.scala`、`AnalysisSuite.scala`、`PropertySuite.scala`。

**Consumes:** 整形式Grammar、明示的params/SlotId。

**Produces:** 各ruleの必要仮引数位置、各nodeのDeps、固定点条件の検査。

- [ ] Exactの依存、BindLでの束縛除去、Choice両枝、Not内依存、Callの未使用引数をテストする。
- [ ] 相互再帰で依存が数段先から伝播する例と、無関係な引数が最後まで不要な例を書く。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.AnalysisSuite'`でredを確認する。
- [ ] 必要仮引数集合の単調反復と最終固定点検査を実装する。
- [ ] well-scopedで同じDeps値を持つ環境を生成し、同じfuelで結果が一致するproperty testを追加する。
- [ ] Child Elementが親のtag名に依存しないことを実データで確認する。
- [ ] 「依存キーの縮小」と「実行環境の要素削除」は別であることを文書化してcommitする。

## Task 7: FullEnv / ProjectedEnvメモ化

**Files:** `MemoEvaluator.scala`、`MemoSuite.scala`、`PropertySuite.scala`。

**Consumes:** 参照Evaluator、固定済みDeps、Statsの契約。

**Produces:** 二つのmodeを持つメモ化Evaluator、RunReport、参照版との比較。

- [ ] 同じExprId・cursor・fuelで、必要Spanだけを変えた衝突テストを書く。
- [ ] 不要Spanだけを変える呼出し、hiだけが変わる呼出し、異なる入力の別run、異なるfuelをテストする。
- [ ] `sbt 'testOnly com.github.kmizu.rbg.MemoSuite'`でredを確認する。
- [ ] まずFullEnvを実装し、同じfuelで参照版と全結果が一致することを確認する。
- [ ] 次にProjectedEnvを実装する。二つのmodeで同じcache engineを用い、キー生成だけを変える。
- [ ] 成功/通常失敗だけをcacheし、OutOfFuel/Faultはcacheしない。計算中entryをFailureとして扱わない。
- [ ] 1,000件のproperty比較を通し、キー射影で実際にhitが増える少なくとも一つの例を保存する。
- [ ] byte比較回数とkey数を計測できるようにする。参照版の計測入口も用意し、計測on/offの結果一致を確認する。結果とstatsを区別してcommitする。

## Task 8: CLI、拡張検証、仕様の固定

**Files:** `cli/Main.scala`、`tools/ValidationMain.scala`、`tools/MeasureMain.scala`、`scripts/verify-scala.sh`、`docs/VALIDATION.md`、`docs/EXPERIMENTS.md`、`README.md`。

**Consumes:** 四つのGrammarと三評価mode。

**Produces:** 再現用CLI、全列挙runner、測定結果、ゲートCの記録。

- [ ] CLIは`<pal|copy|tags|frame> --engine <reference|full|projected> --fuel N --text TEXT`を受け付ける。
- [ ] binary用に`--hex HEX`も設け、`--text`との同時指定を拒否する。引数エラー時に利用法を表示する。
- [ ] exit codeはAccepted=0、Rejected=1、入力/引数エラー=2、OutOfFuel=3、Fault=4に固定し、testする。
- [ ] 拡張検証runnerでPAL 8,191入力、COPY、タグ、Frameを独立oracleと比較する。
- [ ] 深さや長さが大きすぎて参照版が実行できない場合は、拒否とは扱わず制約と未実行を報告する。
- [ ] 測定は実際に成功した入力サイズだけ記録する。JVM warm-up、環境、fuel、node数、比較数、cache数を併記し、最速値だけで結論を出さない。
- [ ] Reference / FullEnv / ProjectedEnvが一致し、SEMANTICSと回帰テストに矛盾がないことを確認してゲートCを記録する。
- [ ] commitする。この時点までLeanの別設計実装を先行させない。

## Task 9: ScalaからLean用fixtureを出力する

**Files:** `tools/ExportLeanFixtures.scala`、`artifacts/fixtures/manifest.txt`、`proof/Rbg/Fixtures/Generated.lean`の生成仕様、`docs/VALIDATION.md`。

**Consumes:** 同じ有限AST、Scala参照Evaluator、回帰例とseed付き生成例。

**Produces:** Scalaが出力するLeanデータファイルとmanifest。LeanのEvaluator実装自体はTask 10で行う。

- [ ] 出力を先に仕様化する。Grammar、node、byte、Span、Env、fuel、期待EvalResultをすべて含める。
- [ ] bridgeの表現可能範囲を固定する。Scalaの負のoffset・ID・fuel・Within長は入口/ValidatorのScala側テストに残し、Natを使うLeanのfixtureへ無理に写さない。非負だが範囲外のID/Span、欠落参照、NonProgressなど表現できる異常例は両側で比較する。
- [ ] 固定回帰例に加え、seed固定の小さなscope-correct Grammarのfixtureも含める。単に例題名をLean側へ渡して作り直すだけにしない。
- [ ] `Generated.lean`にはデータ定義だけを出し、証明、axiom、Evaluator、期待結果を返す関数を生成しない。
- [ ] 同じ入力からbyte-for-byte同じ出力になることをテストする。mapと集合は正規順に並べる。
- [ ] manifestに仕様version、seed、case数、Scala/toolchain情報、生成ファイルのSHA-256、生成元commitを記録する。
- [ ] Scala参照版とメモ化版の双方で期待結果を照合する。
- [ ] `--check`を実装し、一時生成との差異があれば非zero終了させる。検証コマンドが既存fixtureを黙って書き換えて成功しないようにする。
- [ ] commitする。bridgeは差分試験であり、Scala→Leanコンパイラの形式的正当性証明ではないと記録する。

## Task 10: Leanの型とfuel付きEvaluatorを対応移植する

**Files:** `proof/lean-toolchain`、`proof/lakefile.toml`、`Rbg.lean`、`Model.lean`、`Syntax.lean`、`WellFormed.lean`、`ByteOps.lean`、`Eval.lean`、`FixtureCheck.lean`。

**Consumes:** Scalaで固定したModel / Node / evalFuel / decoder。

**Produces:** `Rbg.evalFuel`と実行可能なfixture checker。

- [ ] toolchainを`leanprover/lean4:v4.31.0`に固定し、Lake projectを初めて作る。
- [ ] Scala型とLean型の対応表を文書化する。Int座標はNatに写し、不正負数の検査はScala入口境界の責務として別記する。
- [ ] EvalResultの四分類、node constructor、環境操作、参照照合を一対一で移す。
- [ ] 最初はfuelに対するstructural recursionだけで定義する。`partial`、`unsafe`、独自termination axiomを使わない。[R10]
- [ ] Seq/Choiceの兄弟へ同じ子fuelを渡し、Manyの継続でfuelを減らす。Scalaとの消費規則のズレを禁止する。
- [ ] Lakeに`fixtureCheck`実行targetを登録し、全fixtureを計算比較する。失敗時にはcase indexと期待/実結果を出して非zero終了する。
- [ ] `lake build`と`lake exe fixtureCheck`を通し、ゲートDを記録してcommitする。

## Task 11: 燃料に依存しない意味論と基本定理

**Files:** `Semantics.lean`、`Fuel.lean`、`Bounds.lean`、`docs/THEOREMS.md`。

**Consumes:** Lean evalFuelとWellFormed。

**Produces:** 完了した有限導出を表すEval relation、fuel対応、決定性、区間不変条件。

- [ ] OutOfFuelの導出規則を持たないinductiveな`Eval` relationを定義する。Success/Failure/Faultの有限導出を表す。
- [ ] `evalFuel_sound`: OutOfFuel以外の評価結果には対応するEval導出があることを証明する。
- [ ] `evalFuel_complete`: 有限Eval導出には十分なfuelが存在することを証明する。
- [ ] `fuel_stable`: 一度確定した結果は、より大きいfuelでも同じであることを証明する。
- [ ] `eval_deterministic`: 同じ状態に対する有限導出の結果が一意であることを証明する。
- [ ] `success_bounds`: 有効な初期cursorからのSuccessは、初期区間に包含される有効な残余区間を返すことを証明する。
- [ ] Notの境界保存、ChoiceのFailure後の元状態評価、BindLの外側環境不変を基本補題として整理する。
- [ ] 各定理の前提をTHEOREMSへ記し、fixture、`lake build`、公理出力を確認してcommitする。

## Task 12: 方向・依存解析の健全性

**Files:** `Direction.lean`、`Dependency.lean`、`WellFormed.lean`、`docs/THEOREMS.md`。

**Consumes:** 有限AST、Scalaと同じ固定点算法、基本定理。

**Produces:** 実行可能な解析関数、その出力の健全性、環境同値定理。

- [ ] Scalaのrule要約の固定点反復を移す。有限個のboolean / param位置が増えることによる停止理由を示す。
- [ ] 算出した要約が方程式を満たすことを判定するcheckerを実装し、まずchecker成功から健全性を証明する。
- [ ] 続いて実際のanalysis関数の出力がcheckerを通ることを証明する。証明済みなのがcheckerだけの段階はそう記録する。
- [ ] `right_stable`: mayConsumeRight=falseなら、Success時にhiが変わらないことを証明する。
- [ ] `deps_sound`: 同じDeps値を持つ二つの有効・scope充足環境で、同じfuelのEvalResultが一致することを証明する。
- [ ] Callの未使用実引数にも存在・有効性の前提があることを定理文から落とさない。
- [ ] 例題の解析結果をLeanとScalaで比較し、`lake build`とfixture checkerを通してcommitする。

## Task 13: メモ化版の正当性

**Files:** `Memo.lean`、`docs/THEOREMS.md`。

**Consumes:** deps_sound、同じfuelを含むMemoKey、参照evalFuel。

**Produces:** Leanのpersistent memo evaluator、table invariant、FullEnv/ProjectedEnv一致定理。

- [ ] Scalaと同じキーをLeanで定義する。初期の証明ではassociation listなど素朴な有限tableを使ってよい。
- [ ] `MemoTableValid`を定義する。各entryが、そのキーに対応する参照評価結果を表すことを条件にする。
- [ ] projected keyでは同じキーを持つ有効環境全体へdeps_soundで結果を移せることを示す。
- [ ] table-validityの保存と、hit/missそれぞれの結果一致をfuel帰納法で証明する。
- [ ] 空tableから開始したFullEnv/ProjectedEnvの両方について、同じfuelの参照版とEvalResultが一致する定理を出す。
- [ ] 計算中entry、OutOfFuel、Faultをtableに保存しないScala方針との一致を確認する。
- [ ] fixtureを三つのLean評価modeでも比較し、`lake build`と監査を通してcommitする。

## Task 14: 例題の正しさと長さ拡張の証明

**Files:** `Examples/Pal.lean`、`Examples/Copy.lean`、`Region.lean`、`docs/THEOREMS.md`。

**Consumes:** Core/長さ拡張の意味論と基本補題。

**Produces:** PALと区切り付きCOPYの言語等価・個別停止性、bounded decimal decoderとWithinの性質。

- [ ] `Recognizes(G,w)`を「あるfuelでentryが空残余に成功する」と定義する。
- [ ] PALについて、認識と`w`の全byteがa/bかつ`reverse(w)=w`が同値であることを証明する。
- [ ] PALについて、すべての有限byte入力で十分なfuelが存在し、OutOfFuelでもFaultでもない結果になることを示す。存在fuelを根拠なく固定数に置き換えない。
- [ ] COPYについて、認識と`∃v ∈ {a,b}*, w = v ++ [#] ++ v`が同値であることを証明する。個別停止性も示す。
- [ ] decimal decoderの成功と「非空の十進数字列の値nがcap以下」の対応を証明する。
- [ ] Within/WithinDecの内部完全消費、外側のn byte消費、内部終端、非overflowに対応する算術性質を示す。
- [ ] タグ言語全体の形式的対応はv0では追加目標とする。Scalaのタグoracle検証を、その形式証明が終わったことにはしない。
- [ ] 全fixtureと公理監査を通してcommitする。

## Task 15: 公理監査、再現性、最終文書

**Files:** `Audit.lean`、`scripts/audit-axioms.sh`、`scripts/verify-all.sh`、`docs/RELATED_WORK.md`、`docs/VALIDATION.md`、`docs/THEOREMS.md`、`README.md`。

**Consumes:** 必須Scala/Lean成果物。

**Produces:** clean checkoutでの検証手順、監査結果、正確な主張一覧、ゲートE。

- [ ] 必須定理すべてに`#print axioms`を用意する。
- [ ] `sorryAx`、独自axiom、`Lean.ofReduceBool`などの新たな信頼前提を必須定理で許さない。許容される標準公理は`propext`、`Classical.choice`、`Quot.sound`のみで、不要なら依存させない。
- [ ] 中核証明を`native_decide`で済ませない。小さい有限の整形式検査にkernelで確認される`decide`を使うことは可。大量fixtureの計算比較は証明とは別にする。
- [ ] ソース検索だけでなく実際の定理の公理依存を確認し、禁止項目を検出したらscriptが失敗するようにする。
- [ ] `verify-all.sh`にScala全テスト、fixture再生成check、Lean build、fixture実行、公理監査を組み込み、いずれかの失敗を必ず終了コードに反映する。
- [ ] 関連研究との差分をR1〜R4の実際の仕様と照合する。確認できなかった新規性は未確定と書く。
- [ ] 「Scalaでテスト済み」「Leanモデルで証明済み」「未実装/未証明」を一覧にしてREADMEとTHEOREMSを一致させる。
- [ ] ゲートEを確認してcommitする。承認されていないremote push、release作成、package公開は行わない。

---

# Part III — 検証、証明の範囲、引き継ぎ

## 14. 検証コマンドの契約

以下は実装完了後に提供するコマンドであり、現時点で実行済みという意味ではない。CLIやrunnerの名前を変更する場合は、この節とREADMEを同時に更新する。

```bash
# Scala
sbt clean test
sbt 'Test / runMain com.github.kmizu.rbg.tools.ValidationMain --extended'
sbt 'runMain com.github.kmizu.rbg.cli.Main pal --engine reference --fuel 512 --text abba'
sbt 'runMain com.github.kmizu.rbg.cli.Main copy --engine projected --fuel 512 --text ab#ab'
sbt 'runMain com.github.kmizu.rbg.cli.Main frame --engine full --fuel 512 --text 5:hello,'

# cross-language fixtures: 最初の生成 / 以後の差異確認
sbt 'Test / runMain com.github.kmizu.rbg.tools.ExportLeanFixtures --write'
sbt 'Test / runMain com.github.kmizu.rbg.tools.ExportLeanFixtures --check'

# Lean
(cd proof && lake build)
(cd proof && lake exe fixtureCheck)
./scripts/audit-axioms.sh

# 最終検証
./scripts/verify-scala.sh
./scripts/verify-all.sh
```

`--write`は明示的な更新専用、通常のCIは`--check`を使う。生成元commit情報は、単にHEADが進んだだけで毎回check不一致にしない。生成データに影響するsource tree hashも記録し、fixture内容の一致確認と由来情報の更新を分ける。

## 15. Scala → Leanの対応表

| Scala | Lean | 留意点 |
|---|---|---|
| Vector[Byte] | List UInt8 | byte値とindexの対応。計算量は同じとは仮定しない |
| Span(Int,Int) | Span(Nat,Nat) | Scalaの負数拒否は入口の検証責務 |
| ExprId/RuleId/SlotId | それぞれ別のstructure | すべてを無区別なNat aliasにしない |
| Vector[Node] | List Node | ID lookup失敗の結果を揃える |
| Map[SlotId,Span] | 有限のassociation list等 | lookup/更新/影響しないkeyを最初に補題化 |
| EvalResult | 同じ四分類 | OutOfFuelをFailureへ写さない |
| evalFuel | fuelのstructural recursion | 兄弟へ渡すfuelも一致させる |
| Deps固定点 | 同じ有限単調反復 | 証明の都合で別の解析に置換しない |
| MemoEvaluator | persistentなmemo evaluator | table実装の効率差と意味論同一性を分ける |

Leanに移す際に、Scalaで検証していない便利な一般化を追加しない。小さな補題のためにデータ表現を大きく変えたくなったら、先に対応表と必要性を文書化する。

## 16. 必須定理と正確な達成表示

| 定理/検証 | v0必須 | 主張できること |
|---|---|---|
| Scala三評価modeの差分テスト | Yes | 実行した有限ケースでの一致 |
| Scala→Lean fixture比較 | Yes | 出力した有限データ上での一致 |
| evalFuel sound / complete | Yes | Leanのfuel評価と有限導出の対応 |
| fuel stable / deterministic | Yes | 確定結果の一意性とfuel安定性 |
| success bounds | Yes | 成功時の区間包含 |
| direction sound | Yes | 右境界を保存する解析結果の健全性 |
| dependency sound | Yes | 正しい前提の下での環境射影の健全性 |
| memo correctness | Yes | Leanのmemoモデルと参照モデルの一致 |
| PAL language equality / totality | Yes | 例題PAL文法の全有限入力での性質 |
| marked COPY equality / totality | Yes | 区切り付きCOPYの性質 |
| decoder / Within properties | Yes | 限定された長さ拡張の意味論的性質 |
| Tag全体の言語等価 | No | 終わっていなければScalaテストのみ |
| Scala/JVM実装の形式検証 | No | fixture一致だけでは主張不可 |
| 一般文法の停止性 | No | fuel付き実行可能性とは別 |
| 一般線形時間 / 物理的入力回収 | No | 別の解析・実装・証明が必要 |
| 新文法形式としての新規性 | No | 関連研究比較の結果で判断 |

## 17. 実装者がしてはいけない近道

- 未完了の評価を通常失敗にしてテストを通す。
- 任意の両端消費を一つのcaptureとして表現する。
- 右literalのbyte順を反転する。
- 入力の一部をStringへ変換して、その文字数をbyte長として使う。
- 任意の`flatMap`やmutableなユーザー状態で文脈依存構文を実装し、形式化対象から除外する。
- 「使わないはずの引数」を存在確認ごと削除して、Faultの意味を変える。
- fuelやhiをメモ化キーから落とし、ベンチマークが速いことを正当性の代用にする。
- ハッシュの一致だけでExactを成功にする。
- この言語はPALだから、Evaluator内で直接reverse比較する。
- ScalaとLeanの双方へ同じ期待結果を埋め込み、それを差分テストと呼ぶ。
- `sorry`を残したままbuild成功を証明完成と報告する。
- IPGや既存の状態付き解析との比較をせず、「入力区間が新しい」と宣伝する。
- 先に汎用VM、言語Parser、コード生成器、IDE対応を作り、意味論と検証を後回しにする。

## 18. 作業報告の形式

タスクごとに、変更ファイル、追加した回帰テスト、実行したコマンドとexit code、意味論変更の有無、残課題を短く記録する。

最終報告には以下を含める。

```text
到達ゲート:
固定toolchain:
Scalaのテスト数 / 拡張検証のケース数:
fixture件数とsource hash:
Leanで証明済みの必須定理:
各必須定理の公理依存:
未実装・未証明:
確認できた関連研究との差 / 未確定の差:
主要なベンチマークと計測条件:
再現コマンド:
```

途中で作業を区切る場合も、動くcommit・正確な到達ゲート・次に実施するタスクを残す。まだ到達していないゲートを完了扱いしない。

## 19. 参考資料と採用理由

以下の研究・公式資料は2026-10-05に確認した。URLは参照先を再取得できるように記載する。本文のRBG仕様は本書の設計決定であり、これらの資料がRBGの正しさや新規性を保証するわけではない。

**[R1] Jialun Zhang, Greg Morrisett, Gang Tan. _Interval Parsing Grammars for File Format Parsing_ (2023).** 入力区間と属性を結び付ける文法形式。RBGの最優先比較対象。区間化そのものを新規性としない根拠。

`https://arxiv.org/abs/2304.04859`

**[R2] Kimio Kuramitsu. _Nez: practical open grammar language_ (2015).** ホスト言語actionなしの文脈依存構文と状態管理を比較する。

`https://arxiv.org/abs/1511.08307`

**[R3] Nicolas Laurent, Kim Mens. _Taming Context-Sensitive Languages with Principled Stateful Parsing_ (2016).** 状態変更とbacktracking/memoizationを整合させる規律の比較対象。

`https://arxiv.org/abs/1609.05365`

**[R4] _Regular Expressions with Backreferences: Polynomial-Time Matching Techniques_ (2019).** 借用参照の数や使い方から計算量を考える際の比較対象。文法が異なるため結果をそのまま転用しない。

`https://arxiv.org/abs/1903.05896`

**[R5] Scala 3.3.8 LTS release.** 固定するScala版の公式確認。

`https://www.scala-lang.org/download/3.3.8.html`

**[R6] Scala JDK Compatibility.** JDK 21とScala 3.3系の対応確認。

`https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html`

**[R7] sbt v1.11.7 release.** 固定するbuild tool版の確認。

`https://github.com/sbt/sbt/releases/tag/v1.11.7`

**[R8] MUnit Getting Started / MUnit 1.2.1 artifact.** MUnitのsbt integrationと固定artifactの確認。

`https://scalameta.org/munit/docs/getting-started.html`

`https://index.scala-lang.org/scalameta/munit/artifacts/munit/1.2.1`

**[R9] Lean v4.31.0 release.** 固定するLean版の確認。

`https://github.com/leanprover/lean4/releases/tag/v4.31.0`

**[R10] Lean Reference: Recursive Definitions / Lake.** fuelによるstructural recursion、必要になった場合のwell-founded recursion、実行targetの構築に使う。latest文書と固定版で差異があれば固定版の挙動を優先する。

`https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/`

`https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/`

---

**最重要の実行原則:** Scalaで小さく動かす。別実装とoracleで壊す。意味論を固定する。その構造をLeanへ一つずつ移す。証明のために、動いて確かめた構成を見失わない。
