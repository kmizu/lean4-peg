# PAL Python → Scala 3 移植 実装計画

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `docs/palindromes-in-peg/**/*.py`（約 170 ファイル、18,000 行）を全て Scala 3 に移植し、
コウタが Scala だけで目視検証できるようにする。Python 版は当面残す（差分テストの基準）。

**Architecture:** 既存の `scala/` sbt ビルドに新サブプロジェクト `pal`（`scala/pal/`）を追加。
Python モジュール 1 つ = Scala ファイル 1 つ（`snake_case.py` → `SnakeCase.scala`、
パッケージ `pal`）。`unittest` は munit に 1:1 で移植。テキストを出力する生成器は
Python と **バイト一致** を差分テストで確認する。

**Tech Stack:** Scala 3.7.4（ブレース構文）、sbt 1.11、munit 1.1.1、Python 3.14（基準としてのみ）。

**Spec:** `docs/palindromes-in-peg/STATUS.md` §2（構成）と §5B（移植は SHA 再現の鎖を切りうる →
だからこそバイト一致の差分テストを必須にする）。

**Status note (2026-09-07):** This remains an implementation plan, not a
claim that the port is complete. The pending-at-snapshot inventory is recorded
in `/tmp/pal-port-inventory.md`; its eight entries are now integrated or
assigned, so a final coverage audit after parent integrations is still needed.
The active Scala sources expose `pal.GenerateWindowPal`,
`pal.CompactScaffoldPeg`, `pal.VerifyWindowPal`, `pal.GeneratePhaseExamples`,
and `pal.GenerateScaffoldExamples`. The default full-grammar SHA has not been
verified from Scala; only bounded/source-fixture byte-identity checks currently
count as evidence.

## Global Constraints（全タスク共通・必読）

1. **Scala 3 だがブレース構文を使う。** indentation syntax、`then`/`do` 省略記法、`end` マーカーは禁止。
   `if (c) { ... } else { ... }`、`for (x <- xs) { ... }`、`match { case ... }` の形で書く。
2. `scalacOptions` は既存の `strictOpts`（`-deprecation -feature -Wunused:all -Werror`）。警告ゼロ。
3. **ファイル対応 1:1**：`foo_bar.py` → `scala/pal/src/main/scala/pal/FooBar.scala`、
   `test_foo_bar.py` → `scala/pal/src/test/scala/pal/FooBarSuite.scala`。テストのヘルパーを
   import している test ファイル（例 `test_scaffold_circuit_program`）は `src/test` 側の
   `object` にする。
4. **忠実性優先、ただし Scala らしく。** アルゴリズムと出力（規則名・順序・整形）は Python と
   同一にする。データ表現は Python のタプル/dict をそのまま持ち込まず、sealed trait / case class /
   enum に置き換える。`Expr` は `symbolic_sca2peg.py` の 14 タグ（and, or, not, const, symbol,
   self, select, read, present, pointer, old, null, exists, edge）で閉じているので sealed ADT。
   hash-consing（`Expr._pool`）は `Expr.share { ... }` 的な明示スコープで再現する。
5. **順序に注意。** Python の `dict` の反復順は挿入順だが、`set` は挿入順ではない。Scala では
   `mutable.LinkedHashMap` / `LinkedHashSet` / `Vector` を使い、`Map`/`Set` の不定順を出力順に
   使わない。set 順が出力に影響する箇所は、`CPythonSetOrder` のように対象の CPython 順を明示的に
   再現する。
   `sorted()` の比較（タプル辞書式、文字列）は Scala の `Ordering` で同じ結果になるよう明示する。
6. **不変性の規約は緩める。** 生成器は数百万規則を扱う性能コードなので、局所的な
   `mutable.*` と `var` は可。ただし公開 API は不変値を返す。
7. **差分テスト**：出力を持つモジュールは `PyDiff.assertSameAsPython(...)` で Python の
   出力と比較する（Task 0 で定義）。`generated/*.peg` と `generated/*.json` は Python 版の
   ゴールデン。Scala 版は同じ内容を生成しなければならない。
8. **Python 側は変更しない。** 差分の基準を壊さない。
9. 各タスクの完了条件：`cd scala && sbt -batch "pal/testOnly pal.<Suite>*"` が通り、
   `sbt -batch pal/compile` が警告ゼロ、対応する Python テストと同数以上のテストがある。
10. **コミットはタスク単位**（`feat(pal): port <modules>`）。branch は現在の
    `feat/pal-plain-peg-artifact`。
11. 2 文字の Python コードは Codex 産で密度が高い。Scala では読み手（コウタ）のため
    メソッドを分割し、Python の docstring を Scaladoc として引き継ぐ。日本語コメント可。

## 依存層（leaf → root）。同じ層は並列可能

| 層 | モジュール |
|---|---|
| L0 core | symbolic_sca2peg, phase_peg, scaffold_circuit, scaffold_circuit_structs |
| L0 独立 | scavm, fpp_finite, gs_heads, gs_overlap, gs_local_clock, galil_contracts, fpp, fpp_tape, lps_halving, online_manacher, read_blocks, stage1_kmp_online, stage2_tm_galil, symbolic_tm2peg, tm2peg, twoway, verify_window_pal, compact_scaffold_peg, analysis/grammar_closure, analysis/grammar_scc |
| GS 群 | gs_flag_heads, gs_match_heads, gs_head_liveness, gs_events, gs_dual_flags, gs_batch_clock, delayed_pal, gs_flag_trace, gs_match_trace |
| FPP 群 | fpp_subroutine, fpp_reuse, fpp_cost, dp_finite, dp_search_finite, dp_search_reuse, chain_finite, move_center_finite, galil_clock |
| SCAVM 群 | scavm_structs, scavm_pal, scaffold_input, scaffold_places, scaffold_program, scaffold_search, scaffold_chain, scaffold_galil, galil_realtime, scaffold_pal, stage5_port_block1 |
| 独立小物 | peg_file, twoway_border, stage3_tm_galil_chain, stage3b_design_check, generate_phase_examples, generate_scaffold_examples |
| 回路群 | scaffold_optimize, scaffold_artifact, scaffold_round, scaffold_round_lazy, scaffold_round_tree, scaffold_rom, scaffold_event_buffer, scaffold_queue_registers, scaffold_head_distances, scaffold_live_distances, scaffold_stream_heads, scaffold_circuit_input, scaffold_circuit_program, scaffold_circuit_search, scaffold_circuit_chain, scaffold_circuit_galil, scaffold_match_input, scaffold_gs_heads, scaffold_gs_matcher, scaffold_gs_flags, scaffold_delayed_pal, midpoint_peg, generate_galil_peg, generate_online_peg |
| 窓群 | scaffold_window_counter, scaffold_window_positions, scaffold_window_registers, scaffold_window_live, scaffold_window_stream, scaffold_window_gs, scaffold_window_gs_live, scaffold_flag_packets, scaffold_window_workers, scaffold_window_pal, generate_window_pal |

---

### Task 0: sbt サブプロジェクト `pal` と Python 差分テスト基盤

**Files:**
- Modify: `scala/build.sbt`（`lazy val pal` を追加、`root.aggregate` に加える）
- Create: `scala/pal/src/test/scala/pal/PyDiff.scala`
- Create: `scala/pal/src/test/scala/pal/PyDiffSuite.scala`

**Produces:**
```scala
package pal
object PyDiff {
  /** docs/palindromes-in-peg を cwd にして python3 を実行し、stdout を返す。 */
  def python(args: String*): String
  /** Python スクリプトの stdout と Scala の文字列が完全一致することを検査する。 */
  def assertSameAsPython(actual: String, script: String, args: String*): Unit
  val pyDir: java.nio.file.Path   // docs/palindromes-in-peg の絶対パス
}
```
- [ ] build.sbt に追加（`Test / javaOptions` は `-Xss512m -Xmx8g`、`Test / fork := true`）
- [ ] `PyDiffSuite`：`python("-c", "print('x')")` が `"x\n"` を返す
- [ ] `sbt -batch pal/test` 緑、コミット `chore(pal): sbt subproject and Python diff harness`

### Task 1: L0 core（symbolic_sca2peg, phase_peg, scaffold_circuit, scaffold_circuit_structs）

- `Expr` を sealed ADT に。`Scaffold`, `Node`, `Grammar`, `CompactMemo`, `inverse_repeat`,
  `Value`, `Ref`, `Circuit`, `neg/conjunction/disjunction/choose/choose_pointer` を移植。
- `test_symbolic_sca2peg.py`, `test_phase_peg.py`, `test_scaffold_circuit.py`,
  `test_scaffold_circuit_queue.py` を munit に。
- 差分：`generate_scaffold_examples.py` が出す `generated/sparse_*.peg`, `scaffold_marked_palindrome.peg`
  と `generate_phase_examples.py` が出す `generated/phase_*.peg` をバイト一致で再生成できること。
  （generate_* 2 本はこのタスクに含める。）
- **Produces（後続タスクが依存する名前）**：パッケージ `pal`、`Expr`（+ `Expr.TRUE/FALSE/SELF/NULL`）、
  関数群は Python と同名 camelCase（`symbol, old, exists, negate, both, either, pointer, select,
  read, edge, present`、`neg, conjunction, disjunction, choose, choosePointer`）。
  `Scaffold`/`Circuit` のメソッドも Python 名を camelCase 化。実装後、この Produces 節に
  実際のシグネチャを追記すること。
- **実装済み API（2026-09-07、`scala/pal/src/main/scala/pal/`）**。すべて `package pal`。
  Python の 1 文字 str（入力記号）は `Char`、Python `None`（値域の要素）は Scala `None`、
  `ValueError` は `IllegalArgumentException`（メッセージは Python と同一）。
  ```scala
  // SymbolicSca2Peg.scala
  sealed abstract class Expr { def tag: String; def args: Vector[Any] }   // hashCode はキャッシュ、equals は同一性ショートカット付き
  object Expr {
    case class Const(value: Boolean); case class Symbol(char: Char); case object Self; case object Null
    case class Old(path: Vector[String], label: String); case class Exists(path: Vector[String])
    case class Not(value: Expr); case class And(values: Vector[Expr]); case class Or(values: Vector[Expr])
    case class Pointer(path: Vector[String]); case class Select(condition: Expr, yes: Expr, no: Expr)
    case class Read(target: Expr, label: String); case class Edge(target: Expr, field: String); case class Present(target: Expr)
    val TRUE, FALSE, SELF, NULL: Expr
    def symbol(char: Char): Expr; def old(path: Seq[String], label: String): Expr; def exists(path: Seq[String]): Expr
    def negate(value: Expr): Expr; def both(values: Expr*): Expr; def either(values: Expr*): Expr
    def pointer(path: Seq[String]): Expr; def select(condition: Expr, yes: Expr, no: Expr): Expr
    def read(target: Expr, label: String): Expr; def edge(target: Expr, field: String): Expr; def present(target: Expr): Expr
    def make(tag: String, args: Seq[Any]): Expr            // scaffold_artifact 用の (tag, *args) からの再構成
    def share[A](body: => A): A                            // share_expressions()（ネスト可）
    def clearExpressionCache(): Unit; def sharing: Boolean; def intern[E <: Expr](expr: E): E
  }
  final class Node(var labels: VectorMap[String, Boolean], var pointers: VectorMap[String, Option[Node]])
  final class Scaffold(initial: Iterable[(String, Boolean)], labels: Iterable[(String, Expr)],
                       pointers: Iterable[(String, Expr)], val accepting: String, val alphabet: String = "ab") {
    val initial: VectorMap[String, Boolean]; val labels, pointers: VectorMap[String, Expr]
    def run(word: String): Boolean; def initialNode(): Node; def evaluate(word: String): Option[Node]
    def step(root: Node, char: Char): Option[Node]; def compile(): String; def iterRules(): Iterator[String]
  }
  // PhasePeg.scala
  object PhasePeg { val EMPTY: PegAst; def literal(c: Char): String; def inverseRepeat(source: String, width: Int, start: String = "S"): String }
  sealed abstract class PegAst { val identity: Int }   // Empty, Terminal(char), AnyChar, Ref(name), Sequence, Choice, NotPredicate, AndPredicate, Star
  final class CompactMemo(length: Int) { val width: Int; val kind: String /* "H" | "Q" */; def get(identity: Int, position: Int, default: Int = -1): Int; def update(identity: Int, position: Int, value: Int): Unit }
  class Grammar protected (val rules: collection.Map[String, PegAst], val start: String) {
    def this(source: String, start: String = "S")
    def accepts(word: String, compact: Boolean = false): Boolean; def parsePrefix(word: String, compact: Boolean = false): Option[Int]
  }
  object Grammar { def parseRules(source: String, start: String): VectorMap[String, PegAst] }
  // ScaffoldCircuit.scala
  object ScaffoldCircuit { def neg(a: Expr): Expr; def conjunction(args: Expr*): Expr; def disjunction(args: Expr*): Expr
                           def choose(guard: Expr, yes: Expr, no: Expr): Expr; def choosePointer(guard: Expr, yes: Expr, no: Expr): Expr }
  final class Value[+A] { val domain: Vector[A]; val bits: Vector[Expr]; val valid: Expr
    def cases: Vector[(A, Expr)]; def eqTo(value: Any): Expr /* Python eq */; def recode[B >: A](domain: Seq[B]): Value[B]
    def map[B](f: A => B): Value[B]; def cycle(direction: Int = 1): Value[A]; def equal(other: Value[?]): Expr }
  object Value { def apply[A](cases: Iterable[(A, Expr)]): Value[A]; def encoded[A](domain: Seq[A], bits: Iterable[Expr], valid: Expr = TRUE): Value[A]
                 def constant[A](value: A): Value[A]; def select[A](guard: Expr, yes: Value[A], no: Value[A]): Value[A] }
  final case class Ref(isNew: Expr = FALSE, prior: Expr = NULL) { def present(): Expr; def expression(): Expr }
  object Ref { def select(guard: Expr, yes: Ref, no: Ref): Ref; val NEW, EMPTY, PREVIOUS: Ref }
  final class Circuit(val alphabet: String = "ab", val checkInvariants: Boolean = true) {
    val domains: LinkedHashMap[String, (Vector[Any], Any)]; val initial: LinkedHashMap[String, Boolean]
    val labels, pointers: LinkedHashMap[String, Expr]; val currentValues: LinkedHashMap[String, Value[Any]]
    val currentRefs: LinkedHashMap[String, Ref]; val labelIds: LinkedHashMap[(String, Int), String]
    var fault: Option[Expr]; val pools: ArrayBuffer[StackPool]
    def scalar[A](key: String, domain: Seq[A], initial: A): Unit; def get[A](target: Ref, key: String, domain: Seq[A], initial: A): Value[A]
    def put(key: String, value: Value[Any]): Unit; def put[A](key: String, value: Value[A], domain: Seq[A], initial: A): Unit
    def getRef(target: Ref, key: String): Ref; def putRef(key: String, value: Ref): Unit; def input(): Value[Char]
    def require(condition: Expr, enabled: Expr = TRUE): Unit; def machine(accepting: Expr, initialAccepting: Boolean = false): Scaffold }
  // ScaffoldCircuitStructs.scala（Python finalize() は commit()）
  type CellTag = (String, Int)
  final class StackPool(val circuit: Circuit, layout: Iterable[(String, Int)], payload: Seq[Any] = Vector(None)) {
    val tags: Vector[CellTag]; val payload: Vector[Any]; val prefix: String; val used: LinkedHashMap[String, Int]
    def key(tag: CellTag, field: String): String; def scalar[A](ref: Ref, tag: Value[?], field: String, domain: Seq[A], initial: A): Value[A]
    def pointer(ref: Ref, tag: Value[?], field: String): Ref
    def allocate(name: String, previous: Ref, previousTag: Value[?], value: Ref, data: Value[?], enabled: Expr, slot: Option[Int] = None): (Ref, Value[CellTag]) }
  final class Stack(val pool: StackPool, val name: String, allocation: Option[String] = None) { var top: Ref; var tag: Value[CellTag]
    def empty(): Expr; def peek(): (Ref, Value[Any]); def pop(enabled: Expr = TRUE): (Ref, Value[Any]); def drop(enabled: Expr = TRUE): Unit
    def push(value: Ref = EMPTY, data: Option[Value[Any]] = None, enabled: Expr = TRUE, slot: Option[Int] = None): Unit
    def clear(enabled: Expr = TRUE): Unit; def copyFrom(other: Stack, enabled: Expr = TRUE): Unit; def commit(): Unit }
  final class Tape(val circuit: Circuit, val name: String, alphabet: Iterable[Any], slots: Int = 1, val blank: Any = '_', pool: Option[StackPool] = None) {
    val left, right: Stack; var focus: Value[Any]; def write(value: Value[Any], enabled: Expr = TRUE): Unit; def reset(enabled: Expr = TRUE): Unit
    def move(direction: Int, enabled: Expr = TRUE, slot: Option[Int] = None): Unit; def commit(): Unit }
  object Tape { def withSides(circuit: Circuit, name: String, alphabet: Iterable[Any], slots: (Int, Int), blank: Any = '_', pool: Option[StackPool] = None): Tape }  // Python slots=(l, r)
  final class Counter(pools: Map[String, StackPool], val name: String, allocationName: Option[String] = None) { def this(pool: StackPool, name: String, allocationName: Option[String]); def this(pool: StackPool, name: String)
    var positiveStack, negativeStack: Stack /* Python pos/neg; reassignable */; def pos: Stack /* alias */
    def positive(), negative(), zero(): Expr; def inc/dec(enabled: Expr = TRUE, slot: Option[Int] = None): Unit; def reset(enabled); def copyFrom(other, enabled); def commit(): Unit }
  final class Queue(pools: Map[String, StackPool], counterPools: Map[String, StackPool], val name: String, val sharedSlots: Boolean = false) { def this(pool: StackPool, counterPool: StackPool, name: String[, sharedSlots: Boolean])
    val stacks: VectorMap[String, Stack]; val m, c: Counter; var phase: Value[String]
    def push(value: Ref, enabled: Expr = TRUE): Unit; def pop(enabled: Expr = TRUE): Ref; def empty(): Expr; def clear(enabled); def work(enabled); def workUnit(enabled); def copyFrom(other, enabled); def commit(): Unit }
  // PegFile.scala
  final class RuleMap(data: ByteBuffer, offsets: Map[String, Int]) extends mutable.AbstractMap[String, PegAst]  // apply() で遅延ロード、get/contains/size はロード済みのみ
  final class FileGrammar(path: Path, start: String = "S") extends Grammar with AutoCloseable { val ruleCount: Int; def close(): Unit }
  // GenerateScaffoldExamples.scala / GeneratePhaseExamples.scala
  object GenerateScaffoldExamples { def markedPalindrome(): Scaffold; def summary(output: String): String; def locateDirectory(args: Array[String]): Path; def main(args: Array[String]): Unit }
  object GeneratePhaseExamples { def examples(directory: Path): Vector[(String, String)]; def main(args: Array[String]): Unit }
  ```
  注意: `generated/scaffold_marked_palindrome.peg` は旧版 emitter の出力（同じ 35 規則、`E_i` 番号が異なる）で、
  現行 Python 自身もバイト一致しない。Scala は現行 Python とバイト一致し、ゴールデンとは言語同値で検査している。
  `generated/sparse_*.peg` は `symbolic_tm2peg`（Task 2d）の出力であり、このタスクの生成器の対象外。

### Task 2（並列）: L0 独立モジュール群（4 サブタスク、別エージェント）
- 2a: scavm, scavm_structs, scavm_pal, stage5_port_block1 + tests
- 2b: fpp_finite, fpp_subroutine, fpp_reuse, fpp_cost, dp_finite, dp_search_finite,
  dp_search_reuse, chain_finite, move_center_finite, galil_clock, fpp, fpp_tape + tests、
  `generated/*-controller.json` の再生成一致
- 2c: gs_heads, gs_overlap, gs_local_clock, gs_flag_heads, gs_match_heads, gs_head_liveness,
  gs_events, gs_dual_flags, gs_batch_clock, delayed_pal, gs_flag_trace, gs_match_trace,
  galil_contracts + tests
- 2d: tm2peg, symbolic_tm2peg, twoway, twoway_border, lps_halving, online_manacher, read_blocks,
  stage1_kmp_online, stage2_tm_galil, stage3_tm_galil_chain, stage3b_design_check, peg_file,
  compact_scaffold_peg, verify_window_pal, analysis/grammar_closure, analysis/grammar_scc + tests、
  `generated/anbn_from_tm.peg`, `marked_palindrome_from_tm.peg` の一致

### Task 3: SCAVM 足場群（2a, 2b に依存）
scaffold_input, scaffold_places, scaffold_program, scaffold_search, scaffold_chain, scaffold_galil,
galil_realtime, scaffold_pal + tests

### Task 4: 回路群（1, 2b, 2c, 3 に依存。2 サブタスク）
- 4a: scaffold_optimize, scaffold_artifact, scaffold_round, scaffold_round_lazy, scaffold_round_tree,
  scaffold_rom, scaffold_event_buffer, scaffold_queue_registers, scaffold_head_distances,
  scaffold_live_distances, scaffold_stream_heads, midpoint_peg（`generated/midpoint.peg` 一致）
- 4b: scaffold_circuit_input, scaffold_circuit_program, scaffold_circuit_search,
  scaffold_circuit_chain, scaffold_circuit_galil, scaffold_match_input, scaffold_gs_heads,
  scaffold_gs_matcher, scaffold_gs_flags, scaffold_delayed_pal, generate_galil_peg, generate_online_peg
- **4a 実装済み API（2026-09-07、part 1: optimize, artifact, round, round_lazy, round_tree, event_buffer,
  queue_registers, head_distances, stream_heads, midpoint_peg, compact_scaffold_peg。scaffold_rom と
  scaffold_live_distances は未着手）**。Python `finalize()` は `commit()`。
  ```scala
  // ScaffoldOptimize.scala
  object ScaffoldOptimize { final case class OptimizeStats(rounds, constantLabels, nullPointers, labelsRemoved, pointersRemoved: Int)
    def children(expression: Expr): Vector[Expr]
    def project(initial, labels, pointers: collection.Map, roots: Seq[String], accepting: String, alphabet: String): Scaffold
    def optimize(machine: Scaffold, roots: Seq[String] = Nil): (Scaffold, OptimizeStats) }
  // ScaffoldArtifact.scala（CPython marshal 互換の .sca/.sca.gz。Python 側と相互に読める）
  object ScaffoldArtifact { val MAGIC: Array[Byte]; val OPS: Vector[String]
    def write(machine: Scaffold, path: Path, metadata: Any = None): Int; def read(path: Path): (Scaffold, Any) }
  object PyMarshal { final class Writer(out: OutputStream) { def dump(value: Any): Unit }; final class Reader(in: InputStream) { def load(): Any } }
  // ScaffoldRound.scala（Address.local の併合順は CPython の dict_keys 和集合順を再現: CPythonSetOrder）
  final case class Address(local: VectorMap[Int, Expr], prior: Expr, tag: Value[Int]);  type RoundValue = Expr | Address
  class RoundBuilder(stages: Seq[Scaffold], inputSymbols: Option[Seq[collection.Map[Char, Expr]]] = None, alphabet: Option[String] = None) {
    val stages, source, alphabet, inputSymbols, tags, bits, labels, pointers, initial, slotLabels, slotPointers, zeroTag, empty
    def select(guard, yes: Address, no: Address): Address; def exists(target: Address): Expr; def possibleTags(tag: Value[Int]): Vector[Int]
    def read(target: Address, key: String): Expr; def follow(target: Address, key: String): Address
    def translate(expression: Expr, slot: Int, root: Address, memo: java.util.IdentityHashMap[Expr, RoundValue]): RoundValue; def build(): Scaffold }
  object RoundBuilder { def label(slot, key); def field(slot, key); def tagBit(slot, key, bit) }
  object ScaffoldRound { def packRound(stages, inputSymbols = None, alphabet = None): Scaffold }
  // ScaffoldRoundLazy.scala
  enum FieldKind { case Label, Pointer }; final case class SlotField(kind, slot, key); final class MissingField(val field: SlotField) extends RuntimeException
  final class DemandRoundBuilder(...) extends RoundBuilder { def need(kind, slot, key); def resolve(field: SlotField): RoundValue; override def build() }
  object ScaffoldRoundLazy { def packRoundLazy(stages, inputSymbols = None, alphabet = None): Scaffold }
  // ScaffoldRoundTree.scala / ScaffoldEventBuffer.scala
  object ScaffoldRoundTree { def packServiceTree(wrapper: Scaffold, service: Int): Scaffold }
  object ScaffoldEventBuffer { val PREFIX = "source."
    def substituteSource(source: Scaffold, symbols: collection.Map[Char, Expr]): (LinkedHashMap[String, Expr], LinkedHashMap[String, Expr])
    def bufferSource(source: Scaffold, readyLabel, eventLabel, valueLabel: String): (Circuit, Scaffold)
    def packService(wrapper: Scaffold, service: Int, lazyRound: Boolean = false): Scaffold }
  // ScaffoldQueueRegisters.scala（Queue が counter ごとに pos/neg 別プールを受けるよう ScaffoldCircuitStructs.Queue を拡張）
  final class QueueRegisters(val circuit: Circuit, names: Seq[String]) { val names; val cells: Map[String, StackPool]
    val counterCells: Map[String, Map[String, StackPool]]; val queues: VectorMap[String, Queue]; def commit(): Unit }
  object ScaffoldQueueRegisters { def fixture(): (Circuit, QueueRegisters, Scaffold) }
  // ScaffoldHeadDistances.scala
  final class HeadDistances(circuit: Circuit, names: Seq[String], moves: Option[collection.Map[String, (Int, Int)]] = None,
                            prefix: String = "head.distance", val exclusiveMoves: Boolean = false) {
    val names, index, layout, keys, pool: StackPool, counters: VectorMap[(String, String), Counter]
    def equal(left, right): Expr; def less(left, right): Expr; def move(head, direction: Int, enabled = TRUE); def copy(target, source, enabled = TRUE)
    def coincide(enabled = TRUE); def commit(): Unit }
  // ScaffoldStreamHeads.scala
  final class StreamBank(val circuit: Circuit, names: Seq[String]) { val cells: StackPool; val queues: QueueRegisters; val heads: VectorMap[String, StreamHead]; def commit() }
  final class StreamHead(bank, name) { var focus: Ref; val left, right: Stack; val queue: Queue; def canRight(): Expr; def peekRight(enabled = TRUE): Ref
    def moveRight(enabled): Expr; def moveLeft(enabled); def followArrival(cell: Ref, enabled); def copyFrom(other, enabled); def reset(enabled); def commit() }
  final class PatternTextHead(bank, name) { def available(): Expr; def read(enabled = TRUE): Value[Any]; def start(snapshot: StreamHead, enabled)
    def move(direction: Int, enabled): (String, Expr); def copyFrom(other, enabled); def commit() }
  final class OrientedHead(bank, name) { def start(snapshot, reversed: Boolean, enabled); def read(enabled = TRUE): Value[Any]; def move(direction, enabled): (String, Expr); def copyFrom; def commit() }
  final class MirrorHead(bank, name) { def start(begin, end: StreamHead, atEnd: Boolean, enabled); def read(enabled = TRUE): Value[Any]; def move(direction, enabled): (String, Expr); def copyFrom; def commit() }
  // MidpointPeg.scala / CompactScaffoldPeg.scala
  object MidpointPeg { def build(): (Circuit, Scaffold); def grammar(): String; def summary(output: String, source: String): String; def main(args: Array[String]) }
  object CompactScaffoldPeg { final case class CompactStats(beforeRules, afterRules, fused, beforeBytes, afterBytes: Long, inlinePrivate: Boolean) { def toJson: String }
    def identifier(name: String): Long; def shortened(name: String): String; def references(body: String): Iterator[Long]; def needsGroup(body, before, after: String): Boolean
    def compact(source: Path, target: Path, shortNames: Boolean = false, inlinePrivate: Boolean = false): CompactStats
    def main(args: Array[String]) /* [--short-names] [--inline-private] SOURCE TARGET */ }
  ```
  差分テスト: `generated/midpoint.peg` はバイト一致で再生成。compact は小文法・midpoint 系文法（2 種 × 4 フラグ）で Python と
  バイト一致。`compact` は `generated/midpoint.peg` そのもの（H/HalfCeil/HalfFloor を含む）を Python と同じ理由で拒否する。

### Task 5: 窓群と最終生成器（4 に依存）
scaffold_window_counter, scaffold_window_positions, scaffold_window_registers, scaffold_window_live,
scaffold_window_stream, scaffold_window_gs, scaffold_window_gs_live, scaffold_flag_packets,
scaffold_window_workers, scaffold_window_pal, generate_window_pal + tests。
差分：`generate_window_pal.py` と Scala 版を `--skip-optimize` で走らせた未圧縮 .peg の SHA 一致
（メモリ 22 GiB 級。無理なら `test_generate_window_pal.py` 相当の小さい構成での一致で代替し、
STATUS.md に未確認と明記）。

### Task 6: 文書・ビルド統合
STATUS.md §4 の再現手順に Scala 版を併記、README の pointer、Makefile `scala` ターゲットに
含まれることの確認、`PLAIN_PAL_ARTIFACT.md` に「Scala 版は Python 版とバイト一致（範囲を明記）」。
