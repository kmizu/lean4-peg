package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Finite-state lowering of the offline FPP kernel; not a real-time PAL PEG.
  *
  * Generated instructions are only read/branch, write, unit move, emit and halt.
  * No callbacks, integer registers, dynamic call stack or address tests survive
  * construction. Each instruction is one simulated step on seven independent
  * tapes. Offline input loading and external decoding of emitted head positions
  * are deliberately separate. See FISCHER_PATERSON.md for the invariants.
  *
  * Python 原典: `fpp_finite.py`。
  */
object FppFinite {
  val LEFT: String = "^"
  val END: String = "$"
  val BLANK: String = "_"

  /** The seven kernel tapes, in order. */
  val A: Int = 0
  val B: Int = 1
  val C: Int = 2
  val S: Int = 3
  val T: Int = 4
  val BACK: Int = 5
  val FRONT: Int = 6

  /** Python の `("halt",)` 等のタプルに対応する命令。 `Read` の分岐表は挿入順を保つ。 */
  sealed trait Instruction {
    /** Python の `instruction[0]`。 */
    def op: String
  }

  object Instruction {
    case object Halt extends Instruction { val op = "halt" }
    /** Record the A head position externally, then continue at `next`. */
    final case class Emit(next: Int) extends Instruction { val op = "emit" }
    final case class Move(tape: Int, direction: Int, next: Int) extends Instruction { val op = "move" }
    final case class Write(tape: Int, symbol: String, next: Int) extends Instruction { val op = "write" }
    final case class Read(tape: Int, choices: VectorMap[String, Int]) extends Instruction { val op = "read" }
  }

  /** 挿入順を保つ分岐表。Python の dict リテラルと同じ規則: 既存キーの更新は位置を保つ。 */
  def choices(entries: (String, Int)*): VectorMap[String, Int] = VectorMap.from(entries)

  /** 実行結果。Python の dataclass `Run`。`tapes` は実行に使ったテープそのもの（複製ではない）。 */
  final case class Run(
    borders: Vector[Int],
    steps: Int,
    tapes: Vector[Tape] = Vector.empty,
    positions: Vector[Int] = Vector.empty,
    state: Int = -1
  )

  /** 疎なテープ: Python の `dict[int, str]`。未訪問セルは `BLANK`。
    *
    * `read`/`write` はサブクラスで差し替え可能（テストの局所性ガード用）。
    * 等価性は内容で決まる（Python の dict 比較と同じ）。
    */
  class Tape(initial: Iterable[(Int, String)] = Nil) {
    private val store = mutable.HashMap.from(initial)

    def read(position: Int): String = store.getOrElse(position, BLANK)
    def write(position: Int, symbol: String): Unit = { store.update(position, symbol) }

    /** Python の `tape[i]`（存在しなければ例外）。 */
    def apply(position: Int): String = store(position)
    def get(position: Int): Option[String] = store.get(position)
    def contains(position: Int): Boolean = store.contains(position)
    def values: Iterable[String] = store.values
    def toMap: Map[Int, String] = store.toMap
    def size: Int = store.size
    /** Python の `dict(tape)`。 */
    def copy: Tape = new Tape(store)

    override def equals(other: Any): Boolean = other match {
      case that: Tape => this.toMap == that.toMap
      case _ => false
    }
    override def hashCode: Int = toMap.hashCode
    override def toString: String = store.toSeq.sortBy(_._1).map { case (i, s) => s"$i: $s" }.mkString("Tape(", ", ", ")")
  }

  object Tape {
    def empty: Tape = new Tape()
    /** Python の `dict(enumerate(LEFT + word + END))`。 */
    def bounded(word: String): Tape = new Tape((LEFT + word + END).zipWithIndex.map { case (c, i) => (i, c.toString) })
    /** Python の `dict(enumerate(tokens))`。 */
    def of(tokens: Seq[String]): Tape = new Tape(tokens.zipWithIndex.map(_.swap))
    /** Python の `[{} for _ in range(n)]`。 */
    def fresh(n: Int): Array[Tape] = Array.fill(n)(new Tape())
  }

  /** A finite controller: an instruction table with labelled states.
    *
    * Python 版はビルダーが属性を後付けする（`p.found = ...`）。ここでは同じ名前の
    * 任意フィールドとして持つ。`-1`/`None`/空は未設定。
    */
  class Program(alphabetSymbols: Iterable[String], val ntapes: Int = 7) {
    val alphabet: Vector[String] = alphabetSymbols.toVector
    if (alphabet.isEmpty || alphabet.distinct.size != alphabet.size) {
      throw new IllegalArgumentException("nonempty distinct alphabet required")
    }
    if (alphabet.exists(s => s.length != 1 || Set(LEFT, END, BLANK, "0", "1").contains(s))) {
      throw new IllegalArgumentException("alphabet collides with work-tape symbols")
    }

    /** `None` は `reserve()` 済みで未解決の継続。 */
    val code: mutable.ArrayBuffer[Option[Instruction]] = mutable.ArrayBuffer.empty
    var start: Int = -1

    // ---- labels attached by the builders of the derived kernels ----
    /** Symbols the caller may put on the source/window tapes (excludes the private `#`). */
    var sourceAlphabet: Vector[String] = Vector.empty
    var found: Option[Int] = None
    var missed: Option[Int] = None
    var cleanup: Option[Int] = None
    var finished: Option[Int] = None
    /** dp_search_reuse: the unary distance tape index. */
    var distance: Option[Int] = None
    var inputs: Vector[Int] = Vector.empty
    var scratch: Vector[Int] = Vector.empty
    /** Tapes that hold one scalar cell at the origin (`None` = attribute absent in Python). */
    var scalarTapes: Option[Vector[Int]] = None
    /** Control state -> cleanup entry to take when cancelled there (insertion-ordered). */
    val cancelEntries: mutable.LinkedHashMap[Int, Int] = mutable.LinkedHashMap.empty
    /** chain_finite: states at which the caller may write PORT. */
    var ready: Set[Int] = Set.empty
    var confirmedReady: Set[Int] = Set.empty
    /** chain_finite: halt state -> outcome name (insertion-ordered). */
    val outcomes: mutable.LinkedHashMap[Int, String] = mutable.LinkedHashMap.empty

    def reserve(): Int = {
      code += None
      code.size - 1
    }

    def add(instruction: Instruction): Int = {
      val state = reserve()
      code(state) = Some(instruction)
      state
    }

    def move(tape: Int, direction: Int, nextState: Int): Int = add(Instruction.Move(tape, direction, nextState))

    def write(tape: Int, symbol: String, nextState: Int): Int = add(Instruction.Write(tape, symbol, nextState))

    def branch(tape: Int, choices: VectorMap[String, Int]): Int = add(Instruction.Read(tape, choices))

    /** Resolve a reserved state with a branch. */
    def branch(tape: Int, choices: VectorMap[String, Int], state: Int): Int = {
      assert(code(state).isEmpty)
      code(state) = Some(Instruction.Read(tape, choices))
      state
    }

    /** Python の `p.code[q]`（未解決なら例外）。 */
    def instruction(q: Int): Instruction = code(q).getOrElse(throw new IllegalStateException(s"unresolved continuation $q"))

    /** Python の `p.code[q] = row`。 */
    def set(q: Int, instruction: Instruction): Unit = { code(q) = Some(instruction) }

    /** Replace this program's table by a copy of another table (`p.code = list(other.code)`). */
    def copyCodeFrom(other: Program): Unit = {
      code.clear()
      code ++= other.code
    }

    /** All instructions, which must be resolved. */
    def instructions: Vector[Instruction] = code.indices.iterator.map(instruction).toVector

    def validate(): Unit = {
      assert(0 <= start && start < code.size)
      for (slot <- code) {
        assert(slot.isDefined, "unresolved continuation")
        val row = slot.get
        row match {
          case Instruction.Read(tape, _) => assert(0 <= tape && tape < ntapes)
          case Instruction.Move(tape, direction, _) =>
            assert(0 <= tape && tape < ntapes)
            assert(direction == -1 || direction == 1)
          case Instruction.Write(tape, _, _) => assert(0 <= tape && tape < ntapes)
          case _ => ()
        }
        val targets: Iterable[Int] = row match {
          case Instruction.Read(_, choices) =>
            assert(choices.nonEmpty)
            choices.values
          case Instruction.Halt => Nil
          case Instruction.Emit(next) => Seq(next)
          case Instruction.Move(_, _, next) => Seq(next)
          case Instruction.Write(_, _, next) => Seq(next)
        }
        assert(targets.forall(q => 0 <= q && q < code.size))
      }
    }

    /** Preload `^word$` on A and B, the delta(-1) encoding on C and run to the halt. */
    def run(word: String, maxSteps: Option[Int] = None): Run = {
      if (word.exists(c => !alphabet.contains(c.toString))) {
        throw new IllegalArgumentException("input outside declared alphabet")
      }
      val z = Tape.bounded(word)
      val tapes = Array(z, z.copy, new Tape(Seq(0 -> "0", 1 -> "1", 2 -> "0")),
        new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)))
      val positions = Array(0, 1, 0, 0, 0, 0, 0)
      // The cap is an external test watchdog, not part of the machine.
      execute(tapes, positions, maxSteps.getOrElse(1000 * (word.length + 1)))
    }

    def execution(tapes: scala.collection.IndexedSeq[Tape], positions: Array[Int]): Execution = execution(tapes, positions, start)

    def execution(tapes: scala.collection.IndexedSeq[Tape], positions: Array[Int], start: Int): Execution =
      new Execution(this, tapes, positions, start)

    /** Run at most `maxSteps` local instructions from a finite control state. */
    def execute(tapes: scala.collection.IndexedSeq[Tape], positions: Array[Int], maxSteps: Int): Run = execute(tapes, positions, maxSteps, start)

    def execute(tapes: scala.collection.IndexedSeq[Tape], positions: Array[Int], maxSteps: Int, start: Int): Run = {
      val machine = execution(tapes, positions, start)
      while (!machine.done) {
        if (machine.steps >= maxSteps) {
          throw new IllegalStateException("finite controller exceeded watchdog")
        }
        machine.step()
      }
      machine.result()
    }
  }

  object Program {
    /** `Program("ab#")`: each character is one alphabet symbol. */
    def apply(alphabet: String, ntapes: Int = 7): Program = new Program(alphabet.map(_.toString), ntapes)
  }

  /** Resumable VM; addresses and observation stay outside controller code. */
  final class Execution(val program: Program, val tapes: scala.collection.IndexedSeq[Tape], val positions: Array[Int], initialState: Int) {
    assert(tapes.size == positions.length && positions.length == program.ntapes)
    var state: Int = initialState
    var steps: Int = 0
    val emitted: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty
    var done: Boolean = false

    def step(): Unit = {
      if (done) {
        throw new IllegalStateException("cannot step a halted controller")
      }
      val row = program.instruction(state)
      steps += 1
      row match {
        case Instruction.Halt =>
          done = true
        case Instruction.Emit(next) =>
          emitted += positions(A)
          state = next
        case Instruction.Read(tape, choices) =>
          val symbol = tapes(tape).read(positions(tape))
          state = choices.getOrElse(symbol,
            throw new IllegalStateException(s"undefined transition at $state, tape $tape: $symbol"))
        case Instruction.Move(tape, direction, next) =>
          positions(tape) += direction
          if (positions(tape) < 0) {
            throw new IllegalStateException("left-end crossing")
          }
          state = next
        case Instruction.Write(tape, symbol, next) =>
          tapes(tape).write(positions(tape), symbol)
          state = next
      }
    }

    def result(): Run = {
      if (!done) {
        throw new IllegalStateException("controller has not halted")
      }
      Run(emitted.toVector, steps, tapes.toVector, positions.toVector, state)
    }
  }

  /** Compile-time macros only; all continuations become integer state labels. */
  final class Builder(val p: Program) {

    def push(tape: Int, symbol: String, k: Int): Int = p.move(tape, 1, p.write(tape, symbol, k))

    def pop(tape: Int, k: Int): Int = p.write(tape, BLANK, p.move(tape, -1, k))

    /** Copy the unary counter S onto T (T's head stays at its top), restoring S's head. */
    def copySToT(k: Int): Int = {
      val back = p.reserve()
      val restore = p.reserve()
      p.branch(S, choices(BLANK -> p.move(S, -1, k), "1" -> p.move(S, 1, restore)), restore)
      p.branch(S, choices(LEFT -> p.move(S, 1, restore), "1" -> push(T, "1", p.move(S, -1, back))), back)
      back
    }

    /** Read the next delta bit on C, materializing it from the BACK/FRONT queue on a blank. */
    def deltaRead(zero: Int, one: Int): Int = {
      val front = p.reserve()
      val transfer = p.reserve()
      val outcomes = Seq("0" -> zero, "1" -> one)
      p.branch(FRONT, choices((Seq(LEFT -> transfer) ++ outcomes.map { case (bit, dest) =>
        bit -> pop(FRONT, p.write(C, bit, dest))
      })*), front)
      p.branch(BACK, choices((Seq(LEFT -> front) ++ outcomes.map { case (bit, _) =>
        bit -> pop(BACK, push(FRONT, bit, transfer))
      })*), transfer)
      p.branch(C, choices("0" -> zero, "1" -> one, BLANK -> front))
    }

    /** Fall back along the border chain by the unary count on S, then continue at `k`. */
    def fallback(k: Int, appendDistance: Boolean): Int = {
      val more = p.reserve()
      val scan = p.reserve()
      var afterZero = p.move(A, -1, pop(T, more))
      if (appendDistance) {
        afterZero = push(BACK, "1", afterZero)
      }
      val read = deltaRead(afterZero, pop(S, p.move(C, -1, scan)))
      // Reserve a read-state alias with a finite branch on C. This dispatch
      // neither seeks nor changes a tape, and handles lazy materialization.
      p.branch(C, choices(Seq("0", "1", BLANK).map(_ -> read)*), scan)
      p.branch(T, choices(LEFT -> k, "1" -> p.move(C, -1, scan)), more)
      copySToT(more)
    }
  }

  /** Python の `build_program(alphabet="ab#")`。 */
  def buildProgram(alphabet: String = "ab#"): Program = {
    val p = Program(alphabet)
    val b = new Builder(p)
    val symbols = p.alphabet
    val halt = p.add(Instruction.Halt)
    val chain = p.reserve()
    val emit = p.add(Instruction.Emit(b.fallback(chain, false)))
    p.branch(A, choices((Seq(LEFT -> halt) ++ symbols.map(_ -> emit))*), chain)
    val nextInput = p.reserve()
    val advance = p.move(B, 1, nextInput)
    val matchedScan = p.reserve()
    val scan = b.deltaRead(advance, b.push(S, "1", p.move(C, 1, matchedScan)))
    p.branch(C, choices(Seq("0", "1", BLANK).map(_ -> scan)*), matchedScan)
    val matched = b.push(BACK, "0", p.move(C, 1, matchedScan))
    val failedAtLeft = b.push(BACK, "1", b.push(BACK, "0", advance))
    var nextChoices = choices(END -> chain)
    for (symbol <- symbols) {
      val compare = p.reserve()
      val retry = p.move(A, 1, compare)
      val fallback = b.fallback(retry, true)
      val failed = p.move(A, -1, p.branch(A, choices((Seq(LEFT -> failedAtLeft) ++ symbols.map(_ -> fallback))*)))
      p.branch(A, choices((symbols :+ END).map(c => c -> (if (c == symbol) { matched } else { failed }))*), compare)
      nextChoices = nextChoices.updated(symbol, retry)
    }
    p.branch(B, nextChoices, nextInput)
    p.start = p.branch(B, choices((Seq(END -> halt) ++ symbols.map(_ -> advance))*))
    p.validate()
    p
  }
}
