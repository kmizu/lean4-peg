package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** External, coordinate-based observations of the online source contracts.
  *
  * Nothing in this module participates in the recognizer's decisions. It decodes
  * immutable stacks only at algorithm boundaries, using the already offered input
  * as an independent oracle. Passing finite traces is not a proof of the source.
  *
  * Port of `galil_contracts.py`. The Python module reads the scaffold VM's
  * `Node` objects (`scavm.py`) and the `OnlineGalil`/`OnlineStep`/`Timing`
  * objects of `scaffold_galil.py`/`galil_clock.py`, which belong to later
  * tasks. This port therefore observes them through the small structural
  * interfaces [[GalilContracts.Node]], [[GalilContracts.Source]],
  * [[GalilContracts.StepResult]] and [[GalilContracts.Timing]]; the ports of
  * those modules implement (or adapt to) these traits.
  */
object GalilContracts {

  /** A scaffold label value (`scavm.Node.label` entries are strings, ints or booleans). */
  type LabelValue = String | Int | Boolean

  /** One immutable scaffold node: creation tick, labels and pointers. */
  trait Node {
    def t: Int
    def label(key: String): LabelValue
    def ptr(key: String): Option[Node]
  }

  /** The timing parameters the audit checks against (`galil_clock.Timing`). */
  trait Timing {
    def moveSlope: Int
    def intervalOverhead: Int
    def predictability: Int
  }

  /** The online source (`scaffold_galil.OnlineGalil`): the VM's top node and its timing. */
  trait Source {
    def top: Node
    def timing: Timing
  }

  /** One `read`/`work` result (`scaffold_galil.OnlineStep`). */
  trait StepResult {
    def output: Option[Int]
    def inputReady: Boolean
    def events: Map[String, Int]
  }

  /** A symbol of the doubled coordinate line: `None` at 0, the separator `"s"`
    * at even positions and the word's characters at odd ones.
    */
  type Cell = Option[String]

  private def labelString(value: LabelValue): String = {
    value match {
      case s: String => s
      case i: Int => i.toString
      case b: Boolean => if (b) "True" else "False"
    }
  }

  private def labelInt(value: LabelValue): Int = {
    value match {
      case i: Int => i
      case b: Boolean => if (b) 1 else 0
      case s: String => throw new IllegalArgumentException(s"integer label expected, got '$s'")
    }
  }

  private def labelBoolean(value: LabelValue): Boolean = {
    value match {
      case b: Boolean => b
      case i: Int => i != 0
      case s: String => s.nonEmpty
    }
  }

  /** The height of the immutable stack `name`. */
  def depth(root: Node, name: String): Int = {
    var node = root.ptr(name + ".top")
    var creator = labelString(root.label(name + ".tname"))
    var slot = labelString(root.label(name + ".tslot"))
    var count = 0
    while (node.isDefined) {
      val key = s"$creator.$slot."
      val current = node.get
      creator = labelString(current.label(key + "bname"))
      slot = labelString(current.label(key + "bslot"))
      node = current.ptr(key + "below")
      count += 1
    }
    count
  }

  /** A signed unary counter: positive minus negative stack heights. */
  def number(root: Node, name: String): Int = depth(root, name + ".pos") - depth(root, name + ".neg")

  /** A head position on the doubled line. */
  def place(root: Node, name: String): Int = {
    2 * depth(root, name + ".l") - (if (!labelBoolean(root.label(name + ".gap"))) 1 else 0)
  }

  /** The cells of the doubled line between two positions, inclusive. */
  def interval(word: String, left: Int, right: Int): Vector[Cell] = {
    if (!(0 <= left && left <= right && right <= 2 * word.length)) {
      throw new AssertionError((word, left, right).toString)
    }
    (left to right).toVector.map { p =>
      if (p == 0) None else if (p % 2 == 0) Some("s") else Some(word(p / 2).toString)
    }
  }

  def palindrome[A](value: Seq[A]): Boolean = value == value.reverse

  /** Diagnostic sufficient witness to a live chain forbidden at main entry.
    *
    * A palindromic block of width 2h ending at C determines its alternating
    * reflection extension. Check whether that extension still reaches R. This
    * observer does not replace the paper's chain lemmas or test maximal chains.
    */
  def smallLivePeriod(word: String, center: Int, lower: Int, right: Int): Option[Int] = {
    val limit = math.min(lower, (center - 1) / 2)
    (1 to limit).find { h =>
      val block = interval(word, center - 2 * h, center)
      palindrome(block) && {
        val expected = (0 to right - center).toVector.map { i =>
          block(2 * h - math.min(i % (2 * h), 2 * h - i % (2 * h)))
        }
        interval(word, center, right) == expected
      }
    }
  }

  /** One recorded audit row: the event name, tick and decoded coordinates. */
  final case class AuditRow(event: String, tick: Int, values: VectorMap[String, Int]) {
    def apply(key: String): Int = values(key)
  }

  private def check(condition: Boolean, context: => Any): Unit = {
    if (!condition) {
      throw new AssertionError(context.toString)
    }
  }

  /** Records and checks the contracts at every algorithm boundary. */
  final class ContractAudit {
    private var previous: Option[Node] = None
    private var move: Option[AuditRow] = None
    private var replay: Option[AuditRow] = None
    private var shift: Option[AuditRow] = None
    val counts: mutable.LinkedHashMap[String, Int] = mutable.LinkedHashMap.empty
    val rows: mutable.ArrayBuffer[AuditRow] = mutable.ArrayBuffer.empty
    private var lastOutput: Option[AuditRow] = None

    def record(event: String, root: Node, values: (String, Int)*): AuditRow = {
      counts(event) = counts.getOrElse(event, 0) + 1
      val row = AuditRow(event, root.t, VectorMap.from(values))
      rows += row
      row
    }

    private def places(root: Node, names: String*): Seq[Int] = names.map(place(root, _))

    private def observeDpFound(root: Node, word: String, old: Option[Node]): Unit = {
      val found = labelString(root.label("sp.mode")) == "found" &&
        old.forall(node => labelString(node.label("sp.mode")) != "found")
      if (found) {
        val Seq(c, r) = places(root, "C", "R")
        val lower = number(root, "sp.lo")
        val h = depth(root, "dp.t11.l")
        val candidates = (lower + 1 to (c - 1) / 4).filter { step =>
          palindrome(interval(word, c - 4 * step, c)) && palindrome(interval(word, c - 2 * step, c))
        }
        val row = record("dp_found", root, "C" -> c, "R" -> r, "h" -> h, "lower" -> lower)
        check(candidates.nonEmpty && h == candidates.min, row)
        check(r - c < 2 * h, row)
      }
    }

    private def observeMain(root: Node, word: String): Unit = {
      val Seq(c, r, l) = places(root, "C", "R", "L")
      val lower = number(root, "sp.lo")
      val row = record("main", root, "C" -> c, "R" -> r, "L" -> l, "lower" -> lower)
      check(lower <= r - c && 3 * (r - c) <= 5 * lower, row)
      check(number(root, "g.rad") == r - c && l == 2 * c - r, row)
      check(palindrome(interval(word, l, r)), row)
      check(smallLivePeriod(word, c, lower, r).isEmpty, row)
    }

    private def observeMove(root: Node, word: String): Unit = {
      val Seq(c, r, l) = places(root, "C", "R", "L")
      val value = interval(word, l + 1, r)
      val size = (1 to value.length by 2).filter(n => palindrome(value.takeRight(n))).max
      val row = record("move", root, "C" -> c, "R" -> r, "L" -> l, "selected" -> (r - (size - 1) / 2))
      move = Some(row)
      check(l == 2 * c - r && number(root, "g.rad") == r - c, row)
      check(number(root, "g.rem") == value.length, row)
    }

    private def observeReplayStart(root: Node): Unit = {
      check(move.isDefined, "replay without a move")
      val moved = move.get
      val c = place(root, "C")
      val rr = moved("R")
      val row = record("replay_start", root, "C" -> c, "RR" -> rr)
      check(c == moved("selected"), (moved, row))
      check(4 * (c - moved("C")) > rr - moved("C") - 1, row)
      check(moved("C") < c && c <= rr, row)
      check(place(root, "R") == c && place(root, "L") == c, row)
      check(number(root, "g.rad") == 0 && number(root, "g.replay") == rr - c, row)
      move = None
      replay = Some(row)
    }

    private def observeReplayReturn(root: Node): Unit = {
      val started = replay.get
      val c = started("C")
      val rr = started("RR")
      val row = record("replay_return", root, "C" -> c, "RR" -> rr)
      check(place(root, "R") == rr && place(root, "C") == c, row)
      check(place(root, "L") == 2 * c - rr, row)
      check(number(root, "g.rad") == rr - c, row)
      check(number(root, "g.len") == 2 * (rr - c) + 1, row)
      check(number(root, "g.replay") == 0, row)
      replay = None
    }

    private def observeShift(root: Node): Unit = {
      val Seq(c, r, l) = places(root, "C", "R", "L")
      val h = number(root, "ch.h")
      val row = record("shift", root, "C" -> c, "R" -> r, "L" -> l, "h" -> h)
      shift = Some(row)
      check(h > 0 && number(root, "g.rem") == h, row)
      check(labelInt(root.label("ch.phase")) == 4 && number(root, "ch.lag") == 0, row)
    }

    private def observeShiftReturn(root: Node, word: String): Unit = {
      check(shift.isDefined, "shift return without a shift")
      val shifted = shift.get
      val (c, r, l, h) = (shifted("C"), shifted("R"), shifted("L"), shifted("h"))
      val row = record("shift_return", root, "C" -> (c + h), "R" -> r, "h" -> h)
      check(place(root, "C") == c + h && place(root, "L") == l + 2 * h, row)
      check(place(root, "R") == r && number(root, "g.rad") == r - c - h, row)
      check(number(root, "g.len") == 2 * (r - c - h) + 1, row)
      check(number(root, "ch.cycle") == 2 * h, row)
      check(palindrome(interval(word, l + 2 * h, r)), row)
      shift = None
    }

    private def observeOutput(source: Source, root: Node, word: String, output: Int): Unit = {
      check(output == (if (palindrome(word)) 1 else 0), (word, output))
      val c = place(root, "C")
      val size = word.length
      check(c >= size && (c == size) == (output != 0), (word, c))
      val current = record("output", root, "size" -> size, "value" -> output, "C" -> c,
        "prediction" -> math.max(c - size - 1, 0))
      lastOutput.foreach { before =>
        val ticks = root.t - before.tick
        val delta = c - before("C")
        val timing = source.timing
        check(delta >= 0, (before, current))
        check(ticks <= timing.moveSlope * delta + timing.intervalOverhead, current)
        if (output != 0) {
          check(ticks <= timing.predictability, (before, current))
        }
        val gain = current("prediction") - before("prediction")
        check((gain + 2) * timing.predictability >= ticks, (before, current))
      }
      lastOutput = Some(current)
    }

    /** Observe the source after one `read`/`work` on the prefix `word`. */
    def observe(source: Source, word: String, result: StepResult): Unit = {
      val root = source.top
      val old = previous
      val oldMode = old.map(node => labelString(node.label("g.mode")))
      val mode = labelString(root.label("g.mode"))
      def event(name: String): Boolean = result.events.getOrElse(name, 0) != 0

      observeDpFound(root, word, old)
      if (old.isEmpty || event("replays") || event("search_restarts")) {
        observeMain(root, word)
      }
      if (oldMode.contains("scan") && mode == "copy") {
        observeMove(root, word)
      }
      if (event("replays")) {
        observeReplayStart(root)
      }
      if (replay.isDefined && mode == "scan" && !labelBoolean(root.label("g.replaying"))) {
        observeReplayReturn(root)
      }
      if (event("chain_shifts")) {
        observeShift(root)
      }
      if (oldMode.contains("shift") && mode == "scan") {
        observeShiftReturn(root, word)
      }
      result.output.foreach(output => observeOutput(source, root, word, output))
      previous = Some(root)
    }
  }
}
