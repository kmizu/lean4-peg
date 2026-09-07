package pal

import scala.collection.immutable.VectorMap

import Expr.{TRUE, FALSE}
import ScaffoldCircuit.{conjunction, disjunction, neg, choose}
import Ref.{EMPTY, PREVIOUS}

/** Clonable stream heads using the explicitly scheduled queue kernel.
  *
  * A right move consumes a front cell at an operation boundary and requests
  * three subsequent maintenance instructions if it used a queue. The caller
  * must schedule those before another public operation on that queue.
  *
  * Port of `scaffold_stream_heads.py`. Every `finalize()` is `commit()`.
  */
final class StreamBank(val circuit: Circuit, names: Seq[String]) {
  val cells: StackPool = new StackPool(circuit, Vector("cells" -> 1))
  val queues: QueueRegisters = new QueueRegisters(circuit, names.map(_ + ".in"))
  val heads: VectorMap[String, StreamHead] = VectorMap.from(names.map(name => name -> new StreamHead(this, name)))

  def commit(): Unit = {
    for (head <- heads.values) { head.commit() }
    queues.commit()
  }
}

/** A head over a stream of cells: a focus cell, a left stack, a right stack and an incoming queue. */
final class StreamHead(bank: StreamBank, val name: String) {
  val circuit: Circuit = bank.circuit
  val focusKey: String = name + ".focus"
  var focus: Ref = circuit.getRef(PREVIOUS, focusKey)
  val left: Stack = new Stack(bank.cells, name + ".l", Some("cells"))
  val right: Stack = new Stack(bank.cells, name + ".r", Some("cells"))
  val queue: Queue = bank.queues.queues(name + ".in")

  def canRight(): Expr = disjunction(neg(right.empty()), neg(queue.empty()))

  def peekRight(enabled: Expr = TRUE): Ref = {
    val fromStack = neg(right.empty())
    val (a, _) = right.peek()
    val (b, _) = queue.stacks("F").peek()
    circuit.require(neg(queue.stacks("F").empty()),
                    conjunction(enabled, neg(fromStack), neg(queue.empty())))
    Ref.select(fromStack, a, b)
  }

  /** Move right; returns the guard under which the queue needs maintenance afterwards. */
  def moveRight(enabled: Expr): Expr = {
    circuit.require(canRight(), enabled)
    left.push(focus, enabled = enabled, slot = Some(0))
    val fromStack = neg(right.empty())
    val (a, _) = right.pop(conjunction(enabled, fromStack))
    val maintain = conjunction(enabled, neg(fromStack))
    val b = queue.pop(maintain)
    focus = Ref.select(enabled, Ref.select(fromStack, a, b), focus)
    maintain
  }

  def moveLeft(enabled: Expr): Unit = {
    circuit.require(neg(left.empty()), enabled)
    right.push(focus, enabled = enabled, slot = Some(0))
    val (value, _) = left.pop(enabled)
    focus = Ref.select(enabled, value, focus)
  }

  /** The global end head advances to a newly arrived cell directly. */
  def followArrival(cell: Ref, enabled: Expr): Unit = {
    left.push(focus, enabled = enabled, slot = Some(0))
    focus = Ref.select(enabled, cell, focus)
  }

  def copyFrom(other: StreamHead, enabled: Expr): Unit = {
    focus = Ref.select(enabled, other.focus, focus)
    left.copyFrom(other.left, enabled)
    right.copyFrom(other.right, enabled)
    queue.copyFrom(other.queue, enabled)
  }

  def reset(enabled: Expr): Unit = {
    focus = Ref.select(enabled, EMPTY, focus)
    left.clear(enabled)
    right.clear(enabled)
    queue.clear(enabled)
  }

  def commit(): Unit = {
    left.commit()
    right.commit()
    circuit.putRef(focusKey, focus)
  }
}

/** A head that reads a frozen pattern snapshot, then continues into live text. */
final class PatternTextHead(bank: StreamBank, val name: String) {
  val circuit: Circuit = bank.circuit
  val pattern: StreamHead = bank.heads(name + ".pattern")
  val text: StreamHead = bank.heads(name + ".text")
  val modeKey: String = name + ".text_mode"
  var textMode: Expr = circuit.get(PREVIOUS, modeKey, Vector(false, true), false).eqTo(true)

  def available(): Expr = choose(textMode, text.canRight(), pattern.focus.present())

  /** The symbol under the head, or `None` past the end. */
  def read(enabled: Expr = TRUE): Value[Any] = {
    val target = Ref.select(textMode, text.peekRight(conjunction(enabled, textMode)), pattern.focus)
    val value = circuit.get(target, "input", Vector('a', 'b'), 'a')
    Value.select[Any](target.present(), value, Value.constant(None))
  }

  def start(snapshot: StreamHead, enabled: Expr): Unit = {
    pattern.copyFrom(snapshot, enabled)
    text.reset(enabled)
    textMode = choose(enabled, neg(snapshot.focus.present()), textMode)
  }

  /** Move by one; returns the queue name and the guard requesting its maintenance. */
  def move(direction: Int, enabled: Expr): (String, Expr) = {
    val mode = textMode
    if (direction == 1) {
      pattern.moveLeft(conjunction(enabled, neg(mode)))
      val requested = text.moveRight(conjunction(enabled, mode))
      textMode = disjunction(mode, conjunction(enabled, neg(mode), neg(pattern.focus.present())))
      (text.queue.name, requested)
    } else if (direction == -1) {
      val boundary = neg(text.focus.present())
      text.moveLeft(conjunction(enabled, mode, neg(boundary)))
      val requested = pattern.moveRight(conjunction(enabled, disjunction(neg(mode), boundary)))
      textMode = conjunction(mode, neg(conjunction(enabled, mode, boundary)))
      (pattern.queue.name, requested)
    } else {
      throw new IllegalArgumentException("unit direction required")
    }
  }

  def copyFrom(other: PatternTextHead, enabled: Expr): Unit = {
    pattern.copyFrom(other.pattern, enabled)
    text.copyFrom(other.text, enabled)
    textMode = choose(enabled, other.textMode, textMode)
  }

  def commit(): Unit = {
    circuit.put(modeKey, Value.select(textMode, Value.constant(true), Value.constant(false)))
  }
}

/** A frozen forward or backward view, preserved by head copies. */
final class OrientedHead(bank: StreamBank, val name: String) {
  val circuit: Circuit = bank.circuit
  val cursor: StreamHead = bank.heads(name)
  val modeKey: String = name + ".reverse"
  var reverse: Expr = circuit.get(PREVIOUS, modeKey, Vector(false, true), false).eqTo(true)

  def start(snapshot: StreamHead, reversed: Boolean, enabled: Expr): Unit = {
    cursor.copyFrom(snapshot, enabled)
    reverse = choose(enabled, if (reversed) { TRUE } else { FALSE }, reverse)
  }

  def read(enabled: Expr = TRUE): Value[Any] = {
    val forward = cursor.peekRight(conjunction(enabled, neg(reverse)))
    val target = Ref.select(reverse, cursor.focus, forward)
    val value = circuit.get(target, "input", Vector('a', 'b'), 'a')
    Value.select[Any](target.present(), value, Value.constant(None))
  }

  def move(direction: Int, enabled: Expr): (String, Expr) = {
    if (direction != -1 && direction != 1) { throw new IllegalArgumentException("unit oriented movement required") }
    val right = conjunction(enabled, if (direction == 1) { neg(reverse) } else { reverse })
    val left = conjunction(enabled, if (direction == 1) { reverse } else { neg(reverse) })
    val requested = cursor.moveRight(right)
    cursor.moveLeft(left)
    (cursor.queue.name, requested)
  }

  def copyFrom(other: OrientedHead, enabled: Expr): Unit = {
    cursor.copyFrom(other.cursor, enabled)
    reverse = choose(enabled, other.reverse, reverse)
  }

  def commit(): Unit = {
    circuit.put(modeKey, Value.select(reverse, Value.constant(true), Value.constant(false)))
  }
}

/** A frozen view of u # reverse(u), without building that word. */
final class MirrorHead(bank: StreamBank, val name: String) {
  val circuit: Circuit = bank.circuit
  val forward: StreamHead = bank.heads(name + ".forward")
  val reverse: StreamHead = bank.heads(name + ".reverse")
  val phaseKey: String = name + ".view_phase"
  val nonemptyKey: String = name + ".nonempty"
  var phase: Value[String] = circuit.get(PREVIOUS, phaseKey, Vector("forward", "separator", "reverse", "end"), "separator")
  var nonempty: Expr = circuit.get(PREVIOUS, nonemptyKey, Vector(false, true), false).eqTo(true)

  def start(begin: StreamHead, end: StreamHead, atEnd: Boolean, enabled: Expr): Unit = {
    forward.copyFrom(if (atEnd) { end } else { begin }, enabled)
    reverse.copyFrom(if (atEnd) { begin } else { end }, enabled)
    nonempty = choose(enabled, end.focus.present(), nonempty)
    val next = if (atEnd) {
      Value.constant("end")
    } else {
      Value.select(end.focus.present(), Value.constant("forward"), Value.constant("separator"))
    }
    phase = Value.select(enabled, next, phase)
  }

  /** The viewed symbol: `#` at the separator, `None` at the end. */
  def read(enabled: Expr = TRUE): Value[Any] = {
    val front = forward.peekRight(conjunction(enabled, phase.eqTo("forward")))
    val target = Ref.select(phase.eqTo("forward"), front, reverse.focus)
    val value = circuit.get(target, "input", Vector('a', 'b'), 'a')
    val data = Value.select[Any](target.present(), value, Value.constant(None))
    Value.select[Any](phase.eqTo("separator"), Value.constant('#'),
                      Value.select[Any](phase.eqTo("end"), Value.constant(None), data))
  }

  def move(direction: Int, enabled: Expr): (String, Expr) = {
    val current = phase
    val forwardPhase = conjunction(enabled, current.eqTo("forward"))
    val separator = conjunction(enabled, current.eqTo("separator"))
    val reversePhase = conjunction(enabled, current.eqTo("reverse"))
    val end = conjunction(enabled, current.eqTo("end"))
    if (direction == 1) {
      circuit.require(FALSE, end)
      val requested = forward.moveRight(forwardPhase)
      reverse.moveLeft(reversePhase)
      phase = Value.select(conjunction(forwardPhase, neg(forward.canRight())), Value.constant("separator"), phase)
      phase = Value.select(separator, Value.select(nonempty, Value.constant("reverse"), Value.constant("end")), phase)
      phase = Value.select(conjunction(reversePhase, neg(reverse.focus.present())), Value.constant("end"), phase)
      (forward.queue.name, requested)
    } else if (direction == -1) {
      circuit.require(nonempty, separator)
      val atFirstReverse = neg(reverse.canRight())
      forward.moveLeft(disjunction(forwardPhase, separator))
      val requested = reverse.moveRight(disjunction(conjunction(reversePhase, neg(atFirstReverse)),
                                                    conjunction(end, nonempty)))
      phase = Value.select(separator, Value.constant("forward"), phase)
      phase = Value.select(conjunction(reversePhase, atFirstReverse), Value.constant("separator"), phase)
      phase = Value.select(end, Value.select(nonempty, Value.constant("reverse"), Value.constant("separator")), phase)
      (reverse.queue.name, requested)
    } else {
      throw new IllegalArgumentException("unit direction required")
    }
  }

  def copyFrom(other: MirrorHead, enabled: Expr): Unit = {
    forward.copyFrom(other.forward, enabled)
    reverse.copyFrom(other.reverse, enabled)
    phase = Value.select(enabled, other.phase, phase)
    nonempty = choose(enabled, other.nonempty, nonempty)
  }

  def commit(): Unit = {
    circuit.put(phaseKey, phase)
    circuit.put(nonemptyKey, Value.select(nonempty, Value.constant(true), Value.constant(false)))
  }
}
