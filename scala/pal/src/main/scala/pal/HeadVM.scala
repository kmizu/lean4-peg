package pal

import scala.collection.IndexedSeq
import scala.collection.mutable

/** Observer/interpreter for the explicit finite table and preloaded word.
  *
  * @tparam S the symbol type of the loaded view (`Char` for a plain word,
  *           `Option[Char]` for a [[PalindromeView]] with its separator)
  */
class HeadVM[S](val word: IndexedSeq[S], val program: Program) {
  import Event.*
  import GsHeads.{BLIND, HEADS, TESTS}

  /** Head coordinates, in `HEADS` order (extended by subclasses). */
  val positions: mutable.LinkedHashMap[String, Int] = mutable.LinkedHashMap.from(HEADS.map(_ -> 0))
  positions("OriginalEnd") = word.length

  var state: Int = program.start
  var steps: Int = 0
  var motion: Int = 0
  var comparisons: Int = 0
  protected val outputBuffer: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

  /** Reported `border` coordinates so far. */
  def outputs: Vector[Int] = outputBuffer.toVector

  def done: Boolean = program.code(state).event == Halt

  /** The instruction about to execute. */
  protected def current: Row = program.code(state)

  /** Execute one instruction of the table. */
  def step(): Unit = {
    if (done) {
      throw new IllegalStateException("local-head controller already halted")
    }
    val Row(event, targets) = current
    steps += 1
    val decision: Option[Boolean] = event match {
      case Move(moves) =>
        moves.foreach { case Movement(head, delta) =>
          positions(head) += delta
          motion += math.abs(delta)
          if (!BLIND.contains(head) && positions(head) < 0) {
            throw new AssertionError(("left-end crossing", head, event).toString)
          }
        }
        None
      case Copy(target, source) =>
        if (!BLIND.contains(target) && BLIND.contains(source)) {
          throw new AssertionError("cannot restore a data head from a blind coordinate")
        }
        positions(target) = positions(source)
        None
      case Equal(left, right) =>
        comparisons += 1
        Some(positions(left) == positions(right))
      case Less(left, right) =>
        comparisons += 1
        Some(positions(left) < positions(right))
      case Symbols(left, right) =>
        comparisons += 1
        Some(compareSymbols(event, left, right))
      case Border(head) =>
        // Coordinates are decoded only by the observer; control never receives
        // this output integer. A local consumer may compare the named head.
        outputBuffer += positions(head)
        None
      case _ => throw new IllegalArgumentException("unknown local-head instruction")
    }
    state = if (TESTS.contains(event.op)) targets(if (decision.get) 1 else 0) else targets(0)
  }

  private def compareSymbols(event: Event, leftHead: String, rightHead: String): Boolean = {
    val left = positions(leftHead)
    val right = positions(rightHead)
    val inRange = 0 <= left && left < word.length && 0 <= right && right < word.length
    if (BLIND.contains(leftHead) || BLIND.contains(rightHead) || !inRange) {
      throw new AssertionError(("invalid local symbol query", event, left, right, word.length).toString)
    }
    word(left) == word(right)
  }

  /** Run to `halt`; `watchdog` defaults to `10000 * (len(word) + 1)`. */
  def run(watchdog: Option[Long] = None): Vector[Int] = {
    // A test watchdog, not a semantic input cap or a real-time claim.
    val limit = watchdog.getOrElse(10000L * (word.length + 1))
    while (!done) {
      if (steps >= limit) {
        throw new IllegalStateException("local-head test watchdog exceeded")
      }
      step()
    }
    outputs
  }
}
