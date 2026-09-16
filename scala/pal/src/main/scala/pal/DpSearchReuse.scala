package pal

import scala.collection.mutable

import FppFinite.*
import FppFinite.Instruction.*
import FppReuse.C_ORIGIN
import DpFinite.LOWER
import DpSearchFinite.{WINDOW, STATUS, periodSymbol}

/** Cancellation/reentry for the whole offline doubling search.
  *
  * One extra unary tape tracks WINDOW's distance from C and furthest visit.
  * Finite cancellation entries finish a half-completed paired move before
  * cleanup. Cancel any normal instruction, including internal kernel cleanup,
  * but not the outer cleanup itself. WINDOW/LOWER survive; all scratch clears.
  *
  * Python 原典: `dp_search_reuse.py`。
  */
object DpSearchReuse {
  val ERASED: String = "erased:_"

  /** What a paired WINDOW/DISTANCE move had left undone when cancelled at that state. */
  sealed trait Pending
  object Pending {
    /** The unary distance mark write is still due. */
    case object Write extends Pending
    /** The DISTANCE head still has to move by `direction`. */
    final case class Move(direction: Int) extends Pending
  }

  /** Python の `make_cancellable(search)`。 */
  def makeCancellable(search: Program): Program = {
    if (search.ntapes < 16) {
      throw new IllegalArgumentException("expected the local doubling search or its chain monitor")
    }
    val distance = search.ntapes
    val p = new Program(search.alphabet, ntapes = search.ntapes + 1)
    p.distance = Some(distance)
    p.scalarTapes = Some(search.scalarTapes.getOrElse(Vector(STATUS)))
    val scalarTapes = p.scalarTapes.get
    p.sourceAlphabet = search.sourceAlphabet
    p.copyCodeFrom(search)
    p.found = search.found
    p.missed = search.missed
    p.outcomes ++= search.outcomes
    p.ready = search.ready
    p.confirmedReady = search.confirmedReady
    p.scratch = (0 until p.ntapes).filterNot(t => t == WINDOW || t == LOWER).toVector

    retainOriginsDuringInternalCleanup(p)
    replaceBlankWritesByTombstones(p)

    val pending = mutable.LinkedHashMap.empty[Int, Pending]
    for ((row, q) <- search.instructions.zipWithIndex) {
      row match {
        case Move(WINDOW, direction, next) =>
          var k = next
          if (direction == -1) {
            val written = p.write(distance, "1", k)
            pending(written) = Pending.Write
            k = written
          }
          val moved = p.move(distance, -direction, k)
          pending(moved) = Pending.Move(-direction)
          p.set(q, Move(WINDOW, direction, moved))
        case _ => ()
      }
    }

    val done = p.add(Halt)
    val symbols = symbolsPerTape(p)

    def reset(tape: Int, k: Int): Int = {
      val root = if (tape == C) { C_ORIGIN } else { LEFT }
      val body = ((symbols(tape) + BLANK) - root).toVector.sorted
      val seek = p.reserve()
      val clear = p.reserve()
      val back = p.reserve()
      p.branch(tape, choices(root -> p.write(tape, BLANK, k),
        BLANK -> p.move(tape, -1, back)), back)
      p.branch(tape, choices((Seq(BLANK -> p.move(tape, -1, back)) ++ body.filter(_ != BLANK).map { s =>
        s -> p.write(tape, BLANK, p.move(tape, 1, clear))
      })*), clear)
      p.branch(tape, choices((Seq(root -> p.move(tape, 1, clear)) ++ body.map { s =>
        s -> p.move(tape, -1, seek)
      })*), seek)
      seek
    }

    var cleanScratch = done
    for (tape <- p.scratch.reverse) {
      if (scalarTapes.contains(tape)) {
        cleanScratch = p.write(tape, BLANK, cleanScratch)
      } else {
        cleanScratch = reset(tape, cleanScratch)
      }
    }
    val lower = p.reserve()
    p.branch(LOWER, choices((Seq(LEFT -> cleanScratch) ++ Seq("1", END).map { s =>
      s -> p.move(LOWER, -1, lower)
    })*), lower)

    // First return to C using the aligned distance heads. Sweep precisely
    // the already visited prefix, erasing P tags, then return to C again.
    // The retained unary extent makes marks behind the current head visible.
    val home = p.reserve()
    val scan = p.reserve()
    val restore = p.reserve()
    p.branch(distance, choices(LEFT -> lower,
      "1" -> p.move(WINDOW, 1, p.move(distance, -1, restore))), restore)
    val nextCell = p.move(distance, 1, scan)
    val unmark = p.branch(WINDOW, choices((Seq(LEFT -> nextCell) ++
      p.sourceAlphabet.map(s => s -> nextCell) ++
      p.sourceAlphabet.map(s => periodSymbol(s) -> p.write(WINDOW, s, nextCell)))*))
    p.branch(distance, choices(BLANK -> p.move(distance, -1, restore),
      "1" -> p.move(WINDOW, -1, unmark)), scan)
    p.branch(distance, choices(LEFT -> nextCell,
      "1" -> p.move(WINDOW, 1, p.move(distance, -1, home))), home)
    p.cleanup = Some(home)

    for (q <- search.code.indices) {
      p.cancelEntries(q) = home
    }
    for ((q, action) <- pending) {
      val entry = action match {
        case Pending.Write => p.write(distance, "1", home)
        case Pending.Move(1) => p.move(distance, 1, p.write(distance, "1", home))
        case Pending.Move(_) => p.move(distance, -1, home)
      }
      p.cancelEntries(q) = entry
    }

    def bootstrap(k: Int): (Int, Vector[Int]) = {
      val states = Vector.newBuilder[Int]
      var next = k
      for (tape <- p.scratch.reverse) {
        val symbol =
          if (tape == STATUS) { "N" }
          else if (scalarTapes.contains(tape)) { BLANK }
          else if (tape == C) { C_ORIGIN }
          else { LEFT }
        next = p.write(tape, symbol, next)
        states += next
      }
      (next, states.result())
    }

    val (cancelBootstrap, _) = bootstrap(home)
    val (start, states) = bootstrap(search.start)
    p.start = start
    for (q <- states) {
      p.cancelEntries(q) = cancelBootstrap
    }
    p.validate()
    p
  }

  /** Retain origins during INTERNAL cleanup so a cancellation can locate
    * them even halfway through that sweep. The next kernel bootstrap
    * overwrites these same origin cells; its body still starts blank.
    */
  private def retainOriginsDuringInternalCleanup(p: Program): Unit = {
    for (q <- p.code.indices) {
      p.instruction(q) match {
        case Read(tape, choices) =>
          val root = if (tape == C) { C_ORIGIN } else { LEFT }
          for (target <- choices.get(root)) {
            p.instruction(target) match {
              case Write(`tape`, BLANK, next) => p.set(target, Write(tape, root, next))
              case _ => ()
            }
          }
        case _ => ()
      }
    }
  }

  /** Logical deletion leaves a physical tombstone. Internal left-to-right
    * cleanup can otherwise leave a blank hole before still-live cells.
    * Normal code treats the tombstone exactly as blank; outer cleanup sees
    * a dense physical prefix and sweeps through it to the true frontier.
    */
  private def replaceBlankWritesByTombstones(p: Program): Unit = {
    for ((row, q) <- p.instructions.zipWithIndex) {
      row match {
        case Write(tape, BLANK, next) => p.set(q, Write(tape, ERASED, next))
        case Read(tape, choices) if choices.contains(BLANK) =>
          p.set(q, Read(tape, choices.updated(ERASED, choices(BLANK))))
        case _ => ()
      }
    }
  }

  /** Every symbol read or written on each tape. */
  private def symbolsPerTape(p: Program): Vector[Set[String]] = {
    val symbols = Vector.fill(p.ntapes)(mutable.HashSet.empty[String])
    for (row <- p.instructions) {
      row match {
        case Read(tape, choices) => symbols(tape) ++= choices.keys
        case Write(tape, symbol, _) => symbols(tape) += symbol
        case _ => ()
      }
    }
    symbols.map(_.toSet)
  }
}
