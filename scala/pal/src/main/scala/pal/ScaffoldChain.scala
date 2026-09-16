package pal

import Scavm.{Label, Node, VM}
import ScavmStructs.{Builder, CounterView}
import ScaffoldInput.ReadonlyHead
import ScaffoldProgram.TapeView
import ScaffoldSearch.alias
import FppFinite.LEFT

/** Persistent semiperiod prediction driven by the real DP unary answer.
  *
  * The input walker copies C..C-h locally. A private tape then bounces between
  * its marked ends; a separate readonly verifier catches up with the already
  * matched radius. No coordinates, head identity tests, or numeric h are used.
  * The caller owns center shifts and must update the relative counters with
  * shift_one() for each real place moved by its center.
  *
  * Python 原典: `scaffold_chain.py`（`SCA_GALIL.md` "Implemented transitions"）。
  * Python の `finalize` は `finish`。
  */
object ScaffoldChain {

  /** The chain state, stored in the label `ch.mode` as its Python string. */
  enum Mode(val label: String) {
    case Idle extends Mode("idle")
    case Copy extends Mode("copy")
    case Back extends Mode("back")
    case Watch extends Mode("watch")
    case Broken extends Mode("broken")
  }

  object Mode {
    def fromLabel(label: Label): Mode = {
      val s = label.asStr
      values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown chain mode '$s'"))
    }
  }

  /** The period tape token marking the first copied place (the center). */
  val FRONT_MARK: String = "F:"

  /** The period tape token marking the last copied place (C-h). */
  val TAIL_MARK: String = "T:"

  /** The chain view: a private period tape and seven unary counters, over a
    * readonly center, a walker that copies the semiperiod and a verifier that
    * catches up with the matched radius (all owned by the caller).
    */
  final class ChainView[H <: ReadonlyHead[H]](
      val vm: VM,
      previous: Option[Node],
      val builder: Builder,
      val center: H,
      val walker: H,
      val verifier: H,
      val radius: CounterView
  ) {

    val period: TapeView = new TapeView(vm, previous, builder, "ch.p")

    /** The unary semiperiod copied from the DP answer. */
    val h: CounterView = new CounterView(vm, previous, builder, "ch.h")
    /** How far the verifier lags behind the matched radius. */
    val lag: CounterView = new CounterView(vm, previous, builder, "ch.lag")
    val distance: CounterView = new CounterView(vm, previous, builder, "ch.dist")
    val boundary: CounterView = new CounterView(vm, previous, builder, "ch.bound")
    /** The previous semiperiod boundary: the DP lower bound after a break. */
    val last: CounterView = new CounterView(vm, previous, builder, "ch.last")
    val margin: CounterView = new CounterView(vm, previous, builder, "ch.margin")
    /** The unary 2h countdown of the two-semiperiod continuation. */
    val cycle: CounterView = new CounterView(vm, previous, builder, "ch.cycle")

    var mode: Mode = previous.fold(Mode.Idle)(p => Mode.fromLabel(vm.label(p)("ch.mode")))
    var direction: Int = previous.fold(1)(p => vm.label(p)("ch.dir").asInt)
    var phase: Int = previous.fold(0)(p => vm.label(p)("ch.phase").asInt)
    var periodOnly: Boolean = previous.fold(false)(p => vm.label(p)("ch.only").asBool)

    /** Begin copying the semiperiod at the current center (after a DP `found`). */
    def start(): Unit = {
      period.reset()
      val symbol = center.read().getOrElse(throw new IllegalStateException("chain start requires a real center place"))
      period.write(FRONT_MARK + symbol)
      walker.copyFrom(center)
      verifier.copyFrom(center)
      h.reset()
      distance.reset()
      boundary.reset()
      last.reset()
      cycle.reset()
      periodOnly = false
      alias(lag, radius)
      alias(margin, radius)
      mode = Mode.Copy
      direction = 1
      phase = 0
    }

    /** The predicted next symbol, once the verifier has caught up in `watch`. */
    def prediction(): Option[String] = {
      if (mode != Mode.Watch || lag.sign != 0) {
        None
      } else {
        Some(period.read().takeRight(1))
      }
    }

    /** Whether four verified semiperiods permit a chain shift now. */
    def canShift: Boolean = {
      val ready = mode == Mode.Watch && lag.sign == 0 && phase == 4
      ready && (if (periodOnly) { cycleEnd } else { margin.sign >= 0 })
    }

    /** The continuation countdown holds exactly one cell. */
    def cycleEnd: Boolean = cycle.sign > 0 && cycle.pos.belowOfTop.isEmpty

    /** Check the two-semiperiod continuation invariant against real input. */
    def checkPair(left: Option[String]): Unit = {
      if (periodOnly && mode == Mode.Watch && lag.sign == 0) {
        if (cycle.sign <= 0) {
          throw new AssertionError("chain continuation exhausted without dispatch")
        }
        val same = left == prediction()
        if (same == cycleEnd) {
          throw new AssertionError("left head contradicts the two-semiperiod continuation")
        }
      }
    }

    /** Enter the two-semiperiod continuation after a shift decision. */
    def beginShift(): Unit = {
      periodOnly = true
      cycle.reset()
    }

    /** Python `_consume`: verify one place against the period tape; `false` breaks the chain. */
    private def consume(): Boolean = {
      verifier.right()
      val token = period.read()
      if (!verifier.read().contains(token.takeRight(1))) {
        mode = Mode.Broken
        false
      } else {
        distance.inc()
        if (token.startsWith(FRONT_MARK) || token.startsWith(TAIL_MARK)) {
          alias(last, boundary)
          alias(boundary, distance)
          phase = math.min(4, phase + 1)
          direction = if (token.startsWith(FRONT_MARK)) { 1 } else { -1 }
        }
        period.move(direction)
        true
      }
    }

    /** One new place has joined the matched interval (also on a chain shift). */
    def matched(): Unit = {
      margin.inc()
      if (periodOnly) {
        cycle.dec()
      }
      if (mode == Mode.Watch && lag.sign == 0) {
        consume()
      } else {
        lag.inc()
      }
    }

    /** The caller moved its center by one real place. */
    def shiftOne(): Unit = {
      for (counter <- Seq(distance, boundary, last, margin)) {
        counter.dec()
      }
      cycle.inc()
      cycle.inc()
    }

    /** One bounded local step, reading the DP unary answer tape `answer`. */
    def step(answer: TapeView): Unit = {
      mode match {
        case Mode.Copy => stepCopy(answer)
        case Mode.Back => stepBack()
        case Mode.Watch if lag.sign > 0 =>
          if (consume()) {
            lag.dec()
          }
        case Mode.Idle | Mode.Watch | Mode.Broken => ()
      }
    }

    /** Consume the unary DP answer while copying C-1, C-2, ... onto the period tape. */
    private def stepCopy(answer: TapeView): Unit = {
      if (answer.read() == "1") {
        answer.move(-1)
        h.inc()
        for (_ <- 0 until 4) {
          margin.dec()
        }
        walker.left()
        val symbol = walker.read().getOrElse(throw new IllegalArgumentException("DP answer crosses the input origin"))
        period.move(1)
        period.write(symbol)
      } else if (answer.read() == LEFT && h.sign > 0) {
        period.write(TAIL_MARK + period.read())
        mode = Mode.Back
      } else {
        throw new IllegalArgumentException("positive unary DP answer required")
      }
    }

    /** Return the period tape to its front mark, then watch. */
    private def stepBack(): Unit = {
      if (period.read().startsWith(FRONT_MARK)) {
        period.move(1)
        mode = Mode.Watch
      } else {
        period.move(-1)
      }
    }

    def finish(): Unit = {
      period.finish()
      for (counter <- Seq(h, lag, distance, boundary, last, margin, cycle)) {
        counter.finish()
      }
      builder.label("ch.mode") = mode.label
      builder.label("ch.dir") = direction
      builder.label("ch.phase") = phase
      builder.label("ch.only") = periodOnly
    }
  }
}
