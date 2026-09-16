package pal

import Scavm.{Label, Node, VM}
import ScavmStructs.{Builder, CounterView}
import ScaffoldInput.ReadonlyHead
import ScaffoldProgram.{ProgramView, TapeView}
import FppFinite.{END, LEFT, Program}
import FppSubroutine.SOURCE
import DpFinite.LOWER

/** Match-paced doubling DP search on persistent scaffold state.
  *
  * Each step performs bounded local work, including at most one instruction of
  * the finite FPP/DP table. Missed non-final stages wait until the match radius is
  * ell/4 before preparing the next window of radius 2*ell. All lengths and the
  * remaining distance to that barrier are unary stacks, never host coordinates.
  *
  * This is a scheduler component, not the completed Galil PAL controller. The
  * caller must provide a sufficiently slow match clock and the main(C,r) entry
  * conditions. A missed stage deadline is rejected, not hidden by an offline
  * drain. No claim that a particular clock suffices for all words is made here.
  * The window walker and center are readonly InputHead-compatible views; callers
  * must distribute arrivals to both and finalize both on every scaffold tick.
  *
  * Python 原典: `scaffold_search.py`（`SCA_ONLINE_CONTROL.md` "Match-paced doubling
  * search" に debt 不変条件の説明がある）。Python の `finalize` は `finish`、`final` は
  * Scala の予約語なので `finalStage`。
  */
object ScaffoldSearch {

  /** Python `alias(target, source)`: make `target` an O(1) alias of `source`'s chains. */
  def alias(target: CounterView, source: CounterView): Unit = {
    target.pos.copyFrom(source.pos)
    target.neg.copyFrom(source.neg)
  }

  /** The scheduler state, stored in the label `sp.mode` as its Python string. */
  enum Mode(val label: String) {
    case Idle extends Mode("idle")
    case Grow extends Mode("grow")
    case Lower extends Mode("lower")
    case LowerHome extends Mode("lower_home")
    case Copy extends Mode("copy")
    case Home extends Mode("home")
    case Run extends Mode("run")
    case Wait extends Mode("wait")
    case Double extends Mode("double")
    case Found extends Mode("found")
    case Missed extends Mode("missed")

    /** Python `mode in ("idle", "found", "missed")`: no search is active. */
    def inactive: Boolean = this == Mode.Idle || this == Mode.Found || this == Mode.Missed
  }

  object Mode {
    def fromLabel(label: Label): Mode = {
      val s = label.asStr
      values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown search mode '$s'"))
    }
  }

  /** The paced search over a fixed DP program, a readonly center head, a separate
    * walker and a normalized unary match-radius counter (all owned by the caller).
    *
    * @param kernel the DP table (`dp_finite.build_dp_program`)
    * @param radius the caller's unary match radius; `advanceMatch` increments it
    */
  final class SearchView[H <: ReadonlyHead[H]](
      val vm: VM,
      previous: Option[Node],
      val builder: Builder,
      kernel: Program,
      val center: H,
      val walker: H,
      val radius: CounterView
  ) {

    val program: ProgramView = new ProgramView(vm, previous, builder, kernel, name = "dp")

    val lower: CounterView = new CounterView(vm, previous, builder, "sp.lo")
    val span: CounterView = new CounterView(vm, previous, builder, "sp.span")
    val work: CounterView = new CounterView(vm, previous, builder, "sp.work")
    val debt: CounterView = new CounterView(vm, previous, builder, "sp.debt")

    var mode: Mode = previous.fold(Mode.Idle)(p => Mode.fromLabel(vm.label(p)("sp.mode")))

    /** Python `final`: the copied window reached the input origin, so no larger one exists. */
    var finalStage: Boolean = previous.fold(false)(p => vm.label(p)("sp.final").asBool)

    /** Finite phase counter for the division by four while doubling. */
    var quarter: Int = previous.fold(0)(p => vm.label(p)("sp.quarter").asInt)

    private def sourceTape: TapeView = program.tapes(SOURCE)

    private def lowerTape: TapeView = program.tapes(LOWER)

    /** Enter the first stage with the unary lower bound `lowerBound` (Galil's main(C,r)). */
    def start(lowerBound: CounterView): Unit = {
      if (lowerBound.sign < 0 || radius.sign < 0) {
        throw new IllegalArgumentException("nonnegative lower bound and match radius required")
      }
      if (center.read().isEmpty) {
        throw new IllegalArgumentException("center must be a real input place")
      }
      program.reset()
      alias(lower, lowerBound)
      alias(work, lowerBound)
      if (work.sign == 0) {
        work.inc()
      }
      span.reset()
      // Begin at -radius. Grow adds 2*max(r,1), while concurrent match
      // events subtract one; the normalized signed counter stays exact.
      debt.pos.copyFrom(radius.neg)
      debt.neg.copyFrom(radius.pos)
      mode = Mode.Grow
      finalStage = false
      quarter = 0
    }

    /** Account for one matched place, once per caller's finite clock event. */
    def advanceMatch(): Unit = {
      if (mode.inactive) {
        throw new IllegalArgumentException("no active search")
      }
      radius.inc()
      debt.dec()
    }

    /** Python `_prepare`: reset the DP scratch and begin writing LOWER for a new window. */
    private def prepareWindow(): Unit = {
      program.reset()
      walker.copyFrom(center)
      alias(work, lower)
      val tape = lowerTape
      tape.write(LEFT)
      tape.move(1)
      mode = Mode.Lower
      finalStage = false
    }

    /** Python `_double`: consume the old span to build one of twice the radius. */
    private def doubleWindow(): Unit = {
      alias(work, span)
      span.reset()
      quarter = 0
      mode = Mode.Double
    }

    /** One bounded local step of the scheduler. */
    def step(): Unit = {
      mode match {
        case Mode.Grow => stepGrow()
        case Mode.Lower => stepLower()
        case Mode.LowerHome => stepLowerHome()
        case Mode.Copy => stepCopy()
        case Mode.Home => stepHome()
        case Mode.Run => stepRun()
        case Mode.Wait => stepWait()
        case Mode.Double => stepDouble()
        case Mode.Idle | Mode.Found | Mode.Missed => ()
      }
    }

    /** Each unit of max(r,1) adds eight span cells and two debt cells. */
    private def stepGrow(): Unit = {
      if (work.sign > 0) {
        work.dec()
        for (_ <- 0 until 8) {
          span.inc()
        }
        for (_ <- 0 until 2) {
          debt.inc()
        }
      } else {
        prepareWindow()
      }
    }

    /** Write the unary lower bound `^1^r$` on LOWER. */
    private def stepLower(): Unit = {
      val lower = lowerTape
      if (work.sign > 0) {
        lower.write("1")
        lower.move(1)
        work.dec()
      } else {
        lower.write(END)
        mode = Mode.LowerHome
      }
    }

    /** Return LOWER to its origin, then open SOURCE with `^` and count the span plus the center. */
    private def stepLowerHome(): Unit = {
      val lower = lowerTape
      if (lower.read() == LEFT) {
        val source = sourceTape
        source.write(LEFT)
        source.move(1)
        alias(work, span)
        work.inc() // include the center itself
        mode = Mode.Copy
      } else {
        lower.move(-1)
      }
    }

    /** Copy the window leftwards from the center onto SOURCE, stopping at the origin. */
    private def stepCopy(): Unit = {
      val source = sourceTape
      val symbol = walker.read()
      if (symbol.isEmpty || work.sign == 0) {
        source.write(END)
        finalStage = symbol.isEmpty
        mode = Mode.Home
      } else {
        source.write(symbol.get)
        source.move(1)
        walker.left()
        work.dec()
      }
    }

    /** Return SOURCE to its origin, then start the DP table. */
    private def stepHome(): Unit = {
      val source = sourceTape
      if (source.read() == LEFT) {
        program.start()
        mode = Mode.Run
      } else {
        source.move(-1)
      }
    }

    /** One DP instruction; at the halt, decide found / missed / wait / double. */
    private def stepRun(): Unit = {
      program.step()
      if (program.done) {
        if (debt.sign < 0) {
          throw new IllegalStateException("match passed the DP stage deadline")
        }
        if (program.program.found.contains(program.pc)) {
          mode = Mode.Found
        } else if (finalStage) {
          mode = Mode.Missed
        } else if (debt.sign == 0) {
          doubleWindow()
        } else {
          mode = Mode.Wait
        }
      }
    }

    /** Wait at the barrier until the match radius reaches ell/4. */
    private def stepWait(): Unit = {
      if (debt.sign < 0) {
        throw new IllegalStateException("match passed the DP waiting barrier")
      }
      if (debt.sign == 0) {
        doubleWindow()
      }
    }

    /** Each consumed span cell yields two new ones and a quarter debt cell. */
    private def stepDouble(): Unit = {
      if (work.sign > 0) {
        work.dec()
        span.inc()
        span.inc()
        quarter = (quarter + 1) % 4
        if (quarter == 0) {
          debt.inc()
        }
      } else {
        prepareWindow()
      }
    }

    def finish(): Unit = {
      program.finish()
      for (counter <- Seq(lower, span, work, debt)) {
        counter.finish()
      }
      builder.label("sp.mode") = mode.label
      builder.label("sp.final") = finalStage
      builder.label("sp.quarter") = quarter
    }
  }
}
