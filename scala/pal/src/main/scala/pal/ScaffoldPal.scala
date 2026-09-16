package pal

import scala.collection.mutable

import Scavm.{Label, Self, Stats, VM}
import ScavmStructs.{Builder, CounterView, emit}
import ScaffoldInput.InputHead
import ScaffoldProgram.{ProgramView, TapeView}
import FppFinite.{BLANK, END, LEFT, Program}
import FppSubroutine.{buildMarkedProgram, MARKS, SOURCE}
import FppReuse.makeReusable

/** Whole online PAL control on the scaffold with a finite FPP fallback.
  *
  * This connects matching, input head copies, source preparation, actual finite
  * FPP execution, candidate selection, repositioning and physical scratch reset.
  * No host coordinates, KMP arrays or node-identity tests enter the controller.
  *
  * The chain optimization and Galil's real-time schedule are NOT implemented.
  * budget=None runs each arrival to completion and establishes online correctness;
  * a fixed budget creates exactly that many scaffold nodes per arrival but can
  * miss palindromes while behind. Thus this is not yet a PAL PEG or real-time PAL
  * recognizer. Its bounded instruction path is the integration target for chains.
  *
  * Python 原典: `scaffold_pal.py`（`SCA_ONLINE_CONTROL.md` "Executable whole-prefix
  * baseline"）。
  */
object ScaffoldPal {

  /** The MARKS token written at the mark of the new character itself. */
  val FIRST: String = "first:1"

  /** Python `copy_counter(target, source)`: alias the counter's chains (as `ScaffoldSearch.alias`). */
  def copyCounter(target: CounterView, source: CounterView): Unit = {
    target.pos.copyFrom(source.pos)
    target.neg.copyFrom(source.neg)
  }

  /** Whether `head` is at the first input character (its left stack holds only the origin). */
  def firstCharacter(head: InputHead): Boolean = !head.leftStack.empty && head.leftStack.peek.isEmpty

  /** The controller mode, stored in the label `mode` as its Python string. */
  enum Mode(val label: String) {
    case Idle extends Mode("idle")
    case Match extends Mode("match")
    case Copy extends Mode("copy")
    case SourceHome extends Mode("source_home")
    case Fpp extends Mode("fpp")
    case MarkFirst extends Mode("mark_first")
    case MarksEnd extends Mode("marks_end")
    case Choose extends Mode("choose")
    case RewindChoice extends Mode("rewind_choice")
    case Cleanup extends Mode("cleanup")
    case ClearBegin extends Mode("clear_begin")
    case Clear extends Mode("clear")
    case ClearBack extends Mode("clear_back")
  }

  object Mode {
    def fromLabel(label: Label): Mode = {
      val s = label.asStr
      values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown controller mode '$s'"))
    }
  }

  /** The result of [[run]] (Python's `outputs, {**vm.stats(), "max_microsteps": ..,
    * "fpp_calls": .., "costs": ..}`).
    */
  final case class PalRun(outputs: Vector[Int], stats: Stats, maxMicrosteps: Int, fppCalls: Int, costs: Vector[Int]) {

    /** The Python stats dict, in its key order. */
    def pythonRepr: String = {
      s"{'steps': ${stats.steps}, 'radius': ${stats.radius}, 'fields': ${stats.fields}, 'labels': ${stats.labels}, " +
        s"'max_microsteps': $maxMicrosteps, 'fpp_calls': $fppCalls, 'costs': ${costs.mkString("[", ", ", "]")}}"
    }
  }

  /** The working set of one scaffold microstep (the body of Python `run`'s inner
    * loop): three input heads, the reusable FPP program, two counters and the
    * finite control fields, over the previous top. Field initialisation order is
    * the Python statement order.
    */
  private final class Tick(vm: VM, arrival: String, first: Boolean, kernel: Program) {
    vm.begin()
    private val b = new Builder
    b.label("input") = arrival

    private val right = new InputHead(vm, vm.top, b, "R")
    private val left = new InputHead(vm, vm.top, b, "L")
    private val window = new InputHead(vm, vm.top, b, "W")
    private val heads = Vector(right, left, window)
    if (first) {
      for (head <- heads) {
        head.append(Self)
      }
    }

    private val state = new ProgramView(vm, vm.top, b, kernel)
    private val length = new CounterView(vm, vm.top, b, "length")
    private val remaining = new CounterView(vm, vm.top, b, "remain")

    private var mode: Mode = vm.top.fold(Mode.Idle)(top => Mode.fromLabel(vm.label(top)("mode")))
    private var initialized: Boolean = vm.top.fold(false)(top => vm.label(top)("initialized").asBool)
    private var output: Boolean = vm.top.fold(false)(top => vm.label(top)("output").asBool)

    private val source: TapeView = state.tapes(SOURCE)
    private val marks: TapeView = state.tapes(MARKS)

    /** Whether this microstep started the finite FPP table (an observer count only). */
    var fppStarted: Boolean = false

    /** Run the microstep and emit its node; returns `(report, caught)`. */
    def run(): (Int, Boolean) = {
      mode match {
        case Mode.Idle => stepIdle()
        case Mode.Match => stepMatch()
        case Mode.Copy => stepCopy()
        case Mode.SourceHome => stepSourceHome()
        case Mode.Fpp => stepProgram(Mode.MarkFirst)
        case Mode.MarkFirst => stepMarkFirst()
        case Mode.MarksEnd => stepMarksEnd()
        case Mode.Choose => stepChoose()
        case Mode.RewindChoice => stepRewindChoice()
        case Mode.Cleanup => stepProgram(Mode.ClearBegin)
        case Mode.ClearBegin =>
          source.move(1)
          mode = Mode.Clear
        case Mode.Clear => stepClear()
        case Mode.ClearBack => stepClearBack()
      }
      val caught = mode == Mode.Idle && !right.canRight
      val report = if (caught && output) { 1 } else { 0 }
      finish()
      (report, caught)
    }

    /** Take the next input character; the very first one is a palindrome by itself. */
    private def stepIdle(): Unit = {
      if (right.canRight) {
        right.right()
        if (!initialized) {
          left.copyFrom(right)
          length.inc()
          initialized = true
          output = true
        } else {
          mode = Mode.Match
        }
      }
    }

    /** Extend the longest palindromic suffix by two, or prepare the FPP fallback window. */
    private def stepMatch(): Unit = {
      left.left()
      if (left.read() == right.read()) {
        length.inc()
        length.inc()
        output = firstCharacter(left)
        mode = Mode.Idle
      } else {
        window.copyFrom(right)
        copyCounter(remaining, length)
        remaining.inc()
        source.write(LEFT)
        source.move(1)
        mode = Mode.Copy
      }
    }

    /** Copy the reversal of `(old suffix) + (new character)` onto SOURCE. */
    private def stepCopy(): Unit = {
      if (remaining.sign > 0) {
        source.write(window.read().getOrElse(throw new IllegalStateException("fallback window crossed the input origin")))
        source.move(1)
        window.left()
        remaining.dec()
      } else {
        source.write(END)
        mode = Mode.SourceHome
      }
    }

    private def stepSourceHome(): Unit = {
      if (source.read() == LEFT) {
        state.start()
        fppStarted = true // observer only; never consulted by the controller
        mode = Mode.Fpp
      } else {
        source.move(-1)
      }
    }

    /** One instruction of the finite table; `next` when it halts. */
    private def stepProgram(next: Mode): Unit = {
      state.step()
      if (state.done) {
        mode = next
      }
    }

    private def stepMarkFirst(): Unit = {
      marks.move(1)
      marks.write(FIRST)
      marks.move(1)
      mode = Mode.MarksEnd
    }

    private def stepMarksEnd(): Unit = {
      if (marks.read() == END) {
        marks.move(-1)
        mode = Mode.Choose
      } else {
        marks.move(1)
      }
    }

    /** Select the largest marked prefix of the reversed window: the new longest suffix. */
    private def stepChoose(): Unit = {
      if (marks.read() == "1" || marks.read() == FIRST) {
        left.copyFrom(right)
        length.reset()
        length.inc()
        mode = Mode.RewindChoice
      } else {
        marks.move(-1)
      }
    }

    /** Move L back to the chosen suffix, then enter the kernel's cleanup entry. */
    private def stepRewindChoice(): Unit = {
      if (marks.read() == FIRST) {
        marks.write("1")
        state.start(kernel.cleanup.getOrElse(throw new IllegalStateException("kernel has no cleanup entry")))
        mode = Mode.Cleanup
      } else {
        marks.move(-1)
        left.left()
        length.inc()
      }
    }

    /** Physically blank SOURCE beyond its origin for reuse. */
    private def stepClear(): Unit = {
      if (source.read() == BLANK) {
        source.move(-1)
        mode = Mode.ClearBack
      } else {
        source.write(BLANK)
        source.move(1)
      }
    }

    private def stepClearBack(): Unit = {
      if (source.read() == LEFT) {
        source.write(BLANK)
        output = firstCharacter(left)
        mode = Mode.Idle
      } else {
        source.move(-1)
      }
    }

    private def finish(): Unit = {
      for (head <- heads) {
        head.finish()
      }
      state.finish()
      length.finish()
      remaining.finish()
      b.label("mode") = mode.label
      b.label("initialized") = initialized
      b.label("output") = output
      emit(vm, b)
    }
  }

  /** One report per input letter: without a budget every arrival runs to completion,
    * with `budget = k` exactly k microsteps run per letter (incomplete work reports 0).
    */
  def run(word: String, budget: Option[Int] = None): PalRun = {
    if (word.exists(c => c != 'a' && c != 'b')) {
      throw new IllegalArgumentException("binary input required")
    }
    if (budget.exists(_ < 1)) {
      throw new IllegalArgumentException("positive integer budget required")
    }
    val kernel = makeReusable(buildMarkedProgram("ab"))
    val vm = new VM
    val outputs = mutable.ArrayBuffer.empty[Int]
    val costs = mutable.ArrayBuffer.empty[Int]
    var fppCalls = 0
    for (arrival <- word) {
      var microsteps = 0
      var caught = false
      var report = 0
      def more: Boolean = budget.fold(!caught)(microsteps < _)
      while (more) {
        val tick = new Tick(vm, arrival.toString, microsteps == 0, kernel)
        val (r, c) = tick.run()
        report = r
        caught = c
        if (tick.fppStarted) {
          fppCalls += 1
        }
        microsteps += 1
      }
      outputs += report
      costs += microsteps
    }
    PalRun(outputs.toVector, vm.stats, costs.maxOption.getOrElse(0), fppCalls, costs.toVector)
  }
}
