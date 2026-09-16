package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Scavm.{Label, Self, Stats, VM}
import ScavmStructs.{Builder, CounterView, emit}
import ScaffoldPlaces.PlaceHead
import ScaffoldProgram.{ProgramView, TapeView}
import ScaffoldSearch.{alias, SearchView}
import ScaffoldChain.ChainView
import FppFinite.{END, LEFT}
import FppSubroutine.{buildMarkedProgram, MarkedProgram, MARKS, SOURCE}
import DpFinite.{buildDpProgram, DpProgram, OUTPUT}
import GalilClock.{derive, Timing}

/** Whole online scaffold PAL experiment with DP and actual periodic shifts.
  *
  * All input positions and lengths are represented by readonly place heads and
  * unary persistent stacks. Real finite FPP instructions select odd palindromic
  * place suffixes; actual main1-style replay rebuilds search at the new center.
  * Confirmed chain predictions can move C by h and L by 2h through unit moves.
  *
  * This is still an experimental online controller, NOT a certified real-time
  * PAL machine or a PEG. Two-semiperiod continuation has an explicit unary
  * countdown and checks the left-head/prediction invariant. The global
  * predictability/work proof and SCA-to-PEG output remain outstanding.
  * Default execution drains each arrival; a supplied budget can miss positives.
  *
  * OnlineGalil exposes separate output and input-ready events. Its internal
  * trailing-gap work does not require another external input character. The
  * legacy step/run interfaces remain available for the earlier circuit fixtures.
  *
  * Python 原典: `scaffold_galil.py`。遷移の説明と証明義務は `SCA_GALIL.md`、
  * 時計定数は `GalilClock`（`galil_clock.py`）。
  */
object ScaffoldGalil {

  val FPP_QUANTUM: Int = 64
  val DEFAULT_TIMING: Timing = derive(FPP_QUANTUM)
  val MATCH_DELAY: Int = DEFAULT_TIMING.matchDelay
  val REALTIME_BUDGET: Int = 2048

  /** The MARKS token written after the FPP run at the mark of the new place itself. */
  val FIRST: String = "first:1"

  /** The two finite kernels over the place alphabet `abs`. */
  final case class Kernels(fpp: MarkedProgram, dp: DpProgram)

  object Kernels {
    /** Python `build_marked_program("abs"), build_dp_program("abs")`. */
    def default: Kernels = Kernels(buildMarkedProgram("abs"), buildDpProgram("abs"))
  }

  /** Diagnostic event counts of one transition (Python's `events` dict). They do
    * not control execution.
    */
  final case class Events(fppCalls: Int = 0, chainShifts: Int = 0, searchRestarts: Int = 0, replays: Int = 0) {

    def +(that: Events): Events = Events(
      fppCalls + that.fppCalls,
      chainShifts + that.chainShifts,
      searchRestarts + that.searchRestarts,
      replays + that.replays
    )

    /** Python `events[name]`. */
    def apply(name: String): Int = toMap(name)

    /** The Python dict, in its key order. */
    def toMap: VectorMap[String, Int] = VectorMap(
      "fpp_calls" -> fppCalls,
      "chain_shifts" -> chainShifts,
      "search_restarts" -> searchRestarts,
      "replays" -> replays
    )
  }

  object Events {
    val NAMES: Vector[String] = Vector("fpp_calls", "chain_shifts", "search_restarts", "replays")
  }

  /** The controller mode, stored in the label `g.mode` as its Python string. */
  enum Mode(val label: String) {
    case Init extends Mode("init")
    case Scan extends Mode("scan")
    case Shift extends Mode("shift")
    case Copy extends Mode("copy")
    case Home extends Mode("home")
    case Fpp extends Mode("fpp")
    case MarkEnd extends Mode("mark_end")
    case Choose extends Mode("choose")
    case Rewind extends Mode("rewind")
    case ReplayStart extends Mode("replay_start")
  }

  object Mode {
    def fromLabel(label: Label): Mode = {
      val s = label.asStr
      values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown controller mode '$s'"))
    }
  }

  /** The result of one local operation (Python `_transition`'s tuple).
    *
    * @param report     the answer reported at this tick (`int(output)` when caught, else 0)
    * @param caught     the controller is in `scan` at a letter place with no pending input
    * @param inputReady the controller is in `scan` at a gap place with no pending input
    */
  final case class Transition(report: Int, caught: Boolean, inputReady: Boolean, events: Events)

  /** The finite control fields of the controller (labels `g.mode` .. `g.pair`). */
  private final case class Control(mode: Mode, clock: Int, output: Boolean, replaying: Boolean, odd: Boolean, pair: Int)

  private object Control {
    def initial(timing: Timing): Control = Control(Mode.Init, timing.matchDelay, false, false, false, 0)

    def load(label: Label): Control = Control(
      Mode.fromLabel(label("g.mode")),
      label("g.clock").asStr.toInt,
      label("g.out").asBool,
      label("g.replaying").asBool,
      label("g.odd").asBool,
      label("g.pair").asInt
    )
  }

  /** One local operation; gap availability is independent of external input.
    *
    * The working set of a single scaffold tick: the five place heads, the five unary
    * counters, the search, chain and FPP views over the previous top, and the finite
    * control fields. Python `_transition`, split by mode. Field initialisation order
    * is the Python statement order (it fixes the builder's field order).
    */
  private final class Tick(
      vm: VM,
      arrival: Option[String],
      newInput: Boolean,
      kernels: Kernels,
      advanceTrailingGap: Boolean,
      timing: Timing
  ) {
    private var fppCalls = 0
    private var shifts = 0
    private var restarts = 0
    private var replays = 0

    vm.begin()
    private val b = new Builder
    b.label("input") = arrival.fold[Label](Label.Null)(Label.Str(_))

    private val right = new PlaceHead(vm, vm.top, b, "R")
    private val left = new PlaceHead(vm, vm.top, b, "L")
    private val center = new PlaceHead(vm, vm.top, b, "C")
    private val walker = new PlaceHead(vm, vm.top, b, "W")
    private val verifier = new PlaceHead(vm, vm.top, b, "V")
    private val heads = Vector(right, left, center, walker, verifier)
    if (newInput) {
      for (head <- heads) {
        head.append(Self)
      }
    }

    private val length = new CounterView(vm, vm.top, b, "g.len")
    private val radius = new CounterView(vm, vm.top, b, "g.rad")
    private val remaining = new CounterView(vm, vm.top, b, "g.rem")
    private val replay = new CounterView(vm, vm.top, b, "g.replay")
    private val zero = new CounterView(vm, vm.top, b, "g.zero")
    private val counters = Vector(length, radius, remaining, replay, zero)

    private val search = new SearchView(vm, vm.top, b, kernels.dp, center, walker, radius)
    private val chain = new ChainView(vm, vm.top, b, center, walker, verifier, radius)
    private val fpp = new ProgramView(vm, vm.top, b, kernels.fpp, name = "f")
    private val source: TapeView = fpp.tapes(SOURCE)
    private val marks: TapeView = fpp.tapes(MARKS)

    private val loaded = vm.top.fold(Control.initial(timing))(top => Control.load(vm.label(top)))
    private var mode = loaded.mode
    private var clock = loaded.clock
    private var output = loaded.output
    private var replaying = loaded.replaying
    private var odd = loaded.odd
    private var pair = loaded.pair

    /** Run the tick: background work, the mode transition, then emit the node. */
    def run(): Transition = {
      if (mode == Mode.Scan) {
        background()
      }
      mode match {
        case Mode.Init => stepInit()
        case Mode.Scan => stepScan()
        case Mode.Shift => stepShift()
        case Mode.Copy => stepCopy()
        case Mode.Home => stepHome()
        case Mode.Fpp => stepFpp()
        case Mode.MarkEnd => stepMarkEnd()
        case Mode.Choose => stepChoose()
        case Mode.Rewind => stepRewind()
        case Mode.ReplayStart => stepReplayStart()
      }
      val quiescent = mode == Mode.Scan && !replaying && !right.head.canRight
      val caught = quiescent && !right.gap
      val inputReady = quiescent && right.gap
      val report = if (caught && output) { 1 } else { 0 }
      finish()
      Transition(report, caught, inputReady, Events(fppCalls, shifts, restarts, replays))
    }

    /** Background DP/chain work while scanning. The quantum is a fixed finite
      * unrolling, not a variable work drain. Only instruction execution is batched;
      * span growth runs once/tick.
      */
    private def background(): Unit = {
      if (chain.mode != ScaffoldChain.Mode.Idle) {
        chain.step(search.program.tapes(OUTPUT))
      } else if (!search.mode.inactive) {
        val quantum = if (search.mode == ScaffoldSearch.Mode.Run) { timing.quantum } else { 1 }
        var count = 0
        var running = true
        while (count < quantum && running) {
          search.step()
          running = search.mode == ScaffoldSearch.Mode.Run
          count += 1
        }
        if (search.mode == ScaffoldSearch.Mode.Found) {
          chain.start()
        }
      }
      if (chain.mode == ScaffoldChain.Mode.Broken) {
        if (chain.margin.sign >= 0 && chain.last.sign > 0 && chain.lag.sign == 0) {
          search.start(chain.last)
          chain.mode = ScaffoldChain.Mode.Idle
          restarts += 1
          clock = timing.matchDelay
        } else {
          throw new AssertionError("chain restart violates the confirmed-period invariant")
        }
      }
    }

    /** The first letter: all heads at place 1, the search started with lower bound 0. */
    private def stepInit(): Unit = {
      right.right()
      left.copyFrom(right)
      center.copyFrom(right)
      length.inc()
      search.start(zero)
      mode = Mode.Scan
      output = true
    }

    /** Ordinary matching: one place comparison every `matchDelay` ticks. */
    private def stepScan(): Unit = {
      val available = replaying || (if (advanceTrailingGap) { right.canRight } else { right.head.canRight })
      if (available) {
        clock -= 1
        if (clock == 0) {
          clock = timing.matchDelay
          right.right()
          left.left()
          if (!search.mode.inactive && chain.mode == ScaffoldChain.Mode.Idle) {
            search.advanceMatch()
          } else {
            radius.inc()
          }
          chain.checkPair(left.read())
          if (left.read() == right.read()) {
            matchedPlace()
          } else if (!replaying && chain.canShift && chain.prediction() == right.read()) {
            beginChainShift()
          } else {
            beginFallback()
          }
        }
      }
    }

    /** The outer symbols agree: the palindrome grows by two places. */
    private def matchedPlace(): Unit = {
      length.inc()
      length.inc()
      if (chain.mode != ScaffoldChain.Mode.Idle) {
        chain.matched()
      }
      if (replaying) {
        replay.dec()
        if (replay.sign == 0) {
          replaying = false
        }
      }
      if (!right.gap) {
        output = left.isFirst
      }
    }

    /** A confirmed chain prediction: shift C by h and L by 2h in unit moves. */
    private def beginChainShift(): Unit = {
      chain.matched()
      chain.beginShift()
      length.inc()
      length.inc()
      alias(remaining, chain.h)
      shifts += 1
      mode = Mode.Shift
    }

    /** A nonchain mismatch: copy the reversed candidate window to the FPP SOURCE. */
    private def beginFallback(): Unit = {
      if (replaying) {
        throw new AssertionError("FPP-selected palindrome failed during replay")
      }
      fpp.reset()
      walker.copyFrom(right)
      alias(remaining, length)
      remaining.inc()
      source.write(LEFT)
      source.move(1)
      search.mode = ScaffoldSearch.Mode.Idle
      chain.mode = ScaffoldChain.Mode.Idle
      mode = Mode.Copy
    }

    private def stepShift(): Unit = {
      if (remaining.sign > 0) {
        remaining.dec()
        center.right()
        left.right()
        left.right()
        radius.dec()
        length.dec()
        length.dec()
        chain.shiftOne()
      } else {
        mode = Mode.Scan
        if (!right.gap) {
          output = left.isFirst
        }
      }
    }

    private def stepCopy(): Unit = {
      if (remaining.sign > 0) {
        val symbol = walker.read().getOrElse(throw new AssertionError("fallback window crossed the input origin"))
        source.write(symbol)
        source.move(1)
        walker.left()
        remaining.dec()
      } else {
        source.write(END)
        mode = Mode.Home
      }
    }

    private def stepHome(): Unit = {
      if (source.read() == LEFT) {
        fpp.start()
        fppCalls += 1
        mode = Mode.Fpp
      } else {
        source.move(-1)
      }
    }

    /** Up to `quantum` FPP instructions; at the halt, mark the new place itself. */
    private def stepFpp(): Unit = {
      var count = 0
      var running = true
      while (count < timing.quantum && running) {
        fpp.step()
        if (fpp.done) {
          marks.move(1)
          marks.write(FIRST)
          marks.move(1)
          mode = Mode.MarkEnd
          running = false
        }
        count += 1
      }
    }

    private def stepMarkEnd(): Unit = {
      if (marks.read() == END) {
        marks.move(-1)
        odd = false // old odd length plus one new place
        mode = Mode.Choose
      } else {
        marks.move(1)
      }
    }

    /** Select the longest odd palindromic place suffix among the marks. */
    private def stepChoose(): Unit = {
      if (odd && (marks.read() == "1" || marks.read() == FIRST)) {
        left.copyFrom(right)
        center.copyFrom(right)
        length.reset()
        length.inc()
        radius.reset()
        pair = 0
        mode = Mode.Rewind
      } else {
        marks.move(-1)
        odd = !odd
      }
    }

    /** Move L (and every second place C) back from R to the selected candidate. */
    private def stepRewind(): Unit = {
      if (marks.read() == FIRST) {
        fpp.reset()
        mode = Mode.ReplayStart
      } else {
        marks.move(-1)
        left.left()
        length.inc()
        pair = 1 - pair
        if (pair == 0) {
          center.left()
          radius.inc()
        }
      }
    }

    /** No coordinates or head equality: replay consumes the saved radius. */
    private def stepReplayStart(): Unit = {
      alias(replay, radius)
      right.copyFrom(center)
      left.copyFrom(center)
      radius.reset()
      length.reset()
      length.inc()
      chain.mode = ScaffoldChain.Mode.Idle
      search.start(zero)
      replaying = replay.sign > 0
      clock = timing.matchDelay
      mode = Mode.Scan
      replays += 1
      if (!replaying && !right.gap) {
        output = left.isFirst
      }
    }

    /** Record every view and the control fields in the new node and emit it. */
    private def finish(): Unit = {
      for (head <- heads) {
        head.finish()
      }
      for (counter <- counters) {
        counter.finish()
      }
      search.finish()
      chain.finish()
      fpp.finish()
      b.label("g.mode") = mode.label
      b.label("g.clock") = clock.toString
      b.label("g.out") = output
      b.label("g.replaying") = replaying
      b.label("g.odd") = odd
      b.label("g.pair") = pair
      emit(vm, b)
    }
  }

  /** Python `_transition`: one local operation of the controller on `vm`.
    *
    * @param arrival            the input character of this tick (`None` for work ticks)
    * @param newInput           broadcast `arrival` to the heads (once per arrival)
    * @param advanceTrailingGap the gap after the last letter is available without more input
    */
  def transition(
      vm: VM,
      arrival: Option[String],
      newInput: Boolean,
      kernels: Kernels,
      advanceTrailingGap: Boolean,
      timing: Timing = DEFAULT_TIMING
  ): Transition = {
    new Tick(vm, arrival, newInput, kernels, advanceTrailingGap, timing).run()
  }

  /** Legacy tick boundary, retained for comparison with the earlier circuits.
    * (Python returns `report, caught, events`; `inputReady` is carried along.)
    */
  def step(vm: VM, arrival: Option[String], newInput: Boolean, kernels: Kernels = Kernels.default): Transition = {
    transition(vm, arrival, newInput, kernels, advanceTrailingGap = false, DEFAULT_TIMING)
  }

  /** An output event and a read boundary are independent observations.
    *
    * None means no output event; zero is a completed negative answer. Events
    * are diagnostics and do not control execution.
    */
  final case class OnlineStep(output: Option[Int], inputReady: Boolean, events: Events)

  /** The source protocol driven by `GalilRealtime.BufferedSource`: [[OnlineGalil]]
    * or a scripted test source.
    */
  trait OnlineSource {
    def inputReady: Boolean
    def read(char: String): OnlineStep
    def work(): OnlineStep
  }

  /** Event interface to the experimental online controller, without a budget.
    *
    * read consumes exactly one binary symbol and performs one local transition.
    * work performs one local transition with no input symbol. It may be needed
    * after an output to prepare the next read. Both return an OnlineStep.
    *
    * This fixes the input/output protocol, not the remaining correspondence and
    * timing obligations of the underlying algorithm. There is no drain loop,
    * external input buffer or palindrome oracle inside this object. Its extra control is
    * two Boolean flags; VM and finite kernels hold the actual source machine.
    */
  final class OnlineGalil(quantum: Int = FPP_QUANTUM) extends OnlineSource {
    val vm: VM = new VM
    val kernels: Kernels = Kernels.default
    val timing: Timing = derive(quantum)

    /** The source is waiting for its next input symbol. */
    var inputReady: Boolean = true

    private var outputPending = false

    def read(char: String): OnlineStep = {
      if (char != "a" && char != "b") {
        throw new IllegalArgumentException("one binary input symbol required")
      }
      if (!inputReady) {
        throw new IllegalArgumentException("source is not ready to read another symbol")
      }
      outputPending = true
      advance(Some(char), newInput = true)
    }

    def work(): OnlineStep = {
      if (inputReady) {
        throw new IllegalArgumentException("source is waiting for an input symbol")
      }
      advance(None, newInput = false)
    }

    private def advance(char: Option[String], newInput: Boolean): OnlineStep = {
      val t = transition(vm, char, newInput, kernels, advanceTrailingGap = true, timing)
      val output = if (t.caught && outputPending) { Some(t.report) } else { None }
      if (output.isDefined) {
        outputPending = false
      }
      if (t.inputReady && outputPending) {
        throw new AssertionError("source requested another input before emitting its answer")
      }
      inputReady = t.inputReady
      OnlineStep(output, t.inputReady, t.events)
    }
  }

  /** The result of [[run]]: one report per input letter plus the VM statistics,
    * the summed events, the ticks spent per letter and their maximum
    * (Python's `reports, {**vm.stats(), **totals, "costs": ..., "max_microsteps": ...}`).
    */
  final case class GalilRun(reports: Vector[Int], stats: Stats, events: Events, costs: Vector[Int], maxMicrosteps: Int) {

    /** The Python stats dict, in its key order. */
    def pythonRepr: String = {
      val pairs = Vector(
        s"'steps': ${stats.steps}", s"'radius': ${stats.radius}", s"'fields': ${stats.fields}", s"'labels': ${stats.labels}"
      ) ++ events.toMap.map { case (k, v) => s"'$k': $v" } ++ Vector(
        s"'costs': ${costs.mkString("[", ", ", "]")}", s"'max_microsteps': $maxMicrosteps"
      )
      pairs.mkString("{", ", ", "}")
    }
  }

  /** Drive the legacy interface over `word`: without a budget every arrival is
    * drained until caught; with a budget exactly that many ticks run per letter.
    */
  def run(word: String, budget: Option[Int] = None): GalilRun = {
    if (word.exists(c => c != 'a' && c != 'b')) {
      throw new IllegalArgumentException("binary input required")
    }
    if (budget.exists(_ < 1)) {
      throw new IllegalArgumentException("positive integer budget required")
    }
    val kernels = Kernels.default
    val vm = new VM
    val reports = mutable.ArrayBuffer.empty[Int]
    val costs = mutable.ArrayBuffer.empty[Int]
    var totals = Events()
    for (arrival <- word) {
      var ticks = 0
      var caught = false
      var report = 0
      def more: Boolean = budget.fold(!caught)(ticks < _)
      while (more) {
        val t = step(vm, Some(arrival.toString), ticks == 0, kernels)
        report = t.report
        caught = t.caught
        totals = totals + t.events
        ticks += 1
      }
      reports += report
      costs += ticks
    }
    GalilRun(reports.toVector, vm.stats, totals, costs.toVector, costs.maxOption.getOrElse(0))
  }

  /** Fixed-budget scaffold candidate; this is a scaffold VM machine, not a PEG. */
  def recognize(word: String): Boolean = {
    val result = run(word, Some(REALTIME_BUDGET))
    word.isEmpty || result.reports.last != 0
  }
}
