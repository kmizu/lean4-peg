package pal

import scala.collection.IndexedSeq

import scala.collection.mutable

import Action.{Call, Emit, Return}
import Coroutine.{Frame, Local}

/** One instruction of the finite head table (a Python event tuple, `event[0]` is
  * [[Event.op]]). The tests (`equal`, `less`, `symbols`, `available`) have two
  * successors ordered false/true; every other instruction has one.
  */
sealed abstract class Event(val op: String)

object Event {

  /** A batch of head moves applied simultaneously. */
  final case class Move(moves: Vector[Movement]) extends Event("move")

  /** `target := source`. */
  final case class Copy(target: String, source: String) extends Event("copy")

  final case class Equal(left: String, right: String) extends Event("equal")

  final case class Less(left: String, right: String) extends Event("less")

  /** Compare the symbols under two heads. */
  final case class Symbols(left: String, right: String) extends Event("symbols")

  /** Report the coordinate of a head to the observer. */
  final case class Border(head: String) extends Event("border")

  /** Emit one palindrome-prefix flag bit. */
  final case class Flag(value: Boolean) extends Event("flag")

  /** Has the cell under `head` arrived yet? (`gs_match_heads`) */
  final case class Available(head: String) extends Event("available")

  /** Verifier deadline check (`gs_match_heads`). */
  final case class AssertEqual(left: String, right: String) extends Event("assert_equal")

  /** Report a positive match ending at `head` (`gs_match_heads`). */
  final case class Match(head: String) extends Event("match")

  case object Halt extends Event("halt")

  /** `move` of a single head by `delta` cells; `move((("P", 1),))` in Python. */
  final case class Movement(head: String, delta: Int)

  def move(moves: Movement*): Move = Move(moves.toVector)
  def copy(target: String, source: String): Copy = Copy(target, source)
  def equal(left: String, right: String): Equal = Equal(left, right)
  def less(left: String, right: String): Less = Less(left, right)
  def symbols(left: String, right: String): Symbols = Symbols(left, right)
}

/** One row of a [[Program]]: `(event, successors)`; test successors are ordered
  * false/true.
  */
final case class Row(event: Event, targets: Vector[Int])

/** The closed finite instruction table of a controller.
  *
  * @param constructionStates number of states before bisimulation reduction
  *        (0 in an unreduced program, as in the Python dataclass default)
  */
final case class Program(code: Vector[Row], start: Int, k: Int, constructionStates: Int = 0)

/** Local-head version of the GS overlap pass.
  *
  * The generator's control observes symbols and head order only. Coordinates
  * live in the VM below, never in the generator. Its only integer local is a
  * phase bounded by the fixed parameter k. Compilation closes over that finite
  * control and emits a table, so the generator is not a runtime primitive.
  *
  * Port of `gs_heads.py`. The generators are [[Generator]] state machines (see
  * [[Coroutine]] for the encoding); each `site` constant names one textual
  * `yield` or `yield from` of the Python source, numbered in source order, so
  * that the control keys of [[GsHeads.compileController]] have exactly the
  * granularity of CPython's `(co_name, f_lasti, f_locals)`.
  *
  * Background: `GS_OVERLAP.md` (algorithm and what the head implementation
  * establishes) and `GS_LOCAL_CLOCK.md` (instruction accounting).
  */
object GsHeads {
  import Event.*

  val HEADS: Vector[String] = Vector("Origin", "OriginalEnd", "End", "Cut", "Tail", "A", "B", "P",
    "First", "Reach", "Walk", "KP", "KFirst", "Second")

  /** Heads that never read a symbol and may hold negative coordinates. */
  val BLIND: Set[String] = Set("KP", "KFirst", "Second")

  /** The branching instructions of the border controller. */
  val TESTS: Set[String] = Set("equal", "less", "symbols")

  /** A generator of head events. */
  type HeadGenerator[R] = Generator[Event, R]

  private def requireK(k: Int): Unit = {
    if (k < 4) {
      throw new IllegalArgumentException("fixed integer k >= 4 required")
    }
  }

  /** `_initialize(k)`: place the search heads at the current cut. */
  final class Initialize(k: Int) extends HeadGenerator[Unit]("_initialize") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site += 1
      site match {
        case 1 => Emit(copy("A", "Cut"))
        case 2 => Emit(copy("P", "Cut"))
        case 3 => Emit(move(Movement("P", 1)))
        case 4 => Emit(copy("B", "P"))
        case 5 => Emit(copy("KP", "Cut"))
        case 6 => Emit(move(Movement("KP", k)))
        case _ => Return(())
      }
    }
  }

  /** `_reset_shift(k, search)`: shift by `max(1, ceil(matched / k))` while rewinding
    * `A` (and `B` during matching) to the cut. `phase` counts rewound cells modulo k.
    */
  final class ResetShift(k: Int, search: Boolean) extends HeadGenerator[Unit]("_reset_shift") {
    private var phase: Int = 0
    private var nonempty: Option[Boolean] = None

    override def locals: Vector[(String, Local)] = {
      Vector[(String, Local)]("k" -> k, "search" -> search, "phase" -> phase) ++
        nonempty.map(value => "nonempty" -> (value: Local))
    }

    private def shiftEvent: Move = {
      if (search) {
        move(Movement("P", 1), Movement("B", 1), Movement("KP", -1))
      } else {
        move(Movement("P", 1), Movement("KP", k))
      }
    }

    private def loopHead(): Action[Event, Unit] = {
      site = 2
      Emit(equal("A", "Cut"))
    }

    private def afterLoop(): Action[Event, Unit] = {
      if (!nonempty.get || phase != 0) {
        site = if (search) 7 else 8
        Emit(shiftEvent)
      } else {
        tail()
      }
    }

    private def tail(): Action[Event, Unit] = {
      if (!search) {
        site = 9
        Emit(copy("B", "P"))
      } else {
        Return(())
      }
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 =>
          phase = 0
          site = 1
          Emit(equal("A", "Cut"))
        case 1 =>
          nonempty = Some(!response.get)
          loopHead()
        case 2 =>
          if (response.get) {
            afterLoop()
          } else if (search) {
            site = 3
            Emit(move(Movement("A", -1), Movement("B", -1)))
          } else {
            site = 4
            Emit(move(Movement("A", -1)))
          }
        case 3 | 4 =>
          phase += 1
          if (phase == k) {
            site = if (search) 5 else 6
            Emit(shiftEvent)
          } else {
            loopHead()
          }
        case 5 | 6 =>
          phase = 0
          loopHead()
        case 7 | 8 => tail()
        case _ => Return(())
      }
    }
  }

  /** `_period_shift(k, search)`: shift by the first period `First - Cut` while
    * keeping the matched suffix.
    */
  final class PeriodShift(k: Int, search: Boolean) extends HeadGenerator[Unit]("_period_shift") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k, "search" -> search)

    private def loopHead(): Action[Event, Unit] = {
      site = 2
      Emit(less("Walk", "First"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 =>
          site = 1
          Emit(copy("Walk", "Cut"))
        case 1 => loopHead()
        case 2 =>
          if (response.get) {
            if (search) {
              site = 3
              Emit(move(Movement("Walk", 1), Movement("A", -1), Movement("P", 1), Movement("KP", -1)))
            } else {
              site = 4
              Emit(move(Movement("Walk", 1), Movement("A", -1), Movement("P", 1), Movement("KP", k)))
            }
          } else {
            Return(())
          }
        case _ => loopHead()
      }
    }
  }

  /** `_first(k, bounded)`: find the shortest basic prefix of the pattern (from
    * `Cut`) repeated k times; `bounded` restricts the period below `Second`.
    * Returns whether a first period was found (`First = Cut + p`, `B = KP`).
    */
  final class First(k: Int, bounded: Boolean) extends HeadGenerator[Boolean]("_first") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k, "bounded" -> bounded)

    private def outerHead(): Action[Event, Boolean] = {
      site = 2
      Emit(less("P", "End"))
    }

    private def innerHead(): Action[Event, Boolean] = {
      site = 4
      Emit(less("B", "End"))
    }

    private def afterInner(): Action[Event, Boolean] = {
      site = 8
      Emit(equal("B", "KP"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        case 0 =>
          site = 1
          Call(new Initialize(k))
        case 1 => outerHead()
        case 2 =>
          if (!response.get) {
            Return(false)
          } else if (bounded) {
            site = 3
            Emit(less("P", "Second"))
          } else {
            innerHead()
          }
        case 3 => if (response.get) innerHead() else Return(false)
        case 4 =>
          if (response.get) {
            site = 5
            Emit(less("B", "KP"))
          } else {
            afterInner()
          }
        case 5 =>
          if (response.get) {
            site = 6
            Emit(symbols("A", "B"))
          } else {
            afterInner()
          }
        case 6 =>
          if (response.get) {
            site = 7
            Emit(move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterInner()
          }
        case 7 => innerHead()
        case 8 =>
          if (response.get) {
            Return(true)
          } else {
            site = 9
            Call(new ResetShift(k, false))
          }
        case _ => outerHead()
      }
    }
  }

  /** `_second(k)`: search a second k-prefix-period beyond the reach of the first.
    * Returns whether one was found (`P = Cut + p2`).
    */
  final class Second(k: Int) extends HeadGenerator[Boolean]("_second") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    private def outerHead(): Action[Event, Boolean] = {
      site = 2
      Emit(less("P", "End"))
    }

    private def innerHead(): Action[Event, Boolean] = {
      site = 3
      Emit(less("B", "End"))
    }

    private def afterInner(): Action[Event, Boolean] = {
      site = 8
      Emit(less("A", "KFirst"))
    }

    private def resetShift(): Action[Event, Boolean] = {
      site = 11
      Call(new ResetShift(k, false))
    }

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        case 0 =>
          site = 1
          Call(new Initialize(k))
        case 1 => outerHead()
        case 2 => if (response.get) innerHead() else Return(false)
        case 3 =>
          if (response.get) {
            site = 4
            Emit(symbols("A", "B"))
          } else {
            afterInner()
          }
        case 4 =>
          if (response.get) {
            site = 5
            Emit(move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterInner()
          }
        case 5 =>
          site = 6
          Emit(less("Reach", "B"))
        case 6 =>
          if (response.get) {
            site = 7
            Emit(less("B", "KP"))
          } else {
            innerHead()
          }
        case 7 => if (response.get) innerHead() else Return(true)
        case 8 =>
          if (response.get) {
            resetShift()
          } else {
            site = 9
            Emit(less("Reach", "A"))
          }
        case 9 =>
          if (response.get) {
            resetShift()
          } else {
            site = 10
            Call(new PeriodShift(k, false))
          }
        case _ => outerHead()
      }
    }
  }

  /** `_decompose(k)`: the GS prefix decomposition with local heads. Leaves `Cut`
    * at the short prefix boundary and, when a period exists, `First`/`KFirst`/
    * `Reach` describing it. Returns whether a period exists.
    */
  final class Decompose(k: Int) extends HeadGenerator[Boolean]("_decompose") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    private var first: First = new First(k, false)
    private var second: Second = new Second(k)

    private def outer(): Action[Event, Boolean] = {
      first = new First(k, false)
      site = 2
      Call(first)
    }

    private def extendHead(): Action[Event, Boolean] = {
      site = 5
      Emit(less("B", "End"))
    }

    private def afterExtend(): Action[Event, Boolean] = {
      site = 8
      Emit(copy("Reach", "B"))
    }

    private def boundedHead(): Action[Event, Boolean] = {
      first = new First(k, true)
      site = 11
      Call(first)
    }

    private def cutHead(): Action[Event, Boolean] = {
      site = 12
      Emit(less("Cut", "P"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        case 0 =>
          site = 1
          Emit(copy("Cut", "Origin"))
        case 1 => outer()
        case 2 =>
          if (!first.result) {
            Return(false)
          } else {
            site = 3
            Emit(copy("First", "P"))
          }
        case 3 =>
          site = 4
          Emit(copy("KFirst", "B"))
        case 4 => extendHead()
        case 5 =>
          if (response.get) {
            site = 6
            Emit(symbols("A", "B"))
          } else {
            afterExtend()
          }
        case 6 =>
          if (response.get) {
            site = 7
            Emit(move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterExtend()
          }
        case 7 => extendHead()
        case 8 =>
          second = new Second(k)
          site = 9
          Call(second)
        case 9 =>
          if (!second.result) {
            Return(true)
          } else {
            site = 10
            Emit(copy("Second", "P"))
          }
        case 10 => boundedHead()
        case 11 => if (first.result) cutHead() else outer()
        case 12 =>
          if (response.get) {
            // Second remains at Cut + the saved second-period length. A copy of
            // Cut alone would lose that relative bound, so move both in lockstep.
            site = 13
            Emit(move(Movement("Cut", 1), Movement("Second", 1)))
          } else {
            boundedHead()
          }
        case _ => cutHead()
      }
    }
  }

  /** `_report(flags)`: report a found border, either as a `border` coordinate or
    * as descending flag bits from `Cursor` down to the border length. Returns
    * whether the flag job is complete (`Cursor < Lower`).
    */
  final class Report(flags: Boolean) extends HeadGenerator[Boolean]("_report") {
    override def locals: Vector[(String, Local)] = Vector("flags" -> flags)

    private def fillHead(): Action[Event, Boolean] = {
      site = 4
      Emit(less("KP", "Cursor"))
    }

    private def finalTest(): Action[Event, Boolean] = {
      site = 9
      Emit(less("Cursor", "Lower"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        case 0 =>
          if (!flags) {
            site = 1
            Emit(Border("KP"))
          } else {
            site = 2
            Emit(less("KP", "Lower"))
          }
        case 1 => Return(false)
        case 2 =>
          if (response.get) {
            Return(true)
          } else {
            site = 3
            Emit(less("Cursor", "KP"))
          }
        case 3 => if (response.get) finalTest() else fillHead()
        case 4 =>
          if (response.get) {
            site = 5
            Emit(Flag(false))
          } else {
            site = 7
            Emit(Flag(true))
          }
        case 5 =>
          site = 6
          Emit(move(Movement("Cursor", -1)))
        case 6 => fillHead()
        case 7 =>
          site = 8
          Emit(move(Movement("Cursor", -1)))
        case 8 => finalTest()
        case _ => Return(response.get)
      }
    }
  }

  /** `_finish_flags()`: emit the remaining flags down to `Lower`; only the
    * empty prefix (`Cursor == Origin`) is a palindrome.
    */
  final class FinishFlags extends HeadGenerator[Unit]("_finish_flags") {
    private def head(): Action[Event, Unit] = {
      site = 1
      Emit(less("Cursor", "Lower"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 => head()
        case 1 =>
          if (response.get) {
            Return(())
          } else {
            site = 2
            Emit(equal("Cursor", "Origin"))
          }
        case 2 =>
          if (response.get) {
            site = 3
            Emit(Flag(true))
          } else {
            site = 4
            Emit(Flag(false))
          }
        case 3 | 4 =>
          site = 5
          Emit(move(Movement("Cursor", -1)))
        case _ => head()
      }
    }
  }

  /** `border_controller(k, flags, tail_origin)`: enumerate all nonempty proper
    * borders of the loaded view in strictly decreasing order, stage by stage
    * (see `GS_OVERLAP.md`). With `flags`, report them as palindrome-prefix flag
    * bits between `Upper` and `Lower` instead of `border` coordinates.
    * `tailOrigin` is the text origin of the two-view variant (`gs_dual_flags`).
    */
  final class BorderController(k: Int, flags: Boolean = false, tailOrigin: String = "Origin")
    extends HeadGenerator[Unit]("border_controller") {
    requireK(k)

    private var firstStage: Boolean = true
    private var periodExists: Option[Boolean] = None
    private var decompose: Decompose = new Decompose(k)
    private var report: Report = new Report(flags)

    override def locals: Vector[(String, Local)] = {
      Vector[(String, Local)]("k" -> k, "flags" -> flags, "tail_origin" -> tailOrigin,
        "first_stage" -> firstStage) ++
        periodExists.map(value => "period_exists" -> (value: Local))
    }

    private def stageHead(): Action[Event, Unit] = {
      site = 3
      Emit(less("Origin", "End"))
    }

    private def finish(nextSite: Int): Action[Event, Unit] = {
      site = nextSite
      Call(new FinishFlags)
    }

    private def startDecomposition(): Action[Event, Unit] = {
      decompose = new Decompose(k)
      site = 6
      Call(decompose)
    }

    private def offsetHead(): Action[Event, Unit] = {
      site = 14
      Emit(less("Walk", "Cut"))
    }

    private def matchHead(): Action[Event, Unit] = {
      site = 18
      Emit(less("Second", "P"))
    }

    private def scanHead(): Action[Event, Unit] = {
      site = 19
      Emit(less("B", "OriginalEnd"))
    }

    private def endTest(): Action[Event, Unit] = {
      site = 22
      Emit(equal("B", "OriginalEnd"))
    }

    private def prefixHead(): Action[Event, Unit] = {
      site = 25
      Emit(less("Walk", "Cut"))
    }

    private def prefixDone(): Action[Event, Unit] = {
      site = 28
      Emit(equal("Walk", "Cut"))
    }

    private def restoreB(): Action[Event, Unit] = {
      site = 31
      Emit(copy("B", "OriginalEnd"))
    }

    private def shiftDecision(): Action[Event, Unit] = {
      if (periodExists.get) {
        site = 32
        Emit(less("A", "KFirst"))
      } else {
        resetShift()
      }
    }

    private def resetShift(): Action[Event, Unit] = {
      site = 35
      Call(new ResetShift(k, true))
    }

    private def shrinkStart(): Action[Event, Unit] = {
      site = 36
      Emit(copy("Second", "Origin"))
    }

    private def shrinkWalk(): Action[Event, Unit] = {
      site = 38
      Emit(less("Walk", "Cut"))
    }

    private def shrinkEnd(): Action[Event, Unit] = {
      site = 42
      Emit(less("Second", "End"))
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 =>
          firstStage = true
          site = 1
          Emit(copy("End", "OriginalEnd"))
        case 1 =>
          site = 2
          Emit(copy("Tail", tailOrigin))
        case 2 => stageHead()
        case 3 =>
          if (!response.get) {
            if (flags) finish(44) else Return(())
          } else if (flags && tailOrigin != "Origin") {
            site = 4
            Emit(less("End", "Lower"))
          } else {
            startDecomposition()
          }
        case 4 => if (response.get) finish(5) else startDecomposition()
        case 5 => Return(())
        case 6 =>
          // During matching, KP is the current overlap length, and Second is
          // the last permitted text start (OriginalEnd - max(1, 2*Cut)).
          periodExists = Some(decompose.result)
          site = 7
          Emit(copy("P", "Tail"))
        case 7 =>
          site = 8
          Emit(copy("KP", "End"))
        case 8 =>
          if (firstStage) {
            site = 9
            Emit(move(Movement("P", 1), Movement("KP", -1)))
          } else {
            site = 10
            Emit(copy("A", "Cut"))
          }
        case 9 =>
          site = 10
          Emit(copy("A", "Cut"))
        case 10 =>
          site = 11
          Emit(copy("B", "P"))
        case 11 =>
          site = 12
          Emit(copy("Second", "OriginalEnd"))
        case 12 =>
          site = 13
          Emit(copy("Walk", "Origin"))
        case 13 => offsetHead()
        case 14 =>
          if (response.get) {
            site = 15
            Emit(move(Movement("Walk", 1), Movement("B", 1), Movement("Second", -2)))
          } else {
            site = 16
            Emit(equal("Cut", "Origin"))
          }
        case 15 => offsetHead()
        case 16 =>
          if (response.get) {
            site = 17
            Emit(move(Movement("Second", -1)))
          } else {
            matchHead()
          }
        case 17 => matchHead()
        case 18 => if (response.get) shrinkStart() else scanHead()
        case 19 =>
          if (response.get) {
            site = 20
            Emit(symbols("A", "B"))
          } else {
            endTest()
          }
        case 20 =>
          if (response.get) {
            site = 21
            Emit(move(Movement("A", 1), Movement("B", 1)))
          } else {
            endTest()
          }
        case 21 => scanHead()
        case 22 =>
          if (response.get) {
            // B can be reused for the prefix check, since its saved position
            // here is exactly OriginalEnd. A retains the matched suffix length.
            site = 23
            Emit(copy("Walk", "Origin"))
          } else {
            shiftDecision()
          }
        case 23 =>
          site = 24
          Emit(copy("B", "P"))
        case 24 => prefixHead()
        case 25 =>
          if (response.get) {
            site = 26
            Emit(symbols("Walk", "B"))
          } else {
            prefixDone()
          }
        case 26 =>
          if (response.get) {
            site = 27
            Emit(move(Movement("Walk", 1), Movement("B", 1)))
          } else {
            prefixDone()
          }
        case 27 => prefixHead()
        case 28 =>
          if (response.get) {
            report = new Report(flags)
            site = 29
            Call(report)
          } else {
            restoreB()
          }
        case 29 => if (report.result) finish(30) else restoreB()
        case 30 => Return(())
        case 31 => shiftDecision()
        case 32 =>
          if (response.get) {
            resetShift()
          } else {
            site = 33
            Emit(less("Reach", "A"))
          }
        case 33 =>
          if (response.get) {
            resetShift()
          } else {
            site = 34
            Call(new PeriodShift(k, true))
          }
        case 34 | 35 => matchHead()
        case 36 =>
          // Retain only lengths below the completed interval. Tail = N - End.
          site = 37
          Emit(copy("Walk", "Origin"))
        case 37 => shrinkWalk()
        case 38 =>
          if (response.get) {
            site = 39
            Emit(move(Movement("Walk", 1), Movement("Second", 2)))
          } else {
            site = 40
            Emit(equal("Cut", "Origin"))
          }
        case 39 => shrinkWalk()
        case 40 =>
          if (!response.get) {
            site = 41
            Emit(move(Movement("Second", -1)))
          } else {
            shrinkEnd()
          }
        case 41 => shrinkEnd()
        case 42 =>
          if (response.get) {
            site = 43
            Emit(move(Movement("End", -1), Movement("Tail", 1)))
          } else {
            firstStage = false
            stageHead()
          }
        case 43 => shrinkEnd()
        case _ => Return(())
      }
    }
  }

  /** `border_controller(k=8, flags=False, tail_origin="Origin")`. */
  def borderController(k: Int = 8, flags: Boolean = false, tailOrigin: String = "Origin"): BorderController = {
    new BorderController(k, flags, tailOrigin)
  }

  /** Bisimulation of the complete finite command/test table, without traces. */
  def minimize(program: Program): Program = {
    var groups = Vector.fill(program.code.size)(0)
    var stable = false
    while (!stable) {
      val identifiers = mutable.LinkedHashMap.empty[(Event, Vector[Int]), Int]
      val refined = program.code.map { row =>
        val key = (row.event, row.targets.map(groups))
        identifiers.getOrElseUpdate(key, identifiers.size)
      }
      if (refined == groups) {
        stable = true
      } else {
        groups = refined
      }
    }
    val code = new Array[Row](groups.distinct.size)
    program.code.zipWithIndex.foreach { case (row, index) =>
      code(groups(index)) = Row(row.event, row.targets.map(groups))
    }
    val constructionStates = if (program.constructionStates != 0) program.constructionStates else program.code.size
    Program(code.toVector, groups(program.start), program.k, constructionStates)
  }

  /** Replace each bounded batch by one head's unit move per instruction. */
  def unitMoves(program: Program): Program = {
    val code = mutable.ArrayBuffer.from(program.code)
    program.code.zipWithIndex.foreach { case (Row(event, targets), state) =>
      event match {
        case Move(batch) =>
          val moves = batch.flatMap { case Movement(head, delta) =>
            Vector.fill(math.abs(delta))(Movement(head, if (delta > 0) 1 else -1))
          }
          if (moves.isEmpty) {
            throw new IllegalArgumentException("empty move instruction")
          }
          var target = targets(0)
          moves.drop(1).reverse.foreach { movement =>
            code += Row(move(movement), Vector(target))
            target = code.size - 1
          }
          code(state) = Row(move(moves(0)), Vector(target))
        case _ => ()
      }
    }
    minimize(Program(code.toVector, program.start, program.k, program.constructionStates))
  }

  /** `_control_key`: the event plus the whole suspended frame chain. */
  private type ControlKey = (Event, List[Frame])

  /** Close all finite-control branches, independently of any input words.
    *
    * `maxStates` is a compiler watchdog. It cannot affect an emitted program's
    * accepted word lengths. No sampled execution states determine this table.
    *
    * As in Python, a state is reached by replaying its response path on a fresh
    * controller; its identity is [[Generator.frames]] (name, site, locals of
    * every frame in the `yield from` chain) together with the pending event.
    */
  def compileController(k: Int = 8, maxStates: Int = 10000, reduce: Boolean = true,
                        controller: Int => HeadGenerator[?] = k => borderController(k),
                        tests: Set[String] = TESTS): Program = {
    def replay(path: Vector[Option[Boolean]]): Option[(HeadGenerator[?], Event)] = {
      val generator = controller(k)
      var current: Step[Event, ?] = generator.send(None)
      val responses = path.iterator
      while (responses.hasNext && current.isInstanceOf[Yielded[?]]) {
        current = generator.send(responses.next())
      }
      current match {
        case Yielded(event) => Some((generator, event))
        case Returned(_) => None
      }
    }

    val (firstGenerator, firstEvent) = replay(Vector.empty).get
    val identifiers = mutable.HashMap[ControlKey, Int]((firstEvent, firstGenerator.frames) -> 1)
    val placeholder = Row(Halt, Vector.empty)
    val code = mutable.ArrayBuffer(placeholder, placeholder)
    val paths = mutable.ArrayBuffer(Vector.empty[Option[Boolean]], Vector.empty[Option[Boolean]])
    var cursor = 1
    while (cursor < code.size) {
      val path = paths(cursor)
      val event = replay(path).get._2
      val responses: Vector[Option[Boolean]] = if (tests.contains(event.op)) Vector(Some(false), Some(true)) else Vector(None)
      val destinations = responses.map { response =>
        val follow = path :+ response
        replay(follow) match {
          case None => 0
          case Some((generator, following)) =>
            val key: ControlKey = (following, generator.frames)
            identifiers.get(key) match {
              case Some(identifier) => identifier
              case None =>
                if (code.size >= maxStates) {
                  throw new IllegalStateException("finite controller construction exceeded its watchdog")
                }
                val identifier = code.size
                identifiers(key) = identifier
                code += placeholder
                paths += follow
                identifier
            }
        }
      }
      code(cursor) = Row(event, destinations)
      cursor += 1
    }
    val program = Program(code.toVector, 1, k, code.size)
    if (reduce) minimize(program) else program
  }
}

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
