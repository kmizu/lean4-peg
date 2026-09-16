package pal

import Action.Return
import Coroutine.Local

/** Local-head version of the GS overlap pass.
  *
  * The generator's control observes symbols and head order only. Coordinates
  * live in the VM below, never in the generator. Its only integer local is a
  * phase bounded by the fixed parameter k. Compilation closes over that finite
  * control and emits a table, so the generator is not a runtime primitive.
  *
  * Port of `gs_heads.py` (the table types are in [[GsProgram]], the observer in [[HeadVM]]). The generators are [[Generator]] state machines (see
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

  /** The table compiler lives in [[GsProgram]]; re-exported here as in `gs_heads.py`. */
  export GsProgram.{compileController, minimize, unitMoves}

  private def requireK(k: Int): Unit = {
    if (k < 4) {
      throw new IllegalArgumentException("fixed integer k >= 4 required")
    }
  }

  /** `_initialize(k)`: place the search heads at the current cut. */
  final class Initialize(k: Int) extends HeadGenerator[Unit]("_initialize") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        // start: gs_heads.py:18 def _initialize
        case 0 => emitAt(1, copy("A", "Cut"))
        // site 1 = gs_heads.py:19 yield ("copy", "A", "Cut")
        case 1 => emitAt(2, copy("P", "Cut"))
        // site 2 = gs_heads.py:20 yield ("copy", "P", "Cut")
        case 2 => emitAt(3, move(Movement("P", 1)))
        // site 3 = gs_heads.py:21 yield ("move", (("P", 1),))
        case 3 => emitAt(4, copy("B", "P"))
        // site 4 = gs_heads.py:22 yield ("copy", "B", "P")
        case 4 => emitAt(5, copy("KP", "Cut"))
        // site 5 = gs_heads.py:23 yield ("copy", "KP", "Cut")
        case 5 => emitAt(6, move(Movement("KP", k)))
        // site 6 = gs_heads.py:24 yield ("move", (("KP", k),))
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

    private def loopHead(): Action[Event, Unit] = emitAt(2, equal("A", "Cut"))

    private def afterLoop(): Action[Event, Unit] = {
      if (!nonempty.get || phase != 0) {
        emitAt(if (search) 7 else 8, shiftEvent)
      } else {
        tail()
      }
    }

    private def tail(): Action[Event, Unit] = {
      if (!search) {
        emitAt(9, copy("B", "P"))
      } else {
        Return(())
      }
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        // start: gs_heads.py:27 def _reset_shift
        case 0 =>
          phase = 0
          emitAt(1, equal("A", "Cut"))
        // site 1 = gs_heads.py:29 yield ("equal", "A", "Cut")
        case 1 =>
          nonempty = Some(!response.get)
          loopHead()
        // site 2 = gs_heads.py:30 yield ("equal", "A", "Cut")
        case 2 =>
          if (response.get) {
            afterLoop()
          } else if (search) {
            emitAt(3, move(Movement("A", -1), Movement("B", -1)))
          } else {
            emitAt(4, move(Movement("A", -1)))
          }
        // site 3 = gs_heads.py:32 yield ("move", (("A", -1), ("B", -1)))
        // site 4 = gs_heads.py:34 yield ("move", (("A", -1),))
        case 3 | 4 =>
          phase += 1
          if (phase == k) {
            emitAt(if (search) 5 else 6, shiftEvent)
          } else {
            loopHead()
          }
        // site 5 = gs_heads.py:38 yield ("move", (("P", 1), ("B", 1), ("KP", -1)))
        // site 6 = gs_heads.py:40 yield ("move", (("P", 1), ("KP", k)))
        case 5 | 6 =>
          phase = 0
          loopHead()
        // site 7 = gs_heads.py:44 yield ("move", (("P", 1), ("B", 1), ("KP", -1)))
        // site 8 = gs_heads.py:46 yield ("move", (("P", 1), ("KP", k)))
        case 7 | 8 => tail()
        // site 9 = gs_heads.py:48 yield ("copy", "B", "P")
        case _ => Return(())
      }
    }
  }

  /** `_period_shift(k, search)`: shift by the first period `First - Cut` while
    * keeping the matched suffix.
    */
  final class PeriodShift(k: Int, search: Boolean) extends HeadGenerator[Unit]("_period_shift") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k, "search" -> search)

    private def loopHead(): Action[Event, Unit] = emitAt(2, less("Walk", "First"))

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        // start: gs_heads.py:51 def _period_shift
        case 0 => emitAt(1, copy("Walk", "Cut"))
        // site 1 = gs_heads.py:52 yield ("copy", "Walk", "Cut")
        case 1 => loopHead()
        // site 2 = gs_heads.py:53 yield ("less", "Walk", "First")
        case 2 =>
          if (response.get) {
            if (search) {
              emitAt(3, move(Movement("Walk", 1), Movement("A", -1), Movement("P", 1), Movement("KP", -1)))
            } else {
              emitAt(4, move(Movement("Walk", 1), Movement("A", -1), Movement("P", 1), Movement("KP", k)))
            }
          } else {
            Return(())
          }
        // site 3 = gs_heads.py:55 yield ("move", (("Walk", 1), ("A", -1), ("P", 1), ("KP", -1)))
        // site 4 = gs_heads.py:57 yield ("move", (("Walk", 1), ("A", -1), ("P", 1), ("KP", k)))
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

    private def outerHead(): Action[Event, Boolean] = emitAt(2, less("P", "End"))

    private def innerHead(): Action[Event, Boolean] = emitAt(4, less("B", "End"))

    private def afterInner(): Action[Event, Boolean] = emitAt(8, equal("B", "KP"))

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        // start: gs_heads.py:60 def _first
        case 0 => callAt(1, new Initialize(k))
        // site 1 = gs_heads.py:61 yield from _initialize(k)
        case 1 => outerHead()
        // site 2 = gs_heads.py:62 yield ("less", "P", "End")
        case 2 =>
          if (!response.get) {
            Return(false)
          } else if (bounded) {
            emitAt(3, less("P", "Second"))
          } else {
            innerHead()
          }
        // site 3 = gs_heads.py:63 yield ("less", "P", "Second")
        case 3 => if (response.get) innerHead() else Return(false)
        // site 4 = gs_heads.py:65 yield ("less", "B", "End")
        case 4 =>
          if (response.get) {
            emitAt(5, less("B", "KP"))
          } else {
            afterInner()
          }
        // site 5 = gs_heads.py:66 yield ("less", "B", "KP")
        case 5 =>
          if (response.get) {
            emitAt(6, symbols("A", "B"))
          } else {
            afterInner()
          }
        // site 6 = gs_heads.py:68 yield ("symbols", "A", "B")
        case 6 =>
          if (response.get) {
            emitAt(7, move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterInner()
          }
        // site 7 = gs_heads.py:70 yield ("move", (("A", 1), ("B", 1)))
        case 7 => innerHead()
        // site 8 = gs_heads.py:71 yield ("equal", "B", "KP")
        case 8 =>
          if (response.get) {
            Return(true)
          } else {
            callAt(9, new ResetShift(k, false))
          }
        // site 9 = gs_heads.py:73 yield from _reset_shift(k, False)
        case _ => outerHead()
      }
    }
  }

  /** `_second(k)`: search a second k-prefix-period beyond the reach of the first.
    * Returns whether one was found (`P = Cut + p2`).
    */
  final class Second(k: Int) extends HeadGenerator[Boolean]("_second") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    private def outerHead(): Action[Event, Boolean] = emitAt(2, less("P", "End"))

    private def innerHead(): Action[Event, Boolean] = emitAt(3, less("B", "End"))

    private def afterInner(): Action[Event, Boolean] = emitAt(8, less("A", "KFirst"))

    private def resetShift(): Action[Event, Boolean] = callAt(11, new ResetShift(k, false))

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        // start: gs_heads.py:77 def _second
        case 0 => callAt(1, new Initialize(k))
        // site 1 = gs_heads.py:78 yield from _initialize(k)
        case 1 => outerHead()
        // site 2 = gs_heads.py:79 yield ("less", "P", "End")
        case 2 => if (response.get) innerHead() else Return(false)
        // site 3 = gs_heads.py:80 yield ("less", "B", "End")
        case 3 =>
          if (response.get) {
            emitAt(4, symbols("A", "B"))
          } else {
            afterInner()
          }
        // site 4 = gs_heads.py:81 yield ("symbols", "A", "B")
        case 4 =>
          if (response.get) {
            emitAt(5, move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterInner()
          }
        // site 5 = gs_heads.py:83 yield ("move", (("A", 1), ("B", 1)))
        case 5 => emitAt(6, less("Reach", "B"))
        // site 6 = gs_heads.py:84 yield ("less", "Reach", "B")
        case 6 =>
          if (response.get) {
            emitAt(7, less("B", "KP"))
          } else {
            innerHead()
          }
        // site 7 = gs_heads.py:84 yield ("less", "B", "KP")
        case 7 => if (response.get) innerHead() else Return(true)
        // site 8 = gs_heads.py:86 yield ("less", "A", "KFirst")
        case 8 =>
          if (response.get) {
            resetShift()
          } else {
            emitAt(9, less("Reach", "A"))
          }
        // site 9 = gs_heads.py:86 yield ("less", "Reach", "A")
        case 9 =>
          if (response.get) {
            resetShift()
          } else {
            callAt(10, new PeriodShift(k, false))
          }
        // site 10 = gs_heads.py:87 yield from _period_shift(k, False)
        // site 11 = gs_heads.py:89 yield from _reset_shift(k, False)
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
      callAt(2, first)
    }

    private def extendHead(): Action[Event, Boolean] = emitAt(5, less("B", "End"))

    private def afterExtend(): Action[Event, Boolean] = emitAt(8, copy("Reach", "B"))

    private def boundedHead(): Action[Event, Boolean] = {
      first = new First(k, true)
      callAt(11, first)
    }

    private def cutHead(): Action[Event, Boolean] = emitAt(12, less("Cut", "P"))

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        // start: gs_heads.py:93 def _decompose
        case 0 => emitAt(1, copy("Cut", "Origin"))
        // site 1 = gs_heads.py:94 yield ("copy", "Cut", "Origin")
        case 1 => outer()
        // site 2 = gs_heads.py:96 yield from _first(k, False)
        case 2 =>
          if (!first.result) {
            Return(false)
          } else {
            emitAt(3, copy("First", "P"))
          }
        // site 3 = gs_heads.py:98 yield ("copy", "First", "P")
        case 3 => emitAt(4, copy("KFirst", "B"))
        // site 4 = gs_heads.py:99 yield ("copy", "KFirst", "B")
        case 4 => extendHead()
        // site 5 = gs_heads.py:100 yield ("less", "B", "End")
        case 5 =>
          if (response.get) {
            emitAt(6, symbols("A", "B"))
          } else {
            afterExtend()
          }
        // site 6 = gs_heads.py:101 yield ("symbols", "A", "B")
        case 6 =>
          if (response.get) {
            emitAt(7, move(Movement("A", 1), Movement("B", 1)))
          } else {
            afterExtend()
          }
        // site 7 = gs_heads.py:103 yield ("move", (("A", 1), ("B", 1)))
        case 7 => extendHead()
        // site 8 = gs_heads.py:104 yield ("copy", "Reach", "B")
        case 8 =>
          second = new Second(k)
          callAt(9, second)
        // site 9 = gs_heads.py:105 yield from _second(k)
        case 9 =>
          if (!second.result) {
            Return(true)
          } else {
            emitAt(10, copy("Second", "P"))
          }
        // site 10 = gs_heads.py:107 yield ("copy", "Second", "P")
        case 10 => boundedHead()
        // site 11 = gs_heads.py:108 yield from _first(k, True)
        case 11 => if (first.result) cutHead() else outer()
        // site 12 = gs_heads.py:111 yield ("less", "Cut", "P")
        case 12 =>
          if (response.get) {
            // Second remains at Cut + the saved second-period length. A copy of
            // Cut alone would lose that relative bound, so move both in lockstep.
            emitAt(13, move(Movement("Cut", 1), Movement("Second", 1)))
          } else {
            boundedHead()
          }
        // site 13 = gs_heads.py:112 yield ("move", (("Cut", 1), ("Second", 1)))
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

    private def fillHead(): Action[Event, Boolean] = emitAt(4, less("KP", "Cursor"))

    private def finalTest(): Action[Event, Boolean] = emitAt(9, less("Cursor", "Lower"))

    protected def step(response: Option[Boolean]): Action[Event, Boolean] = {
      site match {
        // start: gs_heads.py:115 def _report
        case 0 =>
          if (!flags) {
            emitAt(1, Border("KP"))
          } else {
            emitAt(2, less("KP", "Lower"))
          }
        // site 1 = gs_heads.py:117 yield ("border", "KP")
        case 1 => Return(false)
        // site 2 = gs_heads.py:119 yield ("less", "KP", "Lower")
        case 2 =>
          if (response.get) {
            Return(true)
          } else {
            emitAt(3, less("Cursor", "KP"))
          }
        // site 3 = gs_heads.py:121 yield ("less", "Cursor", "KP")
        case 3 => if (response.get) finalTest() else fillHead()
        // site 4 = gs_heads.py:122 yield ("less", "KP", "Cursor")
        case 4 =>
          if (response.get) {
            emitAt(5, Flag(false))
          } else {
            emitAt(7, Flag(true))
          }
        // site 5 = gs_heads.py:123 yield ("flag", False)
        case 5 => emitAt(6, move(Movement("Cursor", -1)))
        // site 6 = gs_heads.py:124 yield ("move", (("Cursor", -1),))
        case 6 => fillHead()
        // site 7 = gs_heads.py:125 yield ("flag", True)
        case 7 => emitAt(8, move(Movement("Cursor", -1)))
        // site 8 = gs_heads.py:126 yield ("move", (("Cursor", -1),))
        case 8 => finalTest()
        // site 9 = gs_heads.py:127 yield ("less", "Cursor", "Lower")
        case _ => Return(response.get)
      }
    }
  }

  /** `_finish_flags()`: emit the remaining flags down to `Lower`; only the
    * empty prefix (`Cursor == Origin`) is a palindrome.
    */
  final class FinishFlags extends HeadGenerator[Unit]("_finish_flags") {
    private def head(): Action[Event, Unit] = emitAt(1, less("Cursor", "Lower"))

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        // start: gs_heads.py:130 def _finish_flags
        case 0 => head()
        // site 1 = gs_heads.py:131 yield ("less", "Cursor", "Lower")
        case 1 =>
          if (response.get) {
            Return(())
          } else {
            emitAt(2, equal("Cursor", "Origin"))
          }
        // site 2 = gs_heads.py:132 yield ("equal", "Cursor", "Origin")
        case 2 =>
          if (response.get) {
            emitAt(3, Flag(true))
          } else {
            emitAt(4, Flag(false))
          }
        // site 3 = gs_heads.py:133 yield ("flag", True)
        // site 4 = gs_heads.py:135 yield ("flag", False)
        case 3 | 4 => emitAt(5, move(Movement("Cursor", -1)))
        // site 5 = gs_heads.py:136 yield ("move", (("Cursor", -1),))
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
    private var firstStage: Boolean = true
    private var periodExists: Option[Boolean] = None
    private var decompose: Decompose = new Decompose(k)
    private var report: Report = new Report(flags)

    override def locals: Vector[(String, Local)] = {
      Vector[(String, Local)]("k" -> k, "flags" -> flags, "tail_origin" -> tailOrigin,
        "first_stage" -> firstStage) ++
        periodExists.map(value => "period_exists" -> (value: Local))
    }

    private def stageHead(): Action[Event, Unit] = emitAt(3, less("Origin", "End"))

    private def finish(nextSite: Int): Action[Event, Unit] = callAt(nextSite, new FinishFlags)

    private def startDecomposition(): Action[Event, Unit] = {
      decompose = new Decompose(k)
      callAt(6, decompose)
    }

    private def offsetHead(): Action[Event, Unit] = emitAt(14, less("Walk", "Cut"))

    private def matchHead(): Action[Event, Unit] = emitAt(18, less("Second", "P"))

    private def scanHead(): Action[Event, Unit] = emitAt(19, less("B", "OriginalEnd"))

    private def endTest(): Action[Event, Unit] = emitAt(22, equal("B", "OriginalEnd"))

    private def prefixHead(): Action[Event, Unit] = emitAt(25, less("Walk", "Cut"))

    private def prefixDone(): Action[Event, Unit] = emitAt(28, equal("Walk", "Cut"))

    private def restoreB(): Action[Event, Unit] = emitAt(31, copy("B", "OriginalEnd"))

    private def shiftDecision(): Action[Event, Unit] = {
      if (periodExists.get) {
        emitAt(32, less("A", "KFirst"))
      } else {
        resetShift()
      }
    }

    private def resetShift(): Action[Event, Unit] = callAt(35, new ResetShift(k, true))

    private def shrinkStart(): Action[Event, Unit] = emitAt(36, copy("Second", "Origin"))

    private def shrinkWalk(): Action[Event, Unit] = emitAt(38, less("Walk", "Cut"))

    private def shrinkEnd(): Action[Event, Unit] = emitAt(42, less("Second", "End"))

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        // start: gs_heads.py:139 def border_controller
        case 0 =>
          // Python checks k in the generator body: on the first next(), not at construction.
          requireK(k)
          firstStage = true
          emitAt(1, copy("End", "OriginalEnd"))
        // site 1 = gs_heads.py:143 yield ("copy", "End", "OriginalEnd")
        case 1 => emitAt(2, copy("Tail", tailOrigin))
        // site 2 = gs_heads.py:144 yield ("copy", "Tail", tail_origin)
        case 2 => stageHead()
        // site 3 = gs_heads.py:145 yield ("less", "Origin", "End")
        case 3 =>
          if (!response.get) {
            if (flags) finish(44) else Return(())
          } else if (flags && tailOrigin != "Origin") {
            emitAt(4, less("End", "Lower"))
          } else {
            startDecomposition()
          }
        // site 4 = gs_heads.py:146 yield ("less", "End", "Lower")
        case 4 => if (response.get) finish(5) else startDecomposition()
        // site 5 = gs_heads.py:147 yield from _finish_flags()
        case 5 => Return(())
        // site 6 = gs_heads.py:149 yield from _decompose(k)
        case 6 =>
          // During matching, KP is the current overlap length, and Second is
          // the last permitted text start (OriginalEnd - max(1, 2*Cut)).
          periodExists = Some(decompose.result)
          emitAt(7, copy("P", "Tail"))
        // site 7 = gs_heads.py:152 yield ("copy", "P", "Tail")
        case 7 => emitAt(8, copy("KP", "End"))
        // site 8 = gs_heads.py:153 yield ("copy", "KP", "End")
        case 8 =>
          if (firstStage) {
            emitAt(9, move(Movement("P", 1), Movement("KP", -1)))
          } else {
            emitAt(10, copy("A", "Cut"))
          }
        // site 9 = gs_heads.py:155 yield ("move", (("P", 1), ("KP", -1)))
        case 9 => emitAt(10, copy("A", "Cut"))
        // site 10 = gs_heads.py:156 yield ("copy", "A", "Cut")
        case 10 => emitAt(11, copy("B", "P"))
        // site 11 = gs_heads.py:157 yield ("copy", "B", "P")
        case 11 => emitAt(12, copy("Second", "OriginalEnd"))
        // site 12 = gs_heads.py:158 yield ("copy", "Second", "OriginalEnd")
        case 12 => emitAt(13, copy("Walk", "Origin"))
        // site 13 = gs_heads.py:159 yield ("copy", "Walk", "Origin")
        case 13 => offsetHead()
        // site 14 = gs_heads.py:160 yield ("less", "Walk", "Cut")
        case 14 =>
          if (response.get) {
            emitAt(15, move(Movement("Walk", 1), Movement("B", 1), Movement("Second", -2)))
          } else {
            emitAt(16, equal("Cut", "Origin"))
          }
        // site 15 = gs_heads.py:161 yield ("move", (("Walk", 1), ("B", 1), ("Second", -2)))
        case 15 => offsetHead()
        // site 16 = gs_heads.py:162 yield ("equal", "Cut", "Origin")
        case 16 =>
          if (response.get) {
            emitAt(17, move(Movement("Second", -1)))
          } else {
            matchHead()
          }
        // site 17 = gs_heads.py:163 yield ("move", (("Second", -1),))
        case 17 => matchHead()
        // site 18 = gs_heads.py:164 yield ("less", "Second", "P")
        case 18 => if (response.get) shrinkStart() else scanHead()
        // site 19 = gs_heads.py:165 yield ("less", "B", "OriginalEnd")
        case 19 =>
          if (response.get) {
            emitAt(20, symbols("A", "B"))
          } else {
            endTest()
          }
        // site 20 = gs_heads.py:166 yield ("symbols", "A", "B")
        case 20 =>
          if (response.get) {
            emitAt(21, move(Movement("A", 1), Movement("B", 1)))
          } else {
            endTest()
          }
        // site 21 = gs_heads.py:168 yield ("move", (("A", 1), ("B", 1)))
        case 21 => scanHead()
        // site 22 = gs_heads.py:169 yield ("equal", "B", "OriginalEnd")
        case 22 =>
          if (response.get) {
            // B can be reused for the prefix check, since its saved position
            // here is exactly OriginalEnd. A retains the matched suffix length.
            emitAt(23, copy("Walk", "Origin"))
          } else {
            shiftDecision()
          }
        // site 23 = gs_heads.py:172 yield ("copy", "Walk", "Origin")
        case 23 => emitAt(24, copy("B", "P"))
        // site 24 = gs_heads.py:173 yield ("copy", "B", "P")
        case 24 => prefixHead()
        // site 25 = gs_heads.py:174 yield ("less", "Walk", "Cut")
        case 25 =>
          if (response.get) {
            emitAt(26, symbols("Walk", "B"))
          } else {
            prefixDone()
          }
        // site 26 = gs_heads.py:175 yield ("symbols", "Walk", "B")
        case 26 =>
          if (response.get) {
            emitAt(27, move(Movement("Walk", 1), Movement("B", 1)))
          } else {
            prefixDone()
          }
        // site 27 = gs_heads.py:177 yield ("move", (("Walk", 1), ("B", 1)))
        case 27 => prefixHead()
        // site 28 = gs_heads.py:178 yield ("equal", "Walk", "Cut")
        case 28 =>
          if (response.get) {
            report = new Report(flags)
            callAt(29, report)
          } else {
            restoreB()
          }
        // site 29 = gs_heads.py:179 yield from _report(flags)
        case 29 => if (report.result) finish(30) else restoreB()
        // site 30 = gs_heads.py:180 yield from _finish_flags()
        case 30 => Return(())
        // site 31 = gs_heads.py:182 yield ("copy", "B", "OriginalEnd")
        case 31 => shiftDecision()
        // site 32 = gs_heads.py:183 yield ("less", "A", "KFirst")
        case 32 =>
          if (response.get) {
            resetShift()
          } else {
            emitAt(33, less("Reach", "A"))
          }
        // site 33 = gs_heads.py:184 yield ("less", "Reach", "A")
        case 33 =>
          if (response.get) {
            resetShift()
          } else {
            callAt(34, new PeriodShift(k, true))
          }
        // site 34 = gs_heads.py:185 yield from _period_shift(k, True)
        // site 35 = gs_heads.py:187 yield from _reset_shift(k, True)
        case 34 | 35 => matchHead()
        // site 36 = gs_heads.py:189 yield ("copy", "Second", "Origin")
        case 36 =>
          // Retain only lengths below the completed interval. Tail = N - End.
          emitAt(37, copy("Walk", "Origin"))
        // site 37 = gs_heads.py:190 yield ("copy", "Walk", "Origin")
        case 37 => shrinkWalk()
        // site 38 = gs_heads.py:191 yield ("less", "Walk", "Cut")
        case 38 =>
          if (response.get) {
            emitAt(39, move(Movement("Walk", 1), Movement("Second", 2)))
          } else {
            emitAt(40, equal("Cut", "Origin"))
          }
        // site 39 = gs_heads.py:192 yield ("move", (("Walk", 1), ("Second", 2)))
        case 39 => shrinkWalk()
        // site 40 = gs_heads.py:193 yield ("equal", "Cut", "Origin")
        case 40 =>
          if (!response.get) {
            emitAt(41, move(Movement("Second", -1)))
          } else {
            shrinkEnd()
          }
        // site 41 = gs_heads.py:194 yield ("move", (("Second", -1),))
        case 41 => shrinkEnd()
        // site 42 = gs_heads.py:195 yield ("less", "Second", "End")
        case 42 =>
          if (response.get) {
            emitAt(43, move(Movement("End", -1), Movement("Tail", 1)))
          } else {
            firstStage = false
            stageHead()
          }
        // site 43 = gs_heads.py:196 yield ("move", (("End", -1), ("Tail", 1)))
        case 43 => shrinkEnd()
        // site 44 = gs_heads.py:199 yield from _finish_flags()
        case _ => Return(())
      }
    }
  }

  /** `border_controller(k=8, flags=False, tail_origin="Origin")`. */
  def borderController(k: Int = 8, flags: Boolean = false, tailOrigin: String = "Origin"): BorderController = {
    new BorderController(k, flags, tailOrigin)
  }
}
