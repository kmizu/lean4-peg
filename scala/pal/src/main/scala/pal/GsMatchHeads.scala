package pal

import scala.collection.mutable

import Action.{Call, Emit}
import Coroutine.Local

/** Fixed-head GS matching, including the short-prefix verifier.
  *
  * Tail is the fixed boundary between the pattern and growing text. OriginalEnd
  * is the arrival frontier. The control is finite; integer positions live only
  * in StreamingMatcher, the test interpreter. InputHeads remain to be attached.
  *
  * Port of `gs_match_heads.py`.
  */
object GsMatchHeads {
  import Event.*
  import GsHeads.{Decompose, HEADS, HeadGenerator, PeriodShift, ResetShift, TESTS, compileController, unitMoves}

  val MATCH_HEADS: Vector[String] = HEADS :+ "U"

  val MATCH_TESTS: Set[String] = TESTS + "available"

  /** `matcher_controller(k)`: decompose the pattern (`Origin..Tail`), then match
    * it against the arriving text forever, verifying the short prefix `u` with
    * two comparisons per successful `v` comparison.
    *
    * The generator never returns; the compiler closes its branches anyway.
    */
  final class MatcherController(k: Int) extends HeadGenerator[Unit]("matcher_controller") {
    if (k < 4) {
      throw new IllegalArgumentException("fixed integer k >= 4 required")
    }

    private var periodExists: Option[Boolean] = None
    private var prefixOk: Option[Boolean] = None
    private var phase: Option[Int] = None
    private var decompose: Decompose = new Decompose(k)

    override def locals: Vector[(String, Local)] = {
      Vector[(String, Local)]("k" -> k) ++
        periodExists.map(value => "period_exists" -> (value: Local)) ++
        phase.map(value => "phase" -> (value: Local)) ++
        prefixOk.map(value => "prefix_ok" -> (value: Local))
    }

    private def offsetHead(): Action[Event, Unit] = {
      site = 8
      Emit(less("Walk", "Cut"))
    }

    private def outerLoop(): Action[Event, Unit] = {
      site = 11
      Emit(copy("Walk", "Origin"))
    }

    private def matchHead(): Action[Event, Unit] = {
      site = 13
      Emit(Available("B"))
    }

    /** One iteration of `for phase in range(2)`. */
    private def forBody(): Action[Event, Unit] = {
      if (!prefixOk.get) {
        afterFor()
      } else {
        site = 16
        Emit(less("Walk", "Cut"))
      }
    }

    private def afterFor(): Action[Event, Unit] = {
      site = 19
      Emit(equal("A", "End"))
    }

    private def shiftDecision(): Action[Event, Unit] = {
      if (periodExists.get) {
        site = 22
        Emit(less("A", "KFirst"))
      } else {
        resetShift()
      }
    }

    private def resetShift(): Action[Event, Unit] = {
      site = 25
      Call(new ResetShift(k, true))
    }

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 =>
          site = 1
          Emit(copy("End", "Tail"))
        case 1 =>
          decompose = new Decompose(k)
          site = 2
          Call(decompose)
        case 2 =>
          periodExists = Some(decompose.result)
          site = 3
          Emit(copy("P", "Tail"))
        case 3 =>
          site = 4
          Emit(copy("KP", "End"))
        case 4 =>
          site = 5
          Emit(copy("A", "Cut"))
        case 5 =>
          site = 6
          Emit(copy("B", "P"))
        case 6 =>
          site = 7
          Emit(copy("Walk", "Origin"))
        case 7 => offsetHead()
        case 8 =>
          if (response.get) {
            // This initial text offset must consume arrived cells too. The indexed
            // reference can name a future position; a local head must wait before
            // crossing each of those characters.
            site = 9
            Emit(Available("B"))
          } else {
            outerLoop()
          }
        case 9 =>
          if (response.get) {
            site = 10
            Emit(move(Movement("Walk", 1), Movement("B", 1)))
          } else {
            site = 9
            Emit(Available("B"))
          }
        case 10 => offsetHead()
        case 11 =>
          site = 12
          Emit(copy("U", "P"))
        case 12 =>
          prefixOk = Some(true)
          matchHead()
        case 13 =>
          if (response.get) {
            site = 14
            Emit(symbols("A", "B"))
          } else {
            matchHead()
          }
        case 14 =>
          if (response.get) {
            site = 15
            Emit(move(Movement("A", 1), Movement("B", 1)))
          } else {
            shiftDecision()
          }
        case 15 =>
          phase = Some(0)
          forBody()
        case 16 =>
          if (response.get) {
            site = 17
            Emit(symbols("Walk", "U"))
          } else {
            afterFor()
          }
        case 17 =>
          if (response.get) {
            site = 18
            Emit(move(Movement("Walk", 1), Movement("U", 1)))
          } else {
            prefixOk = Some(false)
            afterFor()
          }
        case 18 =>
          if (phase.contains(0)) {
            phase = Some(1)
            forBody()
          } else {
            afterFor()
          }
        case 19 =>
          if (response.get) {
            if (prefixOk.get) {
              site = 20
              Emit(AssertEqual("Walk", "Cut"))
            } else {
              shiftDecision()
            }
          } else {
            matchHead()
          }
        case 20 =>
          site = 21
          Emit(Match("B"))
        case 21 => shiftDecision()
        case 22 =>
          if (response.get) {
            resetShift()
          } else {
            site = 23
            Emit(less("Reach", "A"))
          }
        case 23 =>
          if (response.get) {
            resetShift()
          } else {
            site = 24
            Call(new PeriodShift(k, true))
          }
        case _ => outerLoop()
      }
    }
  }

  def matcherController(k: Int = 8): MatcherController = new MatcherController(k)

  def compileMatcher(k: Int = 8, unit: Boolean = true): Program = {
    val program = compileController(k, controller = k => matcherController(k), tests = MATCH_TESTS)
    if (unit) unitMoves(program) else program
  }
}

/** Position-array observer for the finite head table, without a clock claim. */
class StreamingMatcher(pattern: String, program: Option[Program] = None) {
  import Event.*
  import GsHeads.BLIND
  import GsMatchHeads.{MATCH_HEADS, MATCH_TESTS}

  if (pattern.isEmpty) {
    throw new IllegalArgumentException("nonempty pattern required")
  }

  /** Pattern followed by the arrived text. */
  val word: mutable.ArrayBuffer[Char] = mutable.ArrayBuffer.from(pattern)
  val patternSize: Int = pattern.length
  val table: Program = program.getOrElse(GsMatchHeads.compileMatcher())
  val positions: mutable.LinkedHashMap[String, Int] = mutable.LinkedHashMap.from(MATCH_HEADS.map(_ -> 0))
  positions("Tail") = pattern.length
  positions("OriginalEnd") = pattern.length
  var state: Int = table.start
  var steps: Int = 0
  private val outputBuffer: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

  /** Text-end indices of the positive matches so far. */
  def outputs: Vector[Int] = outputBuffer.toVector

  /** Is the next comparison waiting for another character? */
  def waiting: Boolean = {
    table.code(state).event match {
      case Available(head) => positions(head) >= word.length
      case _ => false
    }
  }

  def append(char: Char): Unit = {
    word += char
    positions("OriginalEnd") += 1
  }

  /** Execute one instruction; returns a positive match's text-end index. */
  def step(): Option[Int] = {
    val Row(event, targets) = table.code(state)
    steps += 1
    var decision: Option[Boolean] = None
    var output: Option[Int] = None
    event match {
      case Move(moves) =>
        moves.foreach { case Movement(head, delta) =>
          positions(head) += delta
          if (!BLIND.contains(head) && !(0 <= positions(head) && positions(head) <= word.length)) {
            throw new AssertionError(("head crossed the arrived input", head, positions(head), word.length).toString)
          }
        }
      case Copy(target, source) => positions(target) = positions(source)
      case Equal(left, right) => decision = Some(positions(left) == positions(right))
      case Less(left, right) => decision = Some(positions(left) < positions(right))
      case AssertEqual(left, right) =>
        if (positions(left) != positions(right)) {
          throw new AssertionError("short-prefix checker missed its deadline")
        }
      case Symbols(left, right) =>
        val a = positions(left)
        val b = positions(right)
        if (!(0 <= a && a < word.length && 0 <= b && b < word.length)) {
          throw new AssertionError(("query beyond arrival frontier", event, a, b, word.length).toString)
        }
        decision = Some(word(a) == word(b))
      case Available(head) => decision = Some(positions(head) < word.length)
      case Match(head) =>
        output = Some(positions(head) - patternSize)
        outputBuffer += output.get
      case _ => throw new IllegalArgumentException("unknown matching instruction")
    }
    state = if (MATCH_TESTS.contains(event.op)) targets(if (decision.get) 1 else 0) else targets(0)
    output
  }

  /** Run until the matcher waits for input; returns the number of steps taken. */
  def drain(watchdog: Int = 1000000): Int = {
    val start = steps
    while (!waiting) {
      if (steps - start >= watchdog) {
        throw new IllegalStateException("test interpreter exceeded its watchdog")
      }
      step()
    }
    steps - start
  }
}
