package pal

import scala.collection.mutable

import Coroutine.Frame

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

/** The finite-table operations of `gs_heads.py`: bisimulation reduction, unit-move
  * lowering and the closure of a controller's finite control into a [[Program]].
  * `GsHeads` re-exports them; the border controller they compile by default is
  * [[GsHeads.borderController]].
  */
object GsProgram {
  import Event.*
  import GsHeads.{HeadGenerator, TESTS, borderController}

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
