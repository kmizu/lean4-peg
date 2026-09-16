package pal

import scala.collection.mutable

/** Sparse real-time TM to plain PEG: inspect only explicitly guarded tapes.
  * （Python 版: `docs/palindromes-in-peg/symbolic_tm2peg.py`）
  *
  * Like tm2peg, one transition consumes one symbol of reverse(input).
  * This does NOT convert an offline instruction program into a real-time TM.
  * Absent tape operations preserve both focus and position. A `None` write
  * preserves focus while moving. Tape zippers are bi-infinite, as in tm2peg.
  * Overlapping partial guards are rejected instead of assigning hidden priority.
  */
object SymbolicTm2Peg {

  type Move = Tm2Peg.Move
  val Move: Tm2Peg.Move.type = Tm2Peg.Move

  /** One tape operation: an optional write (`None` keeps the focus symbol) then a move. */
  final case class Operation(write: Option[String], move: Move)

  /** One transition row.  `focus` guards only the tapes it mentions; `operations`
    * touches only the tapes it mentions (absent tapes keep focus and position).
    */
  final case class Transition(
      source: String,
      input: String,
      focus: Map[Int, String],
      target: String,
      operations: Map[Int, Operation]
  )

  /** `ValueError` in Python. */
  private def invalid(message: String): Nothing = throw new IllegalArgumentException(message)

  /** Split a string into its Unicode code points (Python iterates `str` that way). */
  private def codePoints(s: String): Vector[String] = {
    s.codePoints().toArray.toVector.map(cp => new String(Character.toChars(cp)))
  }

  final class SymbolicTM(
      val ntapes: Int,
      stateSeq: Seq[String],
      val initial: String,
      acceptingStates: Iterable[String],
      transitionSeq: Seq[Transition],
      inputChars: String = "ab",
      val blank: String = "_"
  ) {
    val states: Vector[String] = stateSeq.toVector
    val accepting: Set[String] = acceptingStates.toSet
    val transitions: Vector[Transition] = transitionSeq.toVector
    val inputAlphabet: Vector[String] = codePoints(inputChars)

    if (ntapes < 0 || states.distinct.size != states.size) {
      invalid("invalid tapes or duplicate states")
    }
    if (!states.contains(initial) || !accepting.subsetOf(states.toSet)) {
      invalid("unknown initial/accepting state")
    }
    if (inputAlphabet.isEmpty || inputAlphabet.exists(c => !isBmpScalar(c))) {
      invalid("nonempty BMP scalar character alphabet required")
    }

    /** Rows grouped by (source, input) in first-seen order; rows keep their order. */
    val groups: Map[(String, String), Vector[Transition]] = {
      val grouped = mutable.LinkedHashMap.empty[(String, String), mutable.ArrayBuffer[Transition]]
      transitions.foreach { row =>
        validateRow(row)
        val peers = grouped.getOrElseUpdate((row.source, row.input), mutable.ArrayBuffer.empty)
        peers.foreach { previous =>
          val common = previous.focus.keySet.intersect(row.focus.keySet)
          if (common.forall(t => previous.focus(t) == row.focus(t))) {
            invalid("overlapping symbolic transition guards")
          }
        }
        peers += row
      }
      grouped.view.mapValues(_.toVector).toMap
    }

    val tapeAlphabet: Vector[String] = {
      val symbols = mutable.Set(blank)
      transitions.foreach { row =>
        symbols ++= row.focus.values
        symbols ++= row.operations.values.flatMap(_.write)
      }
      symbols.toVector.sorted
    }

    private def isBmpScalar(c: String): Boolean = {
      c.codePointCount(0, c.length) == 1 && {
        val cp = c.codePointAt(0)
        cp <= 0xffff && !(0xd800 <= cp && cp <= 0xdfff)
      }
    }

    private def validateRow(row: Transition): Unit = {
      if (!states.contains(row.source) || !states.contains(row.target)) {
        invalid("unknown transition state")
      }
      if (!inputAlphabet.contains(row.input)) {
        invalid("unknown input character")
      }
      if ((row.focus.keys ++ row.operations.keys).exists(t => t < 0 || t >= ntapes)) {
        invalid("unknown tape")
      }
    }

    /** Simulate on reverse(word) with bi-infinite tapes; false on a missing transition. */
    def run(word: String): Boolean = {
      var state = initial
      val tapes = Vector.fill(ntapes)(mutable.Map.empty[Int, String])
      val heads = Array.fill(ntapes)(0)
      val input = codePoints(word).reverse
      var i = 0
      var stuck = false
      while (i < input.length && !stuck) {
        val char = input(i)
        val scanned = (0 until ntapes).map(t => tapes(t).getOrElse(heads(t), blank))
        val row = groups.getOrElse((state, char), Vector.empty).find { r =>
          r.focus.forall { case (t, s) => scanned(t) == s }
        }
        row match {
          case None => stuck = true
          case Some(r) =>
            state = r.target
            r.operations.foreach { case (t, Operation(write, move)) =>
              write.foreach(w => tapes(t).update(heads(t), w))
              heads(t) += (move match {
                case Move.L => -1
                case Move.R => 1
                case Move.S => 0
              })
            }
        }
        i += 1
      }
      !stuck && accepting.contains(state)
    }

    // ---------------------------------------------------------------- compilation

    private val stateIds: Map[String, Int] = states.zipWithIndex.toMap
    private val symbolIds: Map[String, Int] = tapeAlphabet.zipWithIndex.toMap

    /** Parser.CHAR accepts Unicode escapes but not JSON's backspace escape. */
    private def literal(text: String): String = {
      if (text == "\b") "\"\\u0008\"" else PyFormat.jsonString(text)
    }
    private def guard(text: String): String = s"&($text)"
    private def previous(text: String): String = ". " + text
    private def state(q: String): String = s"St_${stateIds(q)}"
    private def focus(t: Int, s: String): String = s"Sc_${t}_${symbolIds(s)}"
    private def pushed(side: String, t: Int, s: String): String = s"${side}sym_${t}_${symbolIds(s)}"

    private def rule(name: String, alternatives: Seq[String]): String = {
      s"$name = " + (if (alternatives.nonEmpty) alternatives.mkString(" / ") else "!\"\"") + ";"
    }

    private def startRule: String = {
      val accept = states.filter(accepting.contains).map(q => guard(state(q))).mkString(" / ")
      rule("S", Vector("(" + (if (accept.nonEmpty) accept else "!\"\"") + ") " +
        "(" + inputAlphabet.map(literal).mkString(" / ") + ")* !."))
    }

    /** Each guard is shared by all state/tape equations. No focus-vector
      * Cartesian product is formed, including for unchanged tapes.
      */
    private def transitionRules: Vector[String] = {
      transitions.zipWithIndex.map { case (row, i) =>
        val parts = Vector(guard(literal(row.input)), guard(previous(state(row.source)))) ++
          row.focus.toVector.sortBy(_._1).map { case (t, s) => guard(previous(focus(t, s))) }
        rule(s"D_$i", Vector(parts.mkString(" ")))
      }
    }

    private def stateRules: Vector[String] = {
      states.map { q =>
        val initialAlt = if (q == initial) Vector("&(!.)") else Vector.empty
        val events = transitions.zipWithIndex.collect { case (row, i) if row.target == q => s"D_$i" }
        rule(state(q), initialAlt ++ events)
      }
    }

    /** Per-tape bookkeeping collected from the transition rows. */
    private final class TapeEvents(t: Int) {
      val changed = mutable.ArrayBuffer.empty[String]
      val moves: Map[Move, mutable.ArrayBuffer[String]] =
        Map(Move.L -> mutable.ArrayBuffer.empty, Move.R -> mutable.ArrayBuffer.empty)
      val writes: Map[String, mutable.ArrayBuffer[String]] =
        tapeAlphabet.map(s => s -> mutable.ArrayBuffer.empty[String]).toMap
      val pushes: Map[(String, String), mutable.ArrayBuffer[String]] =
        (for (side <- Vector("L", "R"); s <- tapeAlphabet) yield (side, s) -> mutable.ArrayBuffer.empty[String]).toMap

      transitions.zipWithIndex.foreach { case (row, i) =>
        val Operation(write, move) = row.operations.getOrElse(t, Operation(None, Move.S))
        val event = s"D_$i"
        if (move != Move.S) {
          changed += event
          moves(move) += event
          val side = if (move == Move.R) "L" else "R"
          tapeAlphabet.foreach { s =>
            write match {
              case None => pushes((side, s)) += event + " " + guard(previous(focus(t, s)))
              case Some(w) => if (w == s) { pushes((side, s)) += event }
            }
          }
        } else {
          write.foreach { w =>
            changed += event
            writes(w) += event
          }
        }
      }
    }

    private def tapeRules(t: Int): Vector[String] = {
      val events = new TapeEvents(t)
      val out = mutable.ArrayBuffer.empty[String]
      out += rule(s"Change_$t", events.changed.toSeq)
      for (direction <- Vector(Move.L, Move.R)) {
        out += rule(s"Move${direction}_$t", events.moves(direction).toSeq)
      }
      for (s <- tapeAlphabet) {
        val alts = mutable.ArrayBuffer.empty[String]
        if (s == blank) { alts += "&(!.)" }
        alts ++= events.writes(s)
        alts += s"!Change_$t " + guard(previous(focus(t, s)))
        for ((side, direction) <- Vector(("R", "R"), ("L", "L"))) {
          val ptr = previous(s"${side}t_$t")
          alts += s"Move${direction}_$t " + guard(ptr + " " + pushed(side, t, s))
          if (s == blank) { alts += s"Move${direction}_$t !($ptr)" }
        }
        out += rule(focus(t, s), alts.toSeq)
      }
      for ((side, pushDirection, popDirection) <- Vector(("L", "R", "L"), ("R", "L", "R"))) {
        val ptr = previous(s"${side}t_$t")
        out += rule(s"${side}t_$t", Vector(s"Move${pushDirection}_$t",
          s"Move${popDirection}_$t $ptr $ptr",
          s"!MoveL_$t !MoveR_$t $ptr"))
        for (s <- tapeAlphabet) {
          out += rule(pushed(side, t, s), events.pushes((side, s)).toSeq)
        }
      }
      out.toVector
    }

    /** The plain PEG text, one rule per line, with a trailing newline. */
    def compile(): String = {
      val rules = Vector(startRule) ++ transitionRules ++ stateRules ++
        (0 until ntapes).flatMap(tapeRules)
      rules.mkString("\n") + "\n"
    }
  }

  /** Every dense delta entry of a `Tm2Peg.TM` becomes one fully guarded row. */
  def fromDense(machine: Tm2Peg.TM, extraTapes: Int = 0): SymbolicTM = {
    val rows = machine.delta.map { case (Tm2Peg.Key(q, scanned, char), Tm2Peg.Step(q2, operations)) =>
      Transition(q, char.toString, scanned.zipWithIndex.map { case (s, t) => t -> s.toString }.toMap, q2,
        operations.zipWithIndex.map { case (op, t) => t -> Operation(Some(op.write.toString), op.move) }.toMap)
    }
    new SymbolicTM(machine.ntapes + extraTapes, machine.states, machine.initial, machine.accepting, rows,
      machine.inputAlphabet, machine.blank.toString)
  }
}
