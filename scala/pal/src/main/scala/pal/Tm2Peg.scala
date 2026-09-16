package pal

import scala.collection.mutable

/** Compile a real-time multitape Turing machine into a plain PEG.
  * （Python 版: `docs/palindromes-in-peg/tm2peg.py`）
  *
  * Why this works.  A packrat PEG assigns to each (rule, position) one value: failure
  * or a position no earlier than the current one.  Reading the input w from the left,
  * the rules at position i may only depend on rules at positions >= i, so the memo table
  * is filled right to left — which is exactly a machine reading reverse(w) left to right.
  * Fix the correspondence
  *
  * {{{
  *     PEG position i   <->   the configuration after the machine has read
  *                            reverse(w)[0 .. n-1-i], i.e. after reading w[i]
  * }}}
  *
  * so a rule at position i is computed from rules at position i+1 (the previous
  * configuration) and the character w[i] (the symbol just read), and position n (past
  * the end of the input, recognisable by `!.`) carries the initial configuration.  The
  * machine accepts iff the state at position 0 is accepting.
  *
  * Each tape is a zipper (left stack, focus symbol, right stack), as in Kim & Park's
  * TM -> SCA compiler, so no position or identity comparison is ever needed:
  *
  * {{{
  *     Lt_j    value = the position at which the current top cell of tape j's left
  *             stack was pushed; fails when the stack is empty
  *     Rt_j    the same for the right stack
  *     Lsym_j_s / Rsym_j_s   predicate: the cell pushed here carries symbol s
  *     Sc_j_s  predicate: the focus symbol of tape j is s
  *     St_q    predicate: the control state is q
  * }}}
  *
  * and the stack operations become
  *
  * {{{
  *     unchanged      Lt_j  <-  . Lt_j                     (the value at position i+1)
  *     push here      Lt_j  <-  ""                         (this position)
  *     pop            Lt_j  <-  . Lt_j . Lt_j              (the cell below the top)
  * }}}
  *
  * because the cell below the top of the stack at position p is the top of the stack at
  * position p+1.  Reading the symbol of the top cell is `. Lt_j Lsym_j_s`.
  *
  * The machine is real time: one input symbol per step, a bounded number of head moves
  * per step.  `delta(Key(state, scanned, input)) = Step(state', [TapeOp(write, move), ...])`
  * where `scanned` is the tuple of focus symbols, and move is L, S or R.
  *
  * Python の状態は int または str だったが、ここでは全て `String`（`tm_even_a` の
  * 状態 0/1 は "0"/"1"）。生成される規則名は同一。
  */
object Tm2Peg {

  val BLANK: Char = '_'

  /** Head move of one tape in one step. */
  enum Move {
    case L, S, R
  }

  /** What one tape does in one step: write `write` on the focus cell, then move. */
  final case class TapeOp(write: Char, move: Move)

  /** A delta key: control state, the focus symbol of every tape, and the input symbol. */
  final case class Key(state: String, focus: Vector[Char], input: Char)

  /** A delta value: the next state and one operation per tape. */
  final case class Step(target: String, ops: Vector[TapeOp])

  /** A real-time multitape TM.  `delta` keeps insertion order (a Python dict). */
  final class TM(
      val ntapes: Int,
      stateSeq: Seq[String],
      val initial: String,
      acceptingStates: Iterable[String],
      deltaEntries: Seq[(Key, Step)],
      val inputAlphabet: String = "ab",
      tapeSymbols: Option[Seq[Char]] = None,
      val blank: Char = BLANK
  ) {
    val states: Vector[String] = stateSeq.toVector
    val accepting: Set[String] = acceptingStates.toSet

    /** Transition table in insertion order (a later assignment to an existing key keeps
      * the key's original position, as a Python dict does).
      */
    val delta: Vector[(Key, Step)] = {
      val table = mutable.LinkedHashMap.empty[Key, Step]
      deltaEntries.foreach { case (k, v) => table.update(k, v) }
      table.toVector
    }
    private val table: Map[Key, Step] = delta.toMap

    val tapeAlphabet: Vector[Char] = {
      val symbols = tapeSymbols match {
        case Some(explicit) => explicit
        case None =>
          val syms = mutable.Set(blank)
          delta.foreach { case (Key(_, focus, _), Step(_, ops)) =>
            syms ++= focus
            syms ++= ops.map(_.write)
          }
          syms.toSeq
      }
      symbols.sorted.toVector
    }

    // ---------------------------------------------------------------- simulation

    /** One tape as a zipper: left stack, focus symbol, right stack (list head = stack top). */
    private final case class Zipper(left: List[Char], focus: Char, right: List[Char])

    /** Run the machine on reverse(w); true iff the final state is accepting. */
    def run(w: String): Boolean = {
      var state = initial
      var tapes = Vector.fill(ntapes)(Zipper(Nil, blank, Nil))
      w.reverse.foreach { c =>
        val key = Key(state, tapes.map(_.focus), c)
        val Step(next, ops) = table.getOrElse(key, throw new NoSuchElementException(s"no transition for $key"))
        state = next
        tapes = tapes.zip(ops).map { case (zipper, op) => applyOp(zipper, op) }
      }
      accepting.contains(state)
    }

    /** Stacks are kept top-first (`List` head = top), so push/pop are O(1). */
    private def applyOp(zipper: Zipper, op: TapeOp): Zipper = {
      val Zipper(left, _, right) = zipper
      op.move match {
        case Move.S => Zipper(left, op.write, right)
        case Move.R =>
          val (focus, rest) = right match {
            case top :: below => (top, below)
            case Nil          => (blank, Nil)
          }
          Zipper(op.write :: left, focus, rest)
        case Move.L =>
          val (focus, rest) = left match {
            case top :: below => (top, below)
            case Nil          => (blank, Nil)
          }
          Zipper(rest, focus, op.write :: right)
      }
    }

    // ---------------------------------------------------------------- compilation

    private val symbolIndex: Map[Char, Int] = tapeAlphabet.zipWithIndex.toMap

    /** The value of `expr` at position i+1. */
    private def prev(expr: String): String = s". $expr"

    private def guard(expr: String): String = s"&($expr)"

    private def symId(s: Char): String = s"s${symbolIndex(s)}"

    /** Conditions identifying one delta entry, evaluated at position i. */
    private def cond(key: Key): String = {
      val Key(q, focus, c) = key
      val parts = Vector(s"""&("$c")""", guard(prev(s"St_$q"))) ++
        focus.zipWithIndex.map { case (s, j) => guard(prev(s"Sc_${j}_${symId(s)}")) }
      parts.mkString(" ")
    }

    private def stateRules(): Vector[(String, Vector[String])] = {
      states.map { q =>
        val initialAlt = if (q == initial) Vector("&(!.)") else Vector.empty
        val alts = initialAlt ++ delta.collect { case (key, Step(q2, _)) if q2 == q => cond(key) }
        (s"St_$q", alts)
      }
    }

    private def focusRules(j: Int): Vector[(String, Vector[String])] = {
      tapeAlphabet.map { s =>
        val alts = mutable.ArrayBuffer.empty[String]
        if (s == blank) { alts += "&(!.)" } // all tapes start blank
        delta.foreach { case (key, Step(_, ops)) =>
          val TapeOp(write, move) = ops(j)
          move match {
            case Move.S =>
              if (write == s) { alts += cond(key) }
            case Move.R =>
              // new focus = symbol of the right stack top, or blank if empty
              alts += cond(key) + " " + guard(s"${prev(s"Rt_$j")} Rsym_${j}_${symId(s)}")
              if (s == blank) { alts += cond(key) + " " + guard(s"!(${prev(s"Rt_$j")})") }
            case Move.L =>
              alts += cond(key) + " " + guard(s"${prev(s"Lt_$j")} Lsym_${j}_${symId(s)}")
              if (s == blank) { alts += cond(key) + " " + guard(s"!(${prev(s"Lt_$j")})") }
          }
        }
        (s"Sc_${j}_${symId(s)}", alts.toVector)
      }
    }

    /** Stack top rules and pushed-symbol rules for one side of tape j.  A push onto
      * the `side` stack happens when the head moves `pushMove`.
      */
    private def stackRules(j: Int, side: Char, pushMove: Move): Vector[(String, Vector[String])] = {
      val topAlts = delta.map { case (key, Step(_, ops)) =>
        val TapeOp(_, move) = ops(j)
        if (move == pushMove) { cond(key) + " \"\"" } // this position
        else if (move == Move.S) { cond(key) + s" ${prev(s"${side}t_$j")}" } // unchanged
        else { cond(key) + s" ${prev(s"${side}t_$j")} ${prev(s"${side}t_$j")}" } // pop
      }
      val symRules = tapeAlphabet.map { s =>
        val alts = delta.collect {
          case (key, Step(_, ops)) if ops(j).move == pushMove && ops(j).write == s => cond(key)
        }
        (s"${side}sym_${j}_${symId(s)}", alts)
      }
      (s"${side}t_$j", topAlts) +: symRules
    }

    /** The plain PEG text (no trailing newline), one rule per line. */
    def compile(): String = {
      val tapes = 0 until ntapes
      val rules = stateRules() ++
        tapes.flatMap(focusRules) ++
        tapes.flatMap { j => stackRules(j, 'L', Move.R) ++ stackRules(j, 'R', Move.L) }
      val acc = accepting.toVector.sorted.map(q => s"&(St_$q)").mkString(" / ") match {
        case "" => "!(\"\")"
        case s  => s
      }
      val cls = "[" + inputAlphabet + "]"
      val out = Vector(s"S = ($acc) $cls* !.;") ++ rules.map { case (name, alts) =>
        val body = if (alts.nonEmpty) alts.mkString(" / ") else "!(\"\")"
        s"$name = $body;"
      }
      out.mkString("\n")
    }
  }

  // ------------------------------------------------------------------ example machines

  /** Regular demo: an even number of 'a's.  One tape, never moved. */
  def tmEvenA(): TM = {
    val delta = for {
      q <- Vector(0, 1)
      f <- Vector(BLANK)
      entry <- Vector(
        Key(q.toString, Vector(f), 'a') -> Step((1 - q).toString, Vector(TapeOp(BLANK, Move.S))),
        Key(q.toString, Vector(f), 'b') -> Step(q.toString, Vector(TapeOp(BLANK, Move.S)))
      )
    } yield entry
    new TM(1, Vector("0", "1"), "0", Set("0"), delta, inputAlphabet = "ab")
  }

  /** Counter tape: the head position is the counter.  Cells 0,1,2 carry the markers
    * '$', '1', '2' so that the focus tells the machine when the counter is small; the
    * state carries k = min(counter, 3) and is corrected by the marker it reads.
    */
  val MARK: Map[Int, Char] = Map(0 -> '$', 1 -> '1', 2 -> '2')
  val FROM_MARK: Map[Char, Int] = Map('$' -> 0, '1' -> 1, '2' -> 2)

  /** The true min(counter,3) at the start of a step, given the state's guess. */
  private def kAfter(focus: Char, k: Int): Int = FROM_MARK.getOrElse(focus, k)

  /** { a^n b^n }.  Reading reverse(w) = b^n a^n: push on b, pop on a. */
  def tmAnBn(): TM = {
    val delta = mutable.ArrayBuffer.empty[(Key, Step)]
    val syms = Vector(BLANK, '$', '1', '2', 'x')
    for (mode <- "PMD"; k <- 0 to 3; f <- syms) {
      val kk = kAfter(f, k)
      val write = MARK.getOrElse(kk, 'x')
      val q = s"$mode$k"
      val key = (c: Char) => Key(q, Vector(f), c)
      if (mode == 'D') {
        delta += key('a') -> Step("D0", Vector(TapeOp(write, Move.S)))
        delta += key('b') -> Step("D0", Vector(TapeOp(write, Move.S)))
      } else {
        val popTarget = if (kk == 0) "D0" else s"M${if (kk == 3) 3 else kk - 1}"
        val popMove = if (kk == 0) Move.S else Move.L
        if (mode == 'P') {
          // pushing while reading b's
          delta += key('b') -> Step(s"P${math.min(kk + 1, 3)}", Vector(TapeOp(write, Move.R)))
          delta += key('a') -> Step(popTarget, Vector(TapeOp(write, popMove)))
        } else {
          delta += key('b') -> Step("D0", Vector(TapeOp(write, Move.S)))
          delta += key('a') -> Step(popTarget, Vector(TapeOp(write, popMove)))
        }
      }
    }
    val states = for (m <- "PMD"; k <- 0 to 3) yield s"$m$k"
    new TM(1, states.toVector, "P0", Set("M0", "P0"), delta.toVector, inputAlphabet = "ab",
      tapeSymbols = Some(syms))
  }

  /** { u # reverse(u) } over {a,b}, marker '#'.  Reversal-closed, so the machine reads
    * the same shape: push u, turn around at '#', then pop-and-compare.
    *
    * One tape.  The bottom cell of the stack carries a marked symbol ('A'/'B') so that
    * the machine knows, at the moment it pops it, that the stack becomes empty — the
    * acceptance test is by state alone, so this has to be known within the step.
    * Phase 'p' the head sits on the first free cell; at '#' it steps left onto the top.
    */
  def tmMarkedPalindrome(): TM = {
    val delta = mutable.ArrayBuffer.empty[(Key, Step)]
    val syms = Vector(BLANK, 'a', 'b', 'A', 'B')
    val up = Map('a' -> 'A', 'b' -> 'B')
    for (f <- syms) {
      val key = (q: String, c: Char) => Key(q, Vector(f), c)
      val stay = Step("d", Vector(TapeOp(f, Move.S)))
      // ---- phase p0: nothing pushed yet
      for (c <- "ab") { delta += key("p0", c) -> Step("p1", Vector(TapeOp(up(c), Move.R))) } // bottom-marked push
      delta += key("p0", '#') -> Step("e", Vector(TapeOp(f, Move.S))) // empty u: accept later
      // ---- phase p1: pushing
      for (c <- "ab") { delta += key("p1", c) -> Step("p1", Vector(TapeOp(c, Move.R))) }
      delta += key("p1", '#') -> Step("m", Vector(TapeOp(BLANK, Move.L))) // turn around
      // ---- phase m: matching; the focus is the current top
      for (c <- "ab") {
        if (f == 'a' || f == 'b') {
          delta += key("m", c) -> Step(if (f == c) "m" else "d", Vector(TapeOp(BLANK, Move.L)))
        } else if (f == 'A' || f == 'B') {
          val ok = f == up(c)
          delta += key("m", c) -> Step(if (ok) "e" else "d", Vector(TapeOp(BLANK, Move.L)))
        } else {
          delta += key("m", c) -> stay
        }
      }
      delta += key("m", '#') -> stay
      // ---- phase e: the stack is empty and everything matched; any further symbol kills
      for (c <- "ab#") { delta += key("e", c) -> stay }
      for (c <- "ab#") { delta += key("d", c) -> stay }
    }
    new TM(1, Vector("p0", "p1", "m", "e", "d"), "p0", Set("e"), delta.toVector,
      inputAlphabet = "ab#", tapeSymbols = Some(syms))
  }
}
