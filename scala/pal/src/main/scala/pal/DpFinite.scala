package pal

import FppFinite.*
import FppFinite.Instruction.*
import FppSubroutine.{buildMarkedProgram, SOURCE, MARKS}

/** Finite offline double-palindrome search; Galil's scheduler is separate.
  *
  * Given ^word$ and unary ^1^lower$, prepare FPP marker tapes and find the
  * least h > lower with marked lengths 2h+1 and 4h+1. Output h is a unary
  * tape and success is a halt state. Addresses never guide machine control.
  * Input must be the reversed window when looking for suffix palindromes.
  *
  * Python 原典: `dp_finite.py`。
  */
object DpFinite {
  val SECOND: Int = 9
  val LOWER: Int = 10
  val OUTPUT: Int = 11

  final case class DpRun(
    h: Option[Int],
    steps: Int,
    tapes: Vector[Tape] = Vector.empty,
    positions: Vector[Int] = Vector.empty
  )

  class DpProgram(alphabetSymbols: Iterable[String], ntapes: Int = 12) extends Program(alphabetSymbols, ntapes) {

    /** Python の `DpProgram.run(word, lower=0)`（基底の `run` とは戻り値が違うので別名）。 */
    def runDp(word: String, lower: Int = 0): DpRun = {
      if (word.exists(c => !sourceAlphabet.contains(c.toString))) {
        throw new IllegalArgumentException("input outside source alphabet")
      }
      if (lower < 0) {
        throw new IllegalArgumentException("nonnegative unary lower bound required")
      }
      val tapes = Tape.fresh(ntapes)
      tapes(SOURCE) = Tape.bounded(word)
      tapes(LOWER) = Tape.bounded("1" * lower)
      val result = execute(tapes, Array.fill(ntapes)(0), 1000 * (word.length + lower + 1))
      val h = if (found.contains(result.state)) {
        // Decode the unary OUTPUT tape externally, never a head position.
        var count = 0
        while (result.tapes(OUTPUT).read(count + 1) == "1") {
          count += 1
        }
        Some(count)
      } else {
        None
      }
      DpRun(h, result.steps, result.tapes, result.positions)
    }
  }

  object DpProgram {
    def apply(alphabet: String, ntapes: Int = 12): DpProgram = new DpProgram(alphabet.map(_.toString), ntapes)
  }

  /** Python の `build_dp_program(alphabet="ab")`。 */
  def buildDpProgram(alphabet: String = "ab"): DpProgram = {
    val fpp = buildMarkedProgram(alphabet)
    val p = DpProgram(alphabet + "#", ntapes = 12)
    p.sourceAlphabet = alphabet.map(_.toString).toVector
    p.copyCodeFrom(fpp)
    // The duplicate mark tape must remain coherent during preparation,
    // candidate movement, and marking. No shared tape or pointer equality.
    for ((row, q) <- fpp.instructions.zipWithIndex) {
      row match {
        case Write(MARKS, value, k) =>
          val extra = p.add(Write(SECOND, value, k))
          p.set(q, Write(MARKS, value, extra))
        case Move(MARKS, direction, k) =>
          val extra = p.add(Move(SECOND, direction, k))
          p.set(q, Move(MARKS, direction, extra))
        case _ => ()
      }
    }

    val found = p.add(Halt)
    p.found = Some(found)
    val missed = p.add(Halt)

    def advance(tape: Int, count: Int, k0: Int): Int = {
      // Check each skipped cell for the end marker; no out-of-bounds seek.
      var k = k0
      for (_ <- 0 until count) {
        val move = p.move(tape, 1, k)
        k = p.branch(tape, choices(LEFT -> move, "0" -> move, "1" -> move, END -> missed))
      }
      k
    }

    val candidate = p.reserve()
    val checkSecond = p.reserve()
    val nextH = p.move(OUTPUT, 1, p.write(OUTPUT, "1",
      advance(MARKS, 2, advance(SECOND, 4, checkSecond))))
    val checkFirst = p.branch(MARKS, choices("0" -> nextH, "1" -> found, END -> missed))
    val allowed = p.branch(SECOND, choices("0" -> nextH, "1" -> checkFirst, END -> missed))
    p.branch(LOWER, choices("1" -> p.move(LOWER, 1, nextH), END -> allowed), candidate)
    p.branch(SECOND, choices("0" -> candidate, "1" -> candidate, END -> missed), checkSecond)
    val begin = p.write(OUTPUT, LEFT, p.move(LOWER, 1,
      advance(MARKS, 1, advance(SECOND, 1, nextH))))
    for ((row, q) <- fpp.instructions.zipWithIndex) {
      if (row == Halt) {
        // A local branch replaces the kernel's halt, with no epsilon callback.
        p.set(q, Read(SOURCE, choices(LEFT -> begin)))
      }
    }
    p.start = fpp.start
    p.validate()
    p
  }
}
