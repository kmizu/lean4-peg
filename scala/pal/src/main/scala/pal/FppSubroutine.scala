package pal

import FppFinite.*
import FppFinite.Instruction.*

/** Offline FPP subroutine: plain input to a tape of palindrome-prefix marks.
  *
  * Only SOURCE is initially populated (^ word $). All other tapes start blank.
  * The finite controller prepares the two copies of word # reverse(word),
  * initializes work tapes and produces ^ bit_1 ... bit_n $ on MARKS. Every
  * preparation/marking move counts. Runtime control uses no observer integers.
  * Scratch tapes are fresh: reuse/cleanup is a separate calling-convention task.
  *
  * Python 原典: `fpp_subroutine.py`。
  */
object FppSubroutine {
  val SOURCE: Int = 7
  val MARKS: Int = 8

  final case class MarkedRun(
    marks: Vector[Int],
    prepared: String,
    steps: Int,
    tapes: Vector[Tape] = Vector.empty,
    positions: Vector[Int] = Vector.empty
  )

  /** A kernel whose only input is `^word$` on SOURCE; the marks are decoded externally. */
  class MarkedProgram(alphabetSymbols: Iterable[String], ntapes: Int = 9) extends Program(alphabetSymbols, ntapes) {

    /** Python の `MarkedProgram.run(word)`（基底の `run` とは戻り値が違うので別名）。 */
    def runMarked(word: String): MarkedRun = {
      if (word.exists(c => !sourceAlphabet.contains(c.toString))) {
        throw new IllegalArgumentException("input outside source alphabet")
      }
      val tapes = Tape.fresh(ntapes)
      tapes(SOURCE) = Tape.bounded(word)
      val result = execute(tapes, Array.fill(ntapes)(0), 1000 * (word.length + 1))
      // External output decoding only. The controller already wrote these bits.
      val marks = decodeUntilEnd(result.tapes(MARKS)).map(_.toInt)
      val prepared = decodeUntilEnd(result.tapes(A)).mkString
      MarkedRun(marks, prepared, result.steps, result.tapes, result.positions)
    }
  }

  object MarkedProgram {
    def apply(alphabet: String, ntapes: Int = 9): MarkedProgram = new MarkedProgram(alphabet.map(_.toString), ntapes)
  }

  /** Cells 1, 2, ... of a tape up to (excluding) the first `END`. */
  def decodeUntilEnd(tape: Tape): Vector[String] = {
    val out = Vector.newBuilder[String]
    var i = 1
    while (tape.read(i) != END) {
      out += tape(i)
      i += 1
    }
    out.result()
  }

  /** Python の `build_marked_program(alphabet="ab")`。 */
  def buildMarkedProgram(alphabet: String = "ab"): MarkedProgram = {
    if (alphabet.contains('#')) {
      throw new IllegalArgumentException("# is the private separator")
    }
    val kernel = buildProgram(alphabet + "#")
    val p = MarkedProgram(alphabet + "#", ntapes = 9)
    p.sourceAlphabet = alphabet.map(_.toString).toVector
    p.copyCodeFrom(kernel)
    val letters = p.sourceAlphabet
    // Expand every candidate move to a corresponding MARKS move. This
    // transformation touches kernel instructions only, not setup instructions.
    for ((row, q) <- kernel.instructions.zipWithIndex) {
      row match {
        case Move(A, direction, next) => p.set(q, Move(A, direction, p.move(MARKS, direction, next)))
        case Emit(next) => p.set(q, Write(MARKS, "1", next))
        case _ => ()
      }
    }

    def rewind(tape: Int, symbols: Seq[String], k: Int): Int = {
      val loop = p.reserve()
      p.branch(tape, choices((Seq(LEFT -> k) ++ symbols.map(s => s -> p.move(tape, -1, loop)))*), loop)
      loop
    }

    def writeBoth(symbol: String, k: Int): Int = p.write(A, symbol, p.write(B, symbol, k))

    def nextBoth(k: Int): Int = p.move(A, 1, p.move(B, 1, k))

    val prepared = letters ++ Seq("#", END)
    // B must scan the first prepared symbol; A and MARKS must scan ^.
    val ready = rewind(A, prepared,
      rewind(B, prepared,
        rewind(MARKS, Seq("0", END), p.move(B, 1, kernel.start))))
    val finish = writeBoth(END, ready)
    val forward = p.reserve()
    val backward = p.reserve()
    p.branch(SOURCE, choices((Seq(LEFT -> finish) ++ letters.map { symbol =>
      symbol -> writeBoth(symbol, nextBoth(p.move(SOURCE, -1, backward)))
    })*), backward)
    val turn = p.write(MARKS, END,
      writeBoth("#", nextBoth(p.move(SOURCE, -1, backward))))
    p.branch(SOURCE, choices((Seq(END -> turn) ++ letters.map { symbol =>
      symbol -> writeBoth(symbol, p.write(MARKS, "0",
        nextBoth(p.move(MARKS, 1, p.move(SOURCE, 1, forward)))))
    })*), forward)
    val startCopy = nextBoth(p.move(MARKS, 1, p.move(SOURCE, 1, forward)))
    // Initialize C's delta(-1) encoding 010, then restore its head.
    val initC = p.write(C, "0", p.move(C, 1, p.write(C, "1",
      p.move(C, 1, p.write(C, "0", p.move(C, -1,
        p.move(C, -1, startCopy)))))))
    var init = initC
    for (tape <- Seq(A, B, MARKS, S, T, BACK, FRONT)) {
      init = p.write(tape, LEFT, init)
    }
    p.start = init
    p.validate()
    p
  }
}
