package pal

import scala.collection.mutable

import FppFinite.*
import FppFinite.Instruction.*
import FppSubroutine.SOURCE
import DpFinite.LOWER

/** Finite cleanup and cancellation entries for the FPP/DP fresh-tape kernels.
  *
  * Requires their dense-prefix tape invariant, not arbitrary dirty tapes.
  * Cleanup destroys consumed/cancelled output, preserves input contents, and
  * returns every head to its origin. All work uses ordinary local instructions.
  * The finite cancel-entry dictionary is indexed by control state, not position.
  * Cancellation is allowed in the job/bootstrap, not during cleanup itself.
  *
  * Python 原典: `fpp_reuse.py`。
  */
object FppReuse {
  val C_ORIGIN: String = "^0"

  /** The symbols a cleanup sweep may meet on a tape body, in the order the sweep
    * instructions are generated.
    *
    * Python 版は `set(program.alphabet) | {END, BLANK, "0", "1"}` を反復するので、その順序は
    * `PYTHONHASHSEED` に依存する（状態番号と分岐表のキー順に影響し、checked-in の
    * `generated/<name>-controller.json` は dp-search 系が `PYTHONHASHSEED=0` の順序、
    * move-center はどの seed とも一致しない順序で書かれている）。ここでは既定を
    * 決定的な「アルファベット順 → END, BLANK, 0, 1」とし、ゴールデン再生成のために
    * 明示的な順序を渡せるようにする（`ControllerArtifacts`）。順序は状態番号だけを変え、
    * 実行トレースは変えない（`ControllerArtifactsSuite` で確認）。
    */
  def defaultBodySymbols(alphabet: Seq[String]): Vector[String] =
    (alphabet ++ Seq(END, BLANK, "0", "1")).distinct.toVector

  /** Python の `make_reusable(program)`。
    *
    * @param bodySymbols `reset_tape` が走査する記号の順序（既定は `defaultBodySymbols`）。
    */
  def makeReusable(program: Program, bodySymbols: Option[Seq[String]] = None): Program = {
    if (program.ntapes != 9 && program.ntapes != 12) {
      throw new IllegalArgumentException("expected a marked FPP or DP kernel")
    }
    val p = new Program(program.alphabet, program.ntapes)
    p.sourceAlphabet = program.sourceAlphabet
    p.copyCodeFrom(program)
    p.found = program.found
    p.inputs = if (p.ntapes == 12) { Vector(SOURCE, LOWER) } else { Vector(SOURCE) }
    p.scratch = (0 until p.ntapes).filterNot(p.inputs.contains).toVector

    tagSeedWrite(p, program.start)
    for ((row, q) <- p.instructions.zipWithIndex) {
      row match {
        case Read(C, choices) if choices.contains("0") =>
          p.set(q, Read(C, choices.updated(C_ORIGIN, choices("0"))))
        case _ => ()
      }
    }

    val done = p.add(Halt)
    val body = bodySymbols.map(_.toVector).getOrElse(defaultBodySymbols(program.alphabet))
    val bodyOrder = body.filterNot(_ == BLANK) // Python: `if symbol != BLANK` on the same set

    def resetTape(tape: Int, erase: Boolean, k: Int): Int = {
      val root = if (tape == C) { C_ORIGIN } else { LEFT }
      val seek = p.reserve()
      val atRoot = if (erase) {
        val clear = p.reserve()
        val back = p.reserve()
        p.branch(tape, choices(root -> p.write(tape, BLANK, k),
          BLANK -> p.move(tape, -1, back)), back)
        p.branch(tape, choices((Seq(BLANK -> p.move(tape, -1, back)) ++ bodyOrder.map { symbol =>
          symbol -> p.write(tape, BLANK, p.move(tape, 1, clear))
        })*), clear)
        p.move(tape, 1, clear)
      } else {
        k
      }
      p.branch(tape, choices((Seq(root -> atRoot) ++ body.map { symbol =>
        symbol -> p.move(tape, -1, seek)
      })*), seek)
      seek
    }

    var cleanup = done
    for (tape <- (0 until p.ntapes).reverse) {
      cleanup = resetTape(tape, p.scratch.contains(tape), cleanup)
    }
    p.cleanup = Some(cleanup)

    def bootstrap(k: Int): (Int, Vector[Int]) = {
      val states = Vector.newBuilder[Int]
      var next = k
      for (tape <- p.scratch.reverse) {
        next = p.write(tape, if (tape == C) { C_ORIGIN } else { LEFT }, next)
        states += next
      }
      (next, states.result())
    }

    // No bootstrap move occurs. Even a partly bootstrapped job can safely
    // finish writing all origin markers, then enter the uniform cleanup.
    val (cancelBootstrap, _) = bootstrap(cleanup)
    val (start, bootstrapStates) = bootstrap(program.start)
    p.start = start
    for (q <- program.code.indices) {
      p.cancelEntries(q) = cleanup
    }
    for (q <- bootstrapStates) {
      p.cancelEntries(q) = cancelBootstrap
    }
    p.validate()
    p
  }

  /** The first C seed write is reached through a fixed, write-only startup.
    * Tag that origin so cleanup can find it by a finite symbol test. Later
    * C writes only materialize newly visited blank cells beyond the seed.
    */
  private def tagSeedWrite(p: Program, startState: Int): Unit = {
    var q = startState
    val seen = mutable.HashSet.empty[Int]
    var searching = true
    while (searching) {
      if (seen.contains(q)) {
        throw new IllegalArgumentException("unexpected startup cycle")
      }
      seen += q
      p.instruction(q) match {
        case Write(C, "0", next) =>
          p.set(q, Write(C, C_ORIGIN, next))
          searching = false
        case Write(_, _, next) =>
          q = next
        case _ =>
          throw new IllegalArgumentException("unexpected pre-seed startup instruction")
      }
    }
  }
}
