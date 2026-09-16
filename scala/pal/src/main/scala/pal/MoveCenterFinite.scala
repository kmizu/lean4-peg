package pal

import FppFinite.*
import FppFinite.Instruction.*
import FppSubroutine.{buildMarkedProgram, SOURCE, MARKS}
import FppReuse.makeReusable
import DpSearchFinite.WINDOW

/** Offline local center selection for the nonchain move, not the full move.
  *
  * WINDOW has a nonempty interval with ML/MR (or MLR) boundary tags; its head
  * starts at the right boundary. Interior C/P annotations may be present.
  * All scratch starts blank at zero. The controller copies the reversed
  * interval locally, runs FPP, selects its longest odd palindrome prefix and
  * moves WINDOW to the corresponding suffix center. It leaves C and RR tags,
  * preserving the underlying text and cells outside the interval.
  *
  * No coordinate arithmetic remains in the finite instruction table. Scratch
  * is erased and its heads restored to zero before return, permitting reuse.
  * Preparing boundaries, multihead repositioning and main1 replay remain outer
  * operations. Mid-procedure cancellation is not provided.
  *
  * Python 原典: `move_center_finite.py`。
  */
object MoveCenterFinite {
  val FIRST: String = "first:1"

  /** Tag a boundary symbol: `ML:` left, `MR:` right, `MLR:` both. */
  def boundary(symbol: String, left: Boolean = false, right: Boolean = false): String = {
    if (!left && !right) {
      throw new IllegalArgumentException("at least one boundary required")
    }
    (if (left && right) { "MLR:" } else if (left) { "ML:" } else { "MR:" }) + symbol
  }

  /** The source symbol under any tag. Every source symbol is one character, including ':' itself. */
  def decode(symbol: String): String = symbol.takeRight(1)

  /** Python の `build_move_center_program(alphabet="abs")`。
    *
    * @param bodySymbols `FppReuse.makeReusable` に渡す掃除記号の順序（ゴールデン再生成用）。
    */
  def buildMoveCenterProgram(alphabet: String = "abs", bodySymbols: Option[Seq[String]] = None): Program = {
    val baseKernel = buildMarkedProgram(alphabet)
    val kernel = makeReusable(baseKernel, bodySymbols)
    val p = new Program(kernel.alphabet, ntapes = WINDOW + 1)
    p.sourceAlphabet = alphabet.map(_.toString).toVector
    p.copyCodeFrom(kernel)
    val letters = p.sourceAlphabet
    val finished = p.add(Halt)
    p.finished = Some(finished)
    // Kernel cleanup preserves SOURCE; erase that local copy too, leaving
    // only the annotation changes on WINDOW as externally visible output.
    val clearSource = p.reserve()
    val backSource = p.reserve()
    p.branch(SOURCE, choices(LEFT -> p.write(SOURCE, BLANK, finished),
      BLANK -> p.move(SOURCE, -1, backSource)), backSource)
    p.branch(SOURCE, choices((Seq(BLANK -> p.move(SOURCE, -1, backSource)) ++ (letters :+ END).map { s =>
      s -> p.write(SOURCE, BLANK, p.move(SOURCE, 1, clearSource))
    })*), clearSource)
    for (q <- baseKernel.code.size until kernel.code.size) {
      if (kernel.instruction(q) == Halt) {
        p.set(q, Move(SOURCE, 1, clearSource))
      }
    }
    val cleanup = kernel.cleanup.get
    val markCenter = p.branch(WINDOW, choices((
      letters.map(s => s -> p.write(WINDOW, "C:" + s, cleanup)) ++
      letters.map(s => ("RR:" + s) -> p.write(WINDOW, "CRR:" + s, cleanup)))*))

    // At the chosen odd prefix length ell, two unit MARKS moves correspond
    // to one unit WINDOW move. FIRST identifies ell=1 without an address test.
    val reduce = p.reserve()
    val shorter = p.move(MARKS, -1, p.move(MARKS, -1, p.move(WINDOW, -1, reduce)))
    p.branch(MARKS, choices(FIRST -> p.write(MARKS, "1", markCenter),
      "0" -> shorter, "1" -> shorter), reduce)
    val forward = Array(p.reserve(), p.reserve())
    val backward = Array(p.reserve(), p.reserve())
    for (parity <- Seq(0, 1)) {
      val before = p.move(MARKS, -1, backward(1 - parity))
      var backChoices = choices("0" -> before, "1" -> (if (parity == 1) { reduce } else { before }))
      if (parity == 1) {
        backChoices = backChoices.updated(FIRST, reduce)
      }
      p.branch(MARKS, backChoices, backward(parity))
      val after = p.move(MARKS, 1, forward(1 - parity))
      p.branch(MARKS, choices("0" -> after, "1" -> after, END -> before), forward(parity))
    }
    val inspect = p.move(MARKS, 1, p.write(MARKS, FIRST,
      p.move(MARKS, 1, forward(0))))
    for ((row, q) <- baseKernel.instructions.zipWithIndex) {
      if (row == Halt) {
        p.set(q, Read(MARKS, choices(LEFT -> inspect)))
      }
    }

    // FPP requires SOURCE at its origin; WINDOW remains at RR while it runs.
    val rewindSource = p.reserve()
    p.branch(SOURCE, choices((Seq(LEFT -> kernel.start) ++ (letters :+ END).map { s =>
      s -> p.move(SOURCE, -1, rewindSource)
    })*), rewindSource)
    val restoreWindow = p.reserve()
    val ordinary = for {
      s <- letters
      tag <- Seq("", "C:", "P:", "RR:", "CRR:", "ML:")
    } yield (tag + s) -> s
    val right = for {
      s <- letters
      tag <- Seq("MR:", "MLR:")
    } yield (tag + s) -> s
    p.branch(WINDOW, choices((
      ordinary.map { case (token, s) => token -> p.write(WINDOW, s, p.move(WINDOW, 1, restoreWindow)) } ++
      right.map { case (token, s) => token -> p.write(WINDOW, "RR:" + s, rewindSource) })*), restoreWindow)

    val copy = p.reserve()
    val finishCopy = p.write(SOURCE, END, restoreWindow)
    val tokens = for {
      s <- letters
      tag <- Seq("", "C:", "P:", "RR:", "CRR:", "ML:", "MR:", "MLR:")
    } yield (tag + s) -> s
    p.branch(WINDOW, choices(tokens.map { case (token, s) =>
      token -> p.write(SOURCE, s, p.move(SOURCE, 1,
        if (token.startsWith("ML:") || token.startsWith("MLR:")) { finishCopy }
        else { p.move(WINDOW, -1, copy) }))
    }*), copy)
    p.start = p.write(SOURCE, LEFT, p.move(SOURCE, 1, copy))
    p.validate()
    p
  }
}
