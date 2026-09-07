package pal

import FppFinite.*
import FppFinite.Instruction.*
import FppSubroutine.SOURCE
import DpFinite.{buildDpProgram, LOWER, OUTPUT}
import FppReuse.makeReusable

/** Local doubling-window search for Galil's dp(C,r), without its scheduler.
  *
  * WINDOW contains ^prefix suffix$, with the last prefix cell center-tagged;
  * its head starts at that tag. LOWER is ^1^r$, head at its left marker.
  * All other tapes start blank at zero. Only finite read/write/unit-move
  * instructions execute. Success marks C-h, C-2h, C-3h, C-4h and returns h
  * in unary. Both success and failure restore WINDOW's head to C.
  *
  * This is an offline search component. There are no match-paced waiting
  * barriers, outer cancellation entries, or right-chain confirmation yet.
  *
  * Python 原典: `dp_search_finite.py`。
  */
object DpSearchFinite {
  val WINDOW: Int = 12
  val SPAN: Int = 13
  val TEMP: Int = 14
  val STATUS: Int = 15

  def centerSymbol(symbol: String): String = "C:" + symbol

  def periodSymbol(symbol: String): String = "P:" + symbol

  /** Python の `build_search_program(alphabet="abs")`。
    *
    * @param bodySymbols `FppReuse.makeReusable` に渡す掃除記号の順序（ゴールデン再生成用）。
    */
  def buildSearchProgram(alphabet: String = "abs", bodySymbols: Option[Seq[String]] = None): Program = {
    val kernel = buildDpProgram(alphabet)
    val reusable = makeReusable(kernel, bodySymbols)
    val p = Program(alphabet + "#", ntapes = 16)
    p.sourceAlphabet = alphabet.map(_.toString).toVector
    p.copyCodeFrom(reusable)
    val letters = p.sourceAlphabet
    val found = p.add(Halt)
    val missed = p.add(Halt)
    p.found = Some(found)
    p.missed = Some(missed)

    def rewind(tape: Int, symbols: Seq[String], k: Int): Int = {
      val q = p.reserve()
      p.branch(tape, choices((Seq(LEFT -> k) ++ symbols.map(s => s -> p.move(tape, -1, q)))*), q)
      q
    }

    /** Walk WINDOW right until the centre tag, then continue at `k`. */
    def center(k: Int): Int = {
      val q = p.reserve()
      p.branch(WINDOW, choices((letters.map(s => centerSymbol(s) -> k) ++
        (Seq(LEFT) ++ letters ++ letters.map(periodSymbol)).map(s => s -> p.move(WINDOW, 1, q)))*), q)
      q
    }

    def push(tape: Int, symbol: String, k: Int): Int = p.move(tape, 1, p.write(tape, symbol, k))

    // Consume the unary answer four times to place the four semiperiod marks.
    // Rewinding OUTPUT is local; h is never decoded by runtime control.
    var markNext = center(found)
    for (_ <- 0 until 4) {
      val walk = p.reserve()
      val mark = p.branch(WINDOW, choices(letters.map { s =>
        s -> p.write(WINDOW, periodSymbol(s), rewind(OUTPUT, Seq("1", BLANK), markNext))
      }*))
      p.branch(OUTPUT, choices(BLANK -> mark,
        "1" -> p.move(WINDOW, -1, p.move(OUTPUT, 1, walk))), walk)
      markNext = p.move(OUTPUT, 1, walk)
    }
    val markStart = rewind(OUTPUT, Seq("1", BLANK), markNext)
    p.set(reusable.found.get, Read(STATUS, choices("N" -> markStart, "F" -> markStart)))

    val stage = p.reserve()
    // At stage entry all twelve kernel heads are at zero, scratch is blank,
    // WINDOW scans C, SPAN holds 1^ell, and TEMP is empty apart from its root.
    val copied = p.reserve()
    val copySymbol = p.reserve()
    val ready = rewind(SOURCE, letters :+ END,
      rewind(SPAN, Seq("1", BLANK), center(reusable.start)))
    val finish = p.write(SOURCE, END, ready)
    val finalStage = p.write(STATUS, "F", finish)
    val checkBudget = p.branch(SPAN, choices(
      "1" -> p.move(SPAN, 1, copySymbol), BLANK -> finish))
    val leftProbe = p.branch(WINDOW, choices((Seq(LEFT -> finalStage) ++ letters.map(_ -> checkBudget))*))
    p.branch(SOURCE, choices(letters.map { s =>
      s -> p.move(SOURCE, 1, p.move(WINDOW, -1, leftProbe))
    }*), copied)
    p.branch(WINDOW, choices(letters.flatMap { s =>
      Seq(s, centerSymbol(s)).map(token => token -> p.write(SOURCE, s, copied))
    }*), copySymbol)
    val startCopy = p.write(SOURCE, LEFT, p.move(SOURCE, 1,
      p.move(SPAN, 1, copySymbol)))
    p.branch(STATUS, choices("N" -> startCopy, "F" -> startCopy), stage)

    // Double SPAN through a distinct unary temporary tape. Each bit is read,
    // erased, and replaced through local moves; no growing integer register.
    val double = p.reserve()
    val back = p.reserve()
    val transfer = p.reserve()
    val resume = rewind(SPAN, Seq("1"), p.write(STATUS, "N", stage))
    p.branch(TEMP, choices(LEFT -> resume, "1" -> p.write(TEMP, BLANK,
      p.move(TEMP, -1, push(SPAN, "1", transfer)))), transfer)
    p.branch(SPAN, choices(LEFT -> transfer,
      BLANK -> p.move(SPAN, -1, back),
      "1" -> p.write(SPAN, BLANK, p.move(SPAN, -1, back))), back)
    p.branch(SPAN, choices(BLANK -> back,
      "1" -> push(TEMP, "1", push(TEMP, "1", p.move(SPAN, 1, double)))), double)
    val nextStage = p.move(SPAN, 1, double)

    // Kernel miss first clears its own work tapes and rewinds LOWER. Clear
    // the old SOURCE copy as well before building the next, larger window.
    val clear = p.reserve()
    val returnSource = p.reserve()
    val dispatch = p.branch(STATUS, choices("F" -> missed, "N" -> nextStage))
    p.branch(SOURCE, choices(LEFT -> dispatch,
      BLANK -> p.move(SOURCE, -1, returnSource)), returnSource)
    p.branch(SOURCE, choices((Seq(BLANK -> p.move(SOURCE, -1, returnSource)) ++ (letters :+ END).map { s =>
      s -> p.write(SOURCE, BLANK, p.move(SOURCE, 1, clear))
    })*), clear)
    val cleanupHalts = (kernel.code.size until reusable.code.size).filter(q => p.instruction(q) == Halt)
    assert(cleanupHalts.size == 1)
    p.set(cleanupHalts.head, Move(SOURCE, 1, clear))
    for ((row, q) <- kernel.instructions.zipWithIndex) {
      if (row == Halt && !kernel.found.contains(q)) {
        p.set(q, Read(STATUS, choices("N" -> reusable.cleanup.get, "F" -> reusable.cleanup.get)))
      }
    }

    // Initial ell = 8*max(r,1), as in the current behavioral reference.
    // The eight copies per bit are compile-time unrolling, not runtime loops.
    val initialize = p.reserve()
    val afterLower = rewind(LOWER, Seq("1", END), rewind(SPAN, Seq("1"), stage))
    var eightDefault = afterLower
    for (_ <- 0 until 8) {
      eightDefault = push(SPAN, "1", eightDefault)
    }
    val nonempty = p.branch(SPAN, choices(LEFT -> eightDefault, "1" -> afterLower))
    var eight = p.move(LOWER, 1, initialize)
    for (_ <- 0 until 8) {
      eight = push(SPAN, "1", eight)
    }
    p.branch(LOWER, choices("1" -> eight, END -> nonempty), initialize)
    p.start = p.write(STATUS, "N", p.write(TEMP, LEFT,
      p.write(SPAN, LEFT, p.move(LOWER, 1, initialize))))
    p.validate()
    p
  }
}
