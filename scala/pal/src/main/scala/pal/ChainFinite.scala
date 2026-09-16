package pal

import scala.collection.immutable.VectorMap

import FppFinite.*
import FppFinite.Instruction.*
import DpSearchFinite.{buildSearchProgram, WINDOW, STATUS, centerSymbol, periodSymbol}

/** Finite right-dp / three-way chain monitor, composed after local DP search.
  *
  * The caller supplies right-side places C+1,C+2,... through a one-cell PORT,
  * only at a ready state. Setup is offline. Each subsequent place takes
  * constant local work: PERIOD bounces along a marked semiperiod, while
  * WINDOW moves left for ordinary palindrome matching. This implements the
  * branch decisions, not the outer center shift/restart/move scheduler.
  *
  * Python 原典: `chain_finite.py`。
  */
object ChainFinite {
  val PERIOD: Int = 16
  val PORT: Int = 17

  /** The outcome halt states, in the order Python's `build_chain_program` allocates them. */
  val OUTCOME_NAMES: Vector[String] = Vector("palindrome", "failed_right_dp", "restart_search",
    "chain_shift", "nonchain_move", "end_chain", "end_pending")

  /** The first symbol of the copied semiperiod (PERIOD bounces right from here). */
  def first(symbol: String): String = "F:" + symbol

  /** The last symbol of the copied semiperiod (PERIOD bounces left from here). */
  def last(symbol: String): String = "T:" + symbol

  /** Python の `build_chain_program(alphabet="abs")`。
    *
    * @param bodySymbols `FppReuse.makeReusable` に渡す掃除記号の順序（ゴールデン再生成用）。
    */
  def buildChainProgram(alphabet: String = "abs", bodySymbols: Option[Seq[String]] = None): Program = {
    val search = buildSearchProgram(alphabet, bodySymbols)
    val p = new Program(search.alphabet, ntapes = 18)
    p.sourceAlphabet = search.sourceAlphabet
    p.scalarTapes = Some(Vector(STATUS, PORT))
    p.copyCodeFrom(search)
    val letters = p.sourceAlphabet
    p.outcomes(search.missed.get) = "no_chain"
    val outcome: Map[String, Int] = OUTCOME_NAMES.map { name =>
      val state = p.add(Halt)
      p.outcomes(state) = name
      name -> state
    }.toMap
    // These remain available to composition clients expecting search labels.
    p.found = search.found
    p.missed = search.missed
    val ready: VectorMap[(Int, Int), Int] = VectorMap.from(for {
      phase <- 0 until 5
      direction <- Seq(-1, 1)
    } yield (phase, direction) -> p.reserve())
    p.ready = ready.values.toSet
    p.confirmedReady = ready.collect { case ((phase, _), q) if phase == 4 => q }.toSet
    val tokenLetters: VectorMap[String, String] = VectorMap.from(for {
      s <- letters
      token <- Seq(s, centerSymbol(s), periodSymbol(s))
    } yield token -> s)
    val periodLetters: VectorMap[String, String] = VectorMap.from(for {
      s <- letters
      token <- Seq(s, first(s), last(s))
    } yield token -> s)

    for (((phase, direction), q) <- ready) {
      var portChoices = choices(BLANK -> q, END -> p.write(PORT, BLANK,
        if (phase == 4) { outcome("end_chain") } else { outcome("end_pending") }))
      for (right <- letters) {
        var comparePeriod = VectorMap.empty[String, Int]
        for ((token, prediction) <- periodLetters) {
          val (nextDirection, nextPhase) =
            if (token.startsWith("F:")) { (1, math.min(4, phase + 1)) }
            else if (token.startsWith("T:")) { (-1, math.min(4, phase + 1)) }
            else { (direction, phase) }
          val advance = p.move(PERIOD, nextDirection, ready((nextPhase, nextDirection)))
          val boundary = p.branch(WINDOW, choices((Seq(LEFT -> outcome("palindrome")) ++
            tokenLetters.keys.map(_ -> advance))*))
          val matching = p.move(WINDOW, -1, boundary)
          var compareLeft = VectorMap.empty[String, Int]
          for ((symbol, left) <- tokenLetters) {
            val target =
              if (left == right && right == prediction) { matching }
              else if (phase < 4) { outcome("failed_right_dp") }
              else if (left == right) { outcome("restart_search") }
              else if (prediction == right) { outcome("chain_shift") }
              else { outcome("nonchain_move") }
            compareLeft = compareLeft.updated(symbol, p.write(PORT, BLANK, target))
          }
          comparePeriod = comparePeriod.updated(token, p.branch(WINDOW, compareLeft))
        }
        portChoices = portChoices.updated(right, p.branch(PERIOD, comparePeriod))
      }
      p.branch(PORT, portChoices, q)
    }

    // Read the first marked semiperiod directly from the DP result: C..C-h.
    // A local bouncing reader avoids O(h) rewinds between incoming places.
    val backPeriod = p.reserve()
    val backWindow = p.reserve()
    val copyPeriod = p.reserve()
    val startMatching = p.move(WINDOW, -1, p.move(PERIOD, 1, ready((0, 1))))
    p.branch(WINDOW, choices((letters.map(s => centerSymbol(s) -> startMatching) ++
      letters.flatMap(s => Seq(s, periodSymbol(s)).map(token => token -> p.move(WINDOW, 1, backWindow))))*), backWindow)
    p.branch(PERIOD, choices((Seq(LEFT -> p.move(PERIOD, 1, backWindow)) ++
      periodLetters.keys.map(token => token -> p.move(PERIOD, -1, backPeriod)))*), backPeriod)
    p.branch(WINDOW, choices((letters.map(s => periodSymbol(s) -> p.write(PERIOD, last(s), backPeriod)) ++
      letters.map(s => s -> p.write(PERIOD, s, p.move(PERIOD, 1, p.move(WINDOW, -1, copyPeriod)))))*), copyPeriod)
    val initialSymbol = p.branch(WINDOW, choices(letters.map { s =>
      centerSymbol(s) -> p.write(PERIOD, first(s), p.move(PERIOD, 1, p.move(WINDOW, -1, copyPeriod)))
    }*))
    p.set(search.found.get, Write(PERIOD, LEFT, p.move(PERIOD, 1, initialSymbol)))
    p.start = p.write(PORT, BLANK, search.start)
    p.validate()
    p
  }
}
