package pal

import Expr.{TRUE, FALSE}
import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction as and, disjunction as or, neg as not, choose}
import ScaffoldCircuitInput.PlaceHead
import ScaffoldCircuitProgram.Program
import FppFinite.{LEFT, END}
import FppSubroutine.SOURCE
import DpFinite.LOWER

/** Predicated lowering of the match-paced DP search used by scaffold_galil. */
object ScaffoldCircuitSearch {
  val MODES: Vector[String] = Vector("idle", "grow", "lower", "lower_home", "copy", "home", "run",
    "found", "missed", "wait", "double")

  final class Search(val circuit: Circuit, val program: Program, pool: StackPool,
                     val center: PlaceHead, val walker: PlaceHead, val radius: Counter) {
    val lower: Counter = new Counter(pool, "sp.lo")
    val span: Counter = new Counter(pool, "sp.span")
    val work: Counter = new Counter(pool, "sp.work")
    val debt: Counter = new Counter(pool, "sp.debt")
    var mode: Value[String] = circuit.get(PREVIOUS, "sp.mode", MODES, "idle")
    var finalStage: Expr = circuit.get(PREVIOUS, "sp.final", Vector(false, true), false).eqTo(true)
    var quarter: Value[Int] = circuit.get(PREVIOUS, "sp.quarter", (0 until 4).toVector, 0)

    def active(): Expr = not(or(mode.eqTo("idle"), mode.eqTo("found"), mode.eqTo("missed")))
    def setMode(value: String, enabled: Expr): Unit = { mode = Value.select(enabled, Value.constant(value), mode) }

    def start(lowerBound: Counter, enabled: Expr = TRUE): Unit = {
      circuit.require(and(not(lowerBound.negative()), not(radius.negative()), not(center.read().eqTo(None))), enabled)
      program.reset(enabled)
      lower.copyFrom(lowerBound, enabled)
      work.copyFrom(lowerBound, enabled)
      work.inc(and(enabled, work.zero()))
      span.reset(enabled)
      debt.positiveStack.copyFrom(radius.negativeStack, enabled)
      debt.negativeStack.copyFrom(radius.positiveStack, enabled)
      setMode("grow", enabled)
      finalStage = choose(enabled, FALSE, finalStage)
      quarter = Value.select(enabled, Value.constant(0), quarter)
    }

    def advanceMatch(enabled: Expr = TRUE): Unit = {
      circuit.require(active(), enabled)
      radius.inc(enabled)
      debt.dec(enabled)
    }

    def prepare(enabled: Expr): Unit = {
      program.reset(enabled)
      walker.copyFrom(center, enabled)
      work.copyFrom(lower, enabled)
      val tape = program.tapes(LOWER)
      tape.write(Value.constant(LEFT), enabled)
      tape.move(1, enabled)
      setMode("lower", enabled)
      finalStage = choose(enabled, FALSE, finalStage)
    }

    def double(enabled: Expr): Unit = {
      work.copyFrom(span, enabled)
      span.reset(enabled)
      quarter = Value.select(enabled, Value.constant(0), quarter)
      setMode("double", enabled)
    }

    def runStep(enabled: Expr): Unit = {
      program.step(enabled)
      val finished = and(enabled, program.done)
      circuit.require(not(debt.negative()), finished)
      val found = and(finished, program.pc.eqTo(program.kernel.found.get))
      val missed = and(finished, not(found), finalStage)
      val nextStage = and(finished, not(found), not(finalStage), debt.zero())
      val waitForMatch = and(finished, not(found), not(finalStage), not(debt.zero()))
      setMode("found", found)
      setMode("missed", missed)
      double(nextStage)
      setMode("wait", waitForMatch)
    }

    def step(enabled: Expr = TRUE): Unit = {
      val dispatch = MODES.map(name => name -> and(enabled, mode.eqTo(name))).toMap
      val sourceTape = program.tapes(SOURCE)
      val lowerTape = program.tapes(LOWER)
      val growing = work.positive()
      val grow = and(dispatch("grow"), growing)
      work.dec(grow)
      for (_ <- 0 until 8) { span.inc(grow) }
      for (_ <- 0 until 2) { debt.inc(grow) }
      prepare(and(dispatch("grow"), not(growing)))

      val loadingPositive = work.positive()
      val loading = and(dispatch("lower"), loadingPositive)
      lowerTape.write(Value.constant("1"), loading)
      lowerTape.move(1, loading)
      work.dec(loading)
      val loaded = and(dispatch("lower"), not(loadingPositive))
      lowerTape.write(Value.constant(END), loaded)
      setMode("lower_home", loaded)

      val lowerHome = lowerTape.focus.eqTo(LEFT)
      val beginCopy = and(dispatch("lower_home"), lowerHome)
      sourceTape.write(Value.constant(LEFT), beginCopy)
      sourceTape.move(1, beginCopy)
      work.copyFrom(span, beginCopy)
      work.inc(beginCopy)
      setMode("copy", beginCopy)
      lowerTape.move(-1, and(dispatch("lower_home"), not(lowerHome)))

      val symbol = walker.read()
      val end = or(symbol.eqTo(None), work.zero())
      val stopCopy = and(dispatch("copy"), end)
      sourceTape.write(Value.constant(END), stopCopy)
      finalStage = choose(stopCopy, symbol.eqTo(None), finalStage)
      setMode("home", stopCopy)
      val copying = and(dispatch("copy"), not(end))
      sourceTape.write(Value(symbol.cases.collect { case (s, guard) if s != None => s.toString -> guard }), copying)
      sourceTape.move(1, copying)
      walker.left(copying)
      work.dec(copying)

      val sourceHome = sourceTape.focus.eqTo(LEFT)
      val startRun = and(dispatch("home"), sourceHome)
      program.start(startRun)
      setMode("run", startRun)
      sourceTape.move(-1, and(dispatch("home"), not(sourceHome)))
      runStep(dispatch("run"))

      circuit.require(not(debt.negative()), dispatch("wait"))
      double(and(dispatch("wait"), debt.zero()))

      val doublingPositive = work.positive()
      val doubling = and(dispatch("double"), doublingPositive)
      val quarterEnd = quarter.eqTo(3)
      work.dec(doubling)
      span.inc(doubling)
      span.inc(doubling)
      quarter = Value.select(doubling, quarter.map(n => (n + 1) % 4), quarter)
      debt.inc(and(doubling, quarterEnd))
      prepare(and(dispatch("double"), not(doublingPositive)))
    }

    def tick(enabled: Expr = TRUE, quantum: Int = 64): Unit = {
      val running = mode.eqTo("run")
      step(enabled)
      for (_ <- 1 until quantum) { runStep(and(enabled, running, mode.eqTo("run"))) }
    }

    def commit(): Unit = {
      program.commit()
      Vector(lower, span, work, debt).foreach(_.commit())
      circuit.put("sp.mode", mode)
      circuit.put("sp.final", Value.select(finalStage, Value.constant(true), Value.constant(false)))
      circuit.put("sp.quarter", quarter)
    }
  }
}
