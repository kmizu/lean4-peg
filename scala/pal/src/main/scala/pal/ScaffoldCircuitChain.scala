package pal

import Expr.{TRUE, FALSE}
import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction as and, disjunction as or, neg as not, choose}
import ScaffoldCircuitInput.PlaceHead
import FppFinite.{LEFT, BLANK}

/** Lower semiperiod verification and actual continuation counters to equations. */
object ScaffoldCircuitChain {
  val MODES: Vector[String] = Vector("idle", "copy", "back", "watch", "broken")

  final class Chain(val circuit: Circuit, pool: StackPool, val center: PlaceHead,
                    val walker: PlaceHead, val verifier: PlaceHead, val radius: Counter) {
    private val symbols = Vector(BLANK, LEFT, "a", "b", "s", "F:a", "F:b", "F:s", "T:a", "T:b", "T:s")
    val period: Tape = new Tape(circuit, "ch.p", symbols, slots = 4, blank = BLANK)
    val h: Counter = new Counter(pool, "ch.h")
    val lag: Counter = new Counter(pool, "ch.lag")
    val distance: Counter = new Counter(pool, "ch.dist")
    val boundary: Counter = new Counter(pool, "ch.bound")
    val last: Counter = new Counter(pool, "ch.last")
    val margin: Counter = new Counter(pool, "ch.margin")
    val cycle: Counter = new Counter(pool, "ch.cycle")
    var mode: Value[String] = circuit.get(PREVIOUS, "ch.mode", MODES, "idle")
    var direction: Value[Int] = circuit.get(PREVIOUS, "ch.dir", Vector(-1, 1), 1)
    var phase: Value[Int] = circuit.get(PREVIOUS, "ch.phase", (0 until 5).toVector, 0)
    var only: Expr = circuit.get(PREVIOUS, "ch.only", Vector(false, true), false).eqTo(true)

    def setMode(value: String, enabled: Expr): Unit = { mode = Value.select(enabled, Value.constant(value), mode) }

    def start(enabled: Expr = TRUE): Unit = {
      val symbol = center.read()
      circuit.require(not(symbol.eqTo(None)), enabled)
      val marked = Value(symbol.cases.collect { case (s, guard) if s != None => ("F:" + s.toString) -> guard })
      period.reset(enabled)
      period.write(marked, enabled)
      walker.copyFrom(center, enabled)
      verifier.copyFrom(center, enabled)
      Vector(h, distance, boundary, last, cycle).foreach(_.reset(enabled))
      only = choose(enabled, FALSE, only)
      lag.copyFrom(radius, enabled)
      margin.copyFrom(radius, enabled)
      setMode("copy", enabled)
      direction = Value.select(enabled, Value.constant(1), direction)
      phase = Value.select(enabled, Value.constant(0), phase)
    }

    def prediction(): Value[Any] = {
      val ready = and(mode.eqTo("watch"), lag.zero())
      Value.select(ready, period.focus.map(_.toString.last), Value.constant(None))
    }

    def cycleEnd(): Expr = {
      val below = cycle.pos.pool.pointer(cycle.pos.top, cycle.pos.tag, "below")
      and(cycle.positive(), not(below.present()))
    }

    def canShift(): Expr = and(mode.eqTo("watch"), lag.zero(), phase.eqTo(4),
      choose(only, cycleEnd(), not(margin.negative())))

    def checkPair(left: Value[Any], enabled: Expr = TRUE): Unit = {
      val checking = and(enabled, only, mode.eqTo("watch"), lag.zero())
      val same = left.equal(prediction())
      circuit.require(and(cycle.positive(), choose(cycleEnd(), not(same), same)), checking)
    }

    def beginShift(enabled: Expr = TRUE): Unit = {
      only = choose(enabled, TRUE, only)
      cycle.reset(enabled)
    }

    def consume(enabled: Expr): Expr = {
      verifier.right(enabled)
      val token = period.focus
      val same = verifier.read().equal(token.map(_.toString.last))
      val matched = and(enabled, same)
      setMode("broken", and(enabled, not(same)))
      distance.inc(matched)
      val first = or(token.cases.collect { case (value, guard) if value.toString.startsWith("F:") => guard }*)
      val lastToken = or(token.cases.collect { case (value, guard) if value.toString.startsWith("T:") => guard }*)
      val boundaryEvent = and(matched, or(first, lastToken))
      last.copyFrom(boundary, boundaryEvent)
      boundary.copyFrom(distance, boundaryEvent)
      phase = Value.select(boundaryEvent, phase.map(n => math.min(4, n + 1)), phase)
      direction = Value.select(boundaryEvent, Value.select(first, Value.constant(1), Value.constant(-1)), direction)
      period.move(1, and(matched, direction.eqTo(1)))
      period.move(-1, and(matched, direction.eqTo(-1)))
      matched
    }

    def matched(enabled: Expr = TRUE): Unit = {
      margin.inc(enabled)
      cycle.dec(and(enabled, only))
      val ready = and(mode.eqTo("watch"), lag.zero())
      consume(and(enabled, ready))
      lag.inc(and(enabled, not(ready)))
    }

    def shiftOne(enabled: Expr = TRUE): Unit = {
      Vector(distance, boundary, last, margin).foreach(_.dec(enabled))
      cycle.inc(enabled)
      cycle.inc(enabled)
    }

    def step(answer: Tape, enabled: Expr = TRUE): Unit = {
      val copying = and(enabled, mode.eqTo("copy"))
      val backing = and(enabled, mode.eqTo("back"))
      val watching = and(enabled, mode.eqTo("watch"))
      val more = answer.focus.eqTo("1")
      val copy = and(copying, more)
      val done = and(copying, not(more))
      circuit.require(and(answer.focus.eqTo(LEFT), h.positive()), done)
      answer.move(-1, copy)
      h.inc(copy)
      for (_ <- 0 until 4) { margin.dec(copy) }
      walker.left(copy)
      val symbol = walker.read()
      circuit.require(not(symbol.eqTo(None)), copy)
      period.move(1, copy)
      period.write(Value(symbol.cases.collect { case (s, guard) if s != None => s.toString -> guard }), copy)
      // Only plain endpoint letters are reachable under this guard.
      val marked = Value(period.focus.cases.collect { case (s, guard) if "abs".contains(s.toString) => ("T:" + s.toString) -> guard })
      period.write(marked, done)
      setMode("back", done)

      val first = or(period.focus.cases.collect { case (value, guard) if value.toString.startsWith("F:") => guard }*)
      period.move(1, and(backing, first))
      period.move(-1, and(backing, not(first)))
      setMode("watch", and(backing, first))
      val caught = consume(and(watching, lag.positive()))
      lag.dec(caught)
    }

    def commit(): Unit = {
      period.commit()
      Vector(h, lag, distance, boundary, last, margin, cycle).foreach(_.commit())
      circuit.put("ch.mode", mode)
      circuit.put("ch.dir", direction)
      circuit.put("ch.phase", phase)
      circuit.put("ch.only", Value.select(only, Value.constant(true), Value.constant(false)))
    }
  }
}
