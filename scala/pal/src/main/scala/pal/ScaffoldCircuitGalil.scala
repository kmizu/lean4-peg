package pal

import scala.collection.immutable.VectorMap
import Expr.{TRUE, FALSE}
import Ref.{NEW, PREVIOUS}
import ScaffoldCircuit.{conjunction as and, disjunction as or, neg as not, choose}
import ScaffoldCircuitInput.PlaceHead
import ScaffoldCircuitProgram.Program
import ScaffoldCircuitSearch.Search
import ScaffoldCircuitChain.Chain
import FppFinite.{LEFT, END}
import FppSubroutine.{buildMarkedProgram, SOURCE, MARKS}
import DpFinite.{buildDpProgram, OUTPUT, LOWER}

/** Whole Galil controller lowered into finite symbolic scaffold equations.
  *
  * `buildOnline` exposes read/work/output events and derives its internal match
  * clock from the construction quantum. The FIFO and whole-round wrapper is
  * supplied separately. The legacy `build` entry retains its old arrival clock
  * solely for comparison; it is not the raw-input PAL source. No length-dependent
  * host state or pointer equality is in the emitted machine.
  */
object ScaffoldCircuitGalil {
  val FIRST: String = "first:1"
  val MODES: Vector[String] = Vector("init", "scan", "shift", "copy", "home", "fpp", "mark_end", "choose", "rewind", "replay_start")

  /** Construction-time views, replacing Python's dynamically attached c.views. */
  final case class Views(heads: Vector[PlaceHead], counters: Vector[Counter], search: Search, chain: Chain, fpp: Program)
  final case class Built(circuit: Circuit, machine: Scaffold, views: Views)

  /** `a` and `b` are read events; `.` is an input-free work event. */
  def buildOnline(quantum: Int = 64, checkInvariants: Boolean = true, sharedCells: Boolean = false): (Circuit, Scaffold) = {
    val result = buildOnlineWithViews(quantum, checkInvariants, sharedCells)
    (result.circuit, result.machine)
  }

  def buildOnlineWithViews(quantum: Int = 64, checkInvariants: Boolean = true, sharedCells: Boolean = false): Built = {
    val timing = GalilClock.derive(quantum)
    buildWithViews(quantum, timing.matchDelay, 2, coarse = false, checkInvariants = checkInvariants,
      online = true, sharedCells = sharedCells)
  }

  def build(quantum: Int = 64, matchDelay: Int = 256, budget: Int = 2048, coarse: Boolean = false,
            checkInvariants: Boolean = true, online: Boolean = false, sharedCells: Boolean = false): (Circuit, Scaffold) = {
    val result = buildWithViews(quantum, matchDelay, budget, coarse, checkInvariants, online, sharedCells)
    (result.circuit, result.machine)
  }

  private def makeHeads(c: Circuit, arrival: Expr): Vector[PlaceHead] = {
    val rightCalls = VectorMap("R" -> 2, "L" -> 2, "C" -> 1, "W" -> 0, "V" -> 2)
    val leftCalls = VectorMap("R" -> 0, "L" -> 2, "C" -> 1, "W" -> 3, "V" -> 0)
    val headsPool = Map(
      "l" -> new StackPool(c, rightCalls.toVector.collect { case (name, count) if count != 0 => (name + ".l") -> count }),
      "r" -> new StackPool(c, leftCalls.toVector.collect { case (name, count) if count != 0 => (name + ".r") -> count }))
    val units = VectorMap.from(rightCalls.map { case (name, calls) => name -> (3 * (2 + 2 * calls)) })
    val rear = new StackPool(c, rightCalls.keys.toVector.flatMap(name => Vector("B", "B2").map(side => (name + ".in." + side) -> 1)))
    val reverse = new StackPool(c, units.toVector.map { case (name, count) => (name + ".in.Fr") -> count })
    val front = new StackPool(c, units.toVector.map { case (name, count) => (name + ".in.Br") -> (2 * count) })
    val queuesPool = Map("F" -> front, "Br" -> front, "WF" -> front, "B" -> rear, "B2" -> rear, "WB" -> rear, "Fr" -> reverse)
    val headCounters = Vector("m", "c").map { role =>
      role -> Vector("pos", "neg").map { side =>
        val counts = rightCalls.keys.toVector.map { name =>
          val count = if (side == "pos") {
            if (role == "m") { units(name) } else { 2 * units(name) }
          } else {
            if (role == "m") { units(name) + rightCalls(name) } else { 1 + rightCalls(name) }
          }
          (name + ".in." + role + "." + side) -> count
        }
        side -> new StackPool(c, counts)
      }.toMap
    }.toMap
    val heads = rightCalls.keys.toVector.map(name => new PlaceHead(headsPool, queuesPool, headCounters, name))
    heads.foreach(_.append(NEW, arrival))
    heads
  }

  private def makeCounterPool(c: Circuit): StackPool = {
    val counts = Vector(
      "g.len" -> (6, 2), "g.rad" -> (3, 1), "g.rem" -> (1, 2), "g.replay" -> (0, 1), "g.zero" -> (0, 0),
      "sp.lo" -> (0, 0), "sp.span" -> (10, 0), "sp.work" -> (4, 4), "sp.debt" -> (3, 1),
      "ch.h" -> (1, 0), "ch.lag" -> (1, 1), "ch.dist" -> (2, 1), "ch.bound" -> (0, 1),
      "ch.last" -> (0, 1), "ch.margin" -> (1, 5), "ch.cycle" -> (2, 1))
    new StackPool(c, counts.flatMap { case (name, (positive, negative)) => Vector((name + ".pos") -> positive, (name + ".neg") -> negative) })
  }

  def buildWithViews(quantum: Int = 64, matchDelay: Int = 256, budget: Int = 2048, coarse: Boolean = false,
                     checkInvariants: Boolean = true, online: Boolean = false, sharedCells: Boolean = false): Built = {
    if (quantum < 1) { throw new IllegalArgumentException("positive finite instruction quantum required") }
    if (Vector(matchDelay, budget).exists(n => n < 2 || (n & (n - 1)) != 0)) {
      throw new IllegalArgumentException("clocks must be powers of two of at least two")
    }
    val c = new Circuit(if (online) { "ab." } else { "ab" }, checkInvariants)
    var ready: Expr = FALSE
    var pending: Expr = FALSE
    val arrival = if (online) {
      val arriving = not(c.input().eqTo('.'))
      ready = c.get(PREVIOUS, "online.ready", Vector(false, true), true).eqTo(true)
      pending = c.get(PREVIOUS, "online.pending", Vector(false, true), false).eqTo(true)
      c.require(or(and(arriving, ready), and(not(arriving), not(ready))))
      pending = or(pending, arriving)
      c.put("input", Value.select(c.input().eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
      arriving
    } else {
      c.put("input", c.input(), Vector('a', 'b'), 'a')
      val phase = c.get(PREVIOUS, "arrival.phase", (0 until budget).toVector, budget - 1)
      val arriving = phase.eqTo(budget - 1)
      c.put("arrival.phase", phase.cycle())
      arriving
    }
    val heads = makeHeads(c, arrival)
    val right = heads(0)
    val left = heads(1)
    val center = heads(2)
    val walker = heads(3)
    val verifier = heads(4)
    val pool = makeCounterPool(c)
    val counters = Vector("len", "rad", "rem", "replay", "zero").map(name => new Counter(pool, "g." + name))
    val length = counters(0)
    val radius = counters(1)
    val remaining = counters(2)
    val replay = counters(3)
    val zero = counters(4)
    val dp = new Program(c, buildDpProgram("abs"), "dp", quantum = quantum + 8,
      extraSymbols = Map(SOURCE -> Vector("a", "b", "s", LEFT, END), LOWER -> Vector(LEFT, END, "1")),
      coarse = coarse, sharedCells = sharedCells, extraMoves = 8)
    val fpp = new Program(c, buildMarkedProgram("abs"), "f", quantum = quantum + 8,
      extraSymbols = Map(MARKS -> Vector(FIRST)), coarse = coarse, sharedCells = sharedCells, extraMoves = 9)
    val search = new Search(c, dp, pool, center, walker, radius)
    val chain = new Chain(c, pool, center, walker, verifier, radius)
    val source = fpp.tapes(SOURCE)
    val marks = fpp.tapes(MARKS)

    var mode = c.get(PREVIOUS, "g.mode", MODES, "init")
    var clock = c.get(PREVIOUS, "g.clock", (1 to matchDelay).toVector, matchDelay)
    var output = c.get(PREVIOUS, "g.out", Vector(false, true), false).eqTo(true)
    var replaying = c.get(PREVIOUS, "g.replaying", Vector(false, true), false).eqTo(true)
    var odd = c.get(PREVIOUS, "g.odd", Vector(false, true), false).eqTo(true)
    var pair = c.get(PREVIOUS, "g.pair", Vector(0, 1), 0)

    val scanning = mode.eqTo("scan")
    val chainActive = not(chain.mode.eqTo("idle"))
    chain.step(dp.tapes(OUTPUT), and(scanning, chainActive))
    val searching = and(scanning, not(chainActive), search.active())
    search.tick(searching, quantum)
    chain.start(and(searching, search.mode.eqTo("found")))
    val restart = and(scanning, chain.mode.eqTo("broken"))
    c.require(and(not(chain.margin.negative()), chain.last.positive(), chain.lag.zero()), restart)
    search.start(chain.last, restart)
    chain.setMode("idle", restart)
    clock = Value.select(restart, Value.constant(matchDelay), clock)

    val dispatch = MODES.map(name => name -> mode.eqTo(name)).toMap
    val init = dispatch("init")
    right.right(init)
    left.copyFrom(right, init)
    center.copyFrom(right, init)
    length.inc(init)
    search.start(zero, init)
    mode = Value.select(init, Value.constant("scan"), mode)
    output = choose(init, TRUE, output)

    val available = or(replaying, if (online) { right.canRight() } else { right.head.canRight() })
    val ticking = and(dispatch("scan"), available)
    val compare = and(ticking, clock.eqTo(1))
    clock = Value.select(ticking, clock.cycle(-1), clock)
    right.right(compare)
    left.left(compare)
    val advanceSearch = and(compare, search.active(), chain.mode.eqTo("idle"))
    search.advanceMatch(advanceSearch)
    radius.inc(and(compare, not(advanceSearch)))
    val leftSymbol = left.read()
    val rightSymbol = right.read()
    chain.checkPair(leftSymbol, compare)
    val matched = and(compare, leftSymbol.equal(rightSymbol))
    val shift = and(compare, not(matched), not(replaying), chain.canShift(), chain.prediction().equal(rightSymbol))
    val fallback = and(compare, not(or(matched, shift)))
    c.require(not(replaying), fallback)
    length.inc(or(matched, shift))
    length.inc(or(matched, shift))
    chain.matched(or(and(matched, not(chain.mode.eqTo("idle"))), shift))
    val replayed = and(matched, replaying)
    replay.dec(replayed)
    replaying = choose(and(replayed, replay.zero()), FALSE, replaying)
    output = choose(and(matched, not(right.gap)), left.isFirst(), output)
    chain.beginShift(shift)
    remaining.copyFrom(chain.h, shift)
    mode = Value.select(shift, Value.constant("shift"), mode)

    fpp.reset(fallback)
    walker.copyFrom(right, fallback)
    remaining.copyFrom(length, fallback)
    remaining.inc(fallback)
    source.write(Value.constant(LEFT), fallback)
    source.move(1, fallback)
    search.setMode("idle", fallback)
    chain.setMode("idle", fallback)
    mode = Value.select(fallback, Value.constant("copy"), mode)

    val shiftPositive = remaining.positive()
    val shifting = and(dispatch("shift"), shiftPositive)
    remaining.dec(shifting)
    center.right(shifting)
    left.right(shifting)
    left.right(shifting)
    radius.dec(shifting)
    length.dec(shifting)
    length.dec(shifting)
    chain.shiftOne(shifting)
    val shifted = and(dispatch("shift"), not(shiftPositive))
    mode = Value.select(shifted, Value.constant("scan"), mode)
    output = choose(and(shifted, not(right.gap)), left.isFirst(), output)

    val copyPositive = remaining.positive()
    val copying = and(dispatch("copy"), copyPositive)
    val symbol = walker.read()
    c.require(not(symbol.eqTo(None)), copying)
    source.write(Value(symbol.cases.collect { case (s, guard) if s != None => s.toString -> guard }), copying)
    source.move(1, copying)
    walker.left(copying)
    remaining.dec(copying)
    val copied = and(dispatch("copy"), not(copyPositive))
    source.write(Value.constant(END), copied)
    mode = Value.select(copied, Value.constant("home"), mode)

    val home = source.focus.eqTo(LEFT)
    val returned = and(dispatch("home"), home)
    fpp.start(returned)
    mode = Value.select(returned, Value.constant("fpp"), mode)
    source.move(-1, and(dispatch("home"), not(home)))
    c.require(not(fpp.done), dispatch("fpp"))
    for (_ <- 0 until quantum) { fpp.step(dispatch("fpp")) }
    val finished = and(dispatch("fpp"), fpp.done)
    marks.move(1, finished)
    marks.write(Value.constant(FIRST), finished)
    marks.move(1, finished)
    mode = Value.select(finished, Value.constant("mark_end"), mode)

    val end = marks.focus.eqTo(END)
    val marked = and(dispatch("mark_end"), end)
    marks.move(-1, marked)
    odd = choose(marked, FALSE, odd)
    mode = Value.select(marked, Value.constant("choose"), mode)
    marks.move(1, and(dispatch("mark_end"), not(end)))

    val candidate = and(odd, or(marks.focus.eqTo("1"), marks.focus.eqTo(FIRST)))
    val chosen = and(dispatch("choose"), candidate)
    left.copyFrom(right, chosen)
    center.copyFrom(right, chosen)
    length.reset(chosen)
    length.inc(chosen)
    radius.reset(chosen)
    pair = Value.select(chosen, Value.constant(0), pair)
    mode = Value.select(chosen, Value.constant("rewind"), mode)
    val skip = and(dispatch("choose"), not(candidate))
    marks.move(-1, skip)
    odd = choose(skip, not(odd), odd)

    val first = marks.focus.eqTo(FIRST)
    val rewound = and(dispatch("rewind"), first)
    fpp.reset(rewound)
    mode = Value.select(rewound, Value.constant("replay_start"), mode)
    val rewind = and(dispatch("rewind"), not(first))
    marks.move(-1, rewind)
    left.left(rewind)
    length.inc(rewind)
    pair = Value.select(rewind, pair.cycle(), pair)
    val centerStep = and(rewind, pair.eqTo(0))
    center.left(centerStep)
    radius.inc(centerStep)

    val restarting = dispatch("replay_start")
    replay.copyFrom(radius, restarting)
    right.copyFrom(center, restarting)
    left.copyFrom(center, restarting)
    radius.reset(restarting)
    length.reset(restarting)
    length.inc(restarting)
    chain.setMode("idle", restarting)
    search.start(zero, restarting)
    replaying = choose(restarting, replay.positive(), replaying)
    clock = Value.select(restarting, Value.constant(matchDelay), clock)
    mode = Value.select(restarting, Value.constant("scan"), mode)
    output = choose(and(restarting, not(replaying), not(right.gap)), left.isFirst(), output)

    val caught = and(mode.eqTo("scan"), not(replaying), not(right.gap), not(right.head.canRight()))
    var event = caught
    if (online) {
      event = and(caught, pending)
      pending = and(pending, not(event))
      ready = and(mode.eqTo("scan"), not(replaying), right.gap, not(right.head.canRight()))
      c.require(not(and(ready, pending)))
      for ((key, value) <- Vector("online.ready" -> ready, "online.pending" -> pending, "online.event" -> event)) {
        c.put(key, Value.select(value, Value.constant(true), Value.constant(false)), Vector(false, true), key == "online.ready")
      }
    }
    heads.foreach(_.commit())
    counters.foreach(_.commit())
    search.commit()
    chain.commit()
    fpp.commit()
    c.put("g.mode", mode)
    c.put("g.clock", clock)
    c.put("g.pair", pair)
    for ((name, value) <- Vector("g.out" -> output, "g.replaying" -> replaying, "g.odd" -> odd)) {
      c.put(name, Value.select(value, Value.constant(true), Value.constant(false)))
    }
    val views = Views(heads, counters, search, chain, fpp)
    val machine = c.machine(and(event, output), initialAccepting = true)
    Built(c, machine, views)
  }
}
