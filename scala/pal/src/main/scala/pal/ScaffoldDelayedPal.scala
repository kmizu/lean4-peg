package pal

import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction, disjunction, neg, choose}

/** Complete two-stage PAL controller at explicit local-instruction speed.
  * Each input round has a fixed derived number of transitions. Only its ready
  * transition reads an actual input byte. Folding remains a separate compiler
  * step: this machine alone is not a grammar for unchanged PAL input.
  */
object ScaffoldDelayedPal {
  val PHASES: Vector[String] = Vector("ready", "settle", "deliver", "broadcast", "clock", "start", "mark", "middle", "serve", "finish")

  /** Persistent half-interval clock and four batches of palindrome flags. */
  final class Stage(val circuit: Circuit, val index: Int, historyPool: StackPool, flags: GSFlags) {
    private val name = s"stage$index"
    val half = new Stack(historyPool, name + ".half", Some("cells"))
    val clock = new Stack(historyPool, name + ".clock", Some("cells"))
    val aliveKey: String = name + ".alive"
    val phaseKey: String = name + ".interval"
    var alive: Expr = circuit.get(PREVIOUS, aliveKey, Vector(false, true), false).eqTo(true)
    var interval: Value[Int] = circuit.get(PREVIOUS, phaseKey, (0 until 7).toVector, 0)
    val birthKey: String = name + ".birth"
    val releaseKey: String = name + ".release"
    var birth: Expr = circuit.get(PREVIOUS, birthKey, Vector(false, true), false).eqTo(true)
    var release: Expr = circuit.get(PREVIOUS, releaseKey, Vector(false, true), false).eqTo(true)
    val batchKey: String = name + ".batch"
    var batch: Value[Int] = circuit.get(PREVIOUS, batchKey, Vector(0, 1, 2, 3), 0)
    val pendingKey: String = name + ".pending"
    val middleKey: String = name + ".middle"
    var pending: Expr = circuit.get(PREVIOUS, pendingKey, Vector(false, true), false).eqTo(true)
    var middle: Expr = circuit.get(PREVIOUS, middleKey, Vector(false, true), false).eqTo(true)
    val results: Vector[Stack] = Vector.tabulate(4)(i => new Stack(flags.flagPool, s"$name.result$i", Some("cells")))

    def answering(): Expr = conjunction(alive, disjunction((2 until 6).map(interval.eqTo)*))

    def advance(enabled: Expr, born: Expr, sourceHalf: Stack): Unit = {
      clock.drop(conjunction(enabled, alive))
      val boundary = conjunction(enabled, alive, clock.empty())
      interval = Value.select(boundary, interval.map(n => math.min(n + 1, 6)), interval)
      clock.copyFrom(half, boundary)
      val released = conjunction(boundary, disjunction((1 until 5).map(interval.eqTo)*))
      circuit.require(neg(pending), released)
      release = choose(enabled, released, release)
      batch = Value.select(released, interval.map(n => math.max(0, math.min(3, n - 1))).recode(Vector(0, 1, 2, 3)), batch)
      alive = conjunction(alive, neg(conjunction(boundary, interval.eqTo(6))))
      half.copyFrom(sourceHalf, born)
      clock.copyFrom(sourceHalf, born)
      interval = Value.select(born, Value.constant(0), interval)
      alive = disjunction(alive, born)
      release = conjunction(release, neg(born))
      birth = choose(enabled, born, birth)
      pending = conjunction(pending, neg(born))
      results.foreach(_.clear(born))
    }

    def started(enabled: Expr): Unit = { pending = disjunction(pending, conjunction(enabled, release)) }

    def capture(worker: GSFlags): Unit = {
      val done = conjunction(pending, worker.phase.eqTo("done"))
      for ((result, index) <- results.zipWithIndex) { result.copyFrom(worker.flags, conjunction(done, batch.eqTo(index))) }
      pending = conjunction(pending, neg(done))
    }

    def consume(enabled: Expr): Unit = {
      val active = conjunction(enabled, answering())
      val answers = results.zipWithIndex.map { case (result, index) =>
        val take = conjunction(active, interval.eqTo(index + 2))
        circuit.require(neg(result.empty()), take)
        val (_, bit) = result.pop(take)
        conjunction(take, bit.eqTo(true))
      }
      middle = choose(enabled, disjunction(answers*), middle)
    }

    def commit(): Unit = {
      half.commit()
      clock.commit()
      results.foreach(_.commit())
      for ((key, value) <- Vector(phaseKey -> interval, batchKey -> batch)) { circuit.put(key, value) }
      for ((key, value) <- Vector(aliveKey -> alive, birthKey -> birth, releaseKey -> release, pendingKey -> pending, middleKey -> middle)) {
        circuit.put(key, Value.select(value, Value.constant(true), Value.constant(false)))
      }
    }
  }

  def build(rates: Option[Rates] = None, dualFlags: Boolean = true): (Circuit, ScaffoldDelayedPal, Scaffold) = {
    val selected = rates.getOrElse(if (dualFlags) { GsLocalClock.DEFAULT_DUAL } else { GsLocalClock.DEFAULT })
    val circuit = new Circuit("ab")
    val machine = new ScaffoldDelayedPal(circuit, selected, dualFlags)
    machine.tick()
    machine.commit()
    (circuit, machine, circuit.machine(conjunction(machine.phase.eqTo("ready"), machine.output), initialAccepting = true))
  }
}

final class ScaffoldDelayedPal(val circuit: Circuit, val rates: Rates = GsLocalClock.DEFAULT, dualFlags: Boolean = false) {
  import ScaffoldDelayedPal.{PHASES, Stage}
  if (rates.k != 8 || rates.flags < rates.matching || rates.flags < 32 || (rates.flags & (rates.flags - 1)) != 0) {
    throw new IllegalArgumentException("the current worker tables require the derived k=8 power-of-two schedule")
  }
  val matchers: Vector[GSMatcher] = Vector.tabulate(2)(i => new GSMatcher(circuit, s"match$i"))
  val flags: Vector[GSFlags] = Vector.tabulate(2)(i => new GSFlags(circuit, s"flag$i", dualFlags))
  private val historyPool = matchers(0).streams.cells
  val power = new Stack(historyPool, "pal.power", Some("cells"))
  val nextBirth = new Stack(historyPool, "pal.next_birth", Some("cells"))
  val stages: Vector[Stage] = Vector.tabulate(2)(i => new Stage(circuit, i, historyPool, flags(i)))
  var phase: Value[String] = circuit.get(PREVIOUS, "pal.phase", PHASES, "ready")
  var clock: Value[Int] = circuit.get(PREVIOUS, "pal.clock", (0 until rates.flags).toVector, 0)
  var powerReady: Expr = circuit.get(PREVIOUS, "pal.power_ready", Vector(false, true), false).eqTo(true)
  var slot: Value[Int] = circuit.get(PREVIOUS, "pal.slot", Vector(0, 1), 0)
  var small: Value[Int] = circuit.get(PREVIOUS, "pal.small", Vector(0, 1, 2, 3, 4), 0)
  var first: Value[Boolean] = circuit.get(PREVIOUS, "pal.first", Vector(false, true), false)
  var current: Value[Boolean] = circuit.get(PREVIOUS, "pal.current", Vector(false, true), false)
  var output: Expr = circuit.get(PREVIOUS, "pal.output", Vector(false, true), true).eqTo(true)

  def tick(): Unit = {
    val oldPhase = phase
    val ready = oldPhase.eqTo("ready")
    first = Value.select(conjunction(ready, small.eqTo(0)),
      Value.select(circuit.input().eqTo('b'), Value.constant(true), Value.constant(false)), first)
    current = Value.select(ready, Value.select(circuit.input().eqTo('b'), Value.constant(true), Value.constant(false)), current)
    small = Value.select(ready, small.map(n => math.min(4, n + 1)), small)
    val byte = Value.select(current.eqTo(true), Value.constant('b'), Value.constant('a'))
    circuit.put("input", byte, Vector('a', 'b'), 'a')
    val work = Value.constant('.')
    val matchingClock = conjunction(clock.bits.drop(GalilClock.bitLength(rates.matching - 1)).map(neg)*)
    for (((stage, matcher), worker) <- stages.zip(matchers).zip(flags)) {
      var matcherCommand: Value[Any] = Value.constant(None)
      matcherCommand = Value.select(conjunction(oldPhase.eqTo("settle"), matcher.phase.eqTo("maintenance")), work, matcherCommand)
      matcherCommand = Value.select(oldPhase.eqTo("deliver"), byte, matcherCommand)
      matcherCommand = Value.select(conjunction(oldPhase.eqTo("broadcast"),
        disjunction(matcher.phase.eqTo("broadcast"), matcher.phase.eqTo("maintenance"))), work, matcherCommand)
      matcherCommand = Value.select(conjunction(oldPhase.eqTo("start"), stage.birth), Value.constant('!'), matcherCommand)
      matcherCommand = Value.select(conjunction(oldPhase.eqTo("serve"), matchingClock), work, matcherCommand)
      var flagsCommand: Value[Any] = Value.constant(None)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("settle"), worker.phase.eqTo("maintenance")), work, flagsCommand)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("deliver"), stage.alive), byte, flagsCommand)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("broadcast"),
        disjunction(worker.phase.eqTo("broadcast"), worker.phase.eqTo("maintenance"))), work, flagsCommand)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("start"), stage.release), Value.constant('!'), flagsCommand)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("start"), stage.birth), Value.constant('^'), flagsCommand)
      flagsCommand = Value.select(conjunction(oldPhase.eqTo("mark"), stage.release), Value.constant('|'), flagsCommand)
      flagsCommand = Value.select(oldPhase.eqTo("serve"), work, flagsCommand)
      matcher.tick(Some(matcherCommand))
      worker.tick(Some(flagsCommand))
      stage.started(oldPhase.eqTo("start"))
      stage.capture(worker)
    }
    val clocking = oldPhase.eqTo("clock")
    val firstClock = conjunction(clocking, neg(powerReady))
    nextBirth.drop(conjunction(clocking, powerReady))
    val birth = conjunction(clocking, powerReady, nextBirth.empty())
    for ((stage, index) <- stages.zipWithIndex) {
      stage.advance(clocking, conjunction(birth, slot.eqTo(index)), power)
      stage.consume(oldPhase.eqTo("middle"))
    }
    val history = matchers(0).end.left
    power.copyFrom(history, disjunction(firstClock, birth))
    nextBirth.copyFrom(history, disjunction(firstClock, birth))
    powerReady = disjunction(powerReady, firstClock)
    slot = Value.select(birth, slot.cycle(), slot)
    val active = stages.map(_.answering())
    circuit.require(conjunction(disjunction(active*), neg(conjunction(active*))),
      conjunction(oldPhase.eqTo("finish"), small.eqTo(4)))
    val ordinary = disjunction(active.zip(stages).zip(matchers).map { case ((isActive, stage), matcher) =>
      conjunction(isActive, stage.middle, matcher.output)
    }*)
    val smallAnswer = disjunction(small.eqTo(1), conjunction(disjunction(small.eqTo(2), small.eqTo(3)), first.equal(current)))
    output = choose(oldPhase.eqTo("finish"), choose(small.eqTo(4), ordinary, smallAnswer), output)
    val timed = disjunction(Vector("settle", "broadcast", "serve").map(oldPhase.eqTo)*)
    val last = disjunction(conjunction(oldPhase.eqTo("settle"), clock.eqTo(2)),
      conjunction(oldPhase.eqTo("broadcast"), clock.eqTo(28)), conjunction(oldPhase.eqTo("serve"), clock.eqTo(rates.flags - 1)))
    val advance = disjunction(neg(timed), last)
    clock = Value.select(conjunction(timed, neg(last)), clock.cycle(), Value.constant(0))
    phase = Value.select(advance, oldPhase.map(name => PHASES((PHASES.indexOf(name) + 1) % PHASES.size)), oldPhase)
  }

  def commit(): Unit = {
    for (((matcher, worker), stage) <- matchers.zip(flags).zip(stages)) {
      matcher.commit()
      worker.commit()
      stage.commit()
    }
    power.commit()
    nextBirth.commit()
    for ((key, value) <- Vector[(String, Value[Any])]("pal.phase" -> phase, "pal.clock" -> clock, "pal.slot" -> slot,
      "pal.small" -> small, "pal.first" -> first, "pal.current" -> current)) { circuit.put(key, value) }
    circuit.put("pal.power_ready", Value.select(powerReady, Value.constant(true), Value.constant(false)))
    circuit.put("pal.output", Value.select(output, Value.constant(true), Value.constant(false)))
  }
}
