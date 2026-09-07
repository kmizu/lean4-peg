package pal

import Expr.{FALSE, TRUE}
import Ref.{EMPTY, PREVIOUS}
import ScaffoldCircuit.{choose, conjunction as AND, disjunction as OR, neg}

/** One reusable dyadic PAL stage and its four bounded result packets. */
final class WindowStage(val circuit: Circuit, val index: Int, historyPool: StackPool, val worker: WindowWorkerLike) {
  private val stageName = s"stage$index"
  val half: Stack = new Stack(historyPool, stageName + ".half", Some("cells"))
  val clock: Stack = new Stack(historyPool, stageName + ".clock", Some("cells"))
  val aliveKey: String = stageName + ".alive"
  val intervalKey: String = stageName + ".interval"
  var alive: Expr = circuit.get(PREVIOUS, aliveKey, Vector(false, true), false).eqTo(true)
  var interval: Value[Int] = circuit.get(PREVIOUS, intervalKey, (0 to 6).toVector, 0)
  val pendingKey: String = stageName + ".pending"
  val batchKey: String = stageName + ".batch"
  var pending: Expr = circuit.get(PREVIOUS, pendingKey, Vector(false, true), false).eqTo(true)
  var batch: Value[Int] = circuit.get(PREVIOUS, batchKey, (0 to 3).toVector, 0)
  val results: Vector[FlagStack] = Vector.tabulate(4)(i => new FlagStack(worker.flagPool.get, s"$stageName.result$i"))
  var birth: Expr = FALSE
  var release: Expr = FALSE
  var middle: Expr = FALSE

  def answering(): Expr = AND(alive, OR((2 to 5).map(interval.eqTo)*))

  def advance(newBirth: Expr, sourceHalf: Stack): Unit = {
    clock.drop(alive)
    val boundary = AND(alive, clock.empty())
    interval = Value.select(boundary, interval.map(n => math.min(n + 1, 6)), interval)
    clock.copyFrom(half, boundary)
    val newRelease = AND(boundary, OR((1 to 4).map(interval.eqTo)*))
    circuit.require(neg(pending), newRelease)
    batch = Value.select(newRelease, interval.map(n => math.max(0, math.min(3, n - 1))).recode((0 to 3).toVector), batch)
    alive = AND(alive, neg(AND(boundary, interval.eqTo(6))))
    half.copyFrom(sourceHalf, newBirth)
    clock.copyFrom(sourceHalf, newBirth)
    interval = Value.select(newBirth, Value.constant(0), interval)
    alive = OR(alive, newBirth)
    birth = newBirth
    release = AND(newRelease, neg(newBirth))
    pending = AND(pending, neg(newBirth))
    results.foreach(_.clear(newBirth))
  }

  def consume(): Unit = {
    val active = answering()
    val selected = new FlagStack(results.head.pool, results.head.name)
    selected.root = EMPTY
    selected.index = worker.flagPool.get.index(-1)
    for ((result, resultIndex) <- results.zipWithIndex) {
      selected.copyFrom(result, interval.eqTo(resultIndex + 2))
    }
    middle = AND(active, selected.pop(active))
    for ((result, resultIndex) <- results.zipWithIndex) {
      result.copyFrom(selected, AND(active, interval.eqTo(resultIndex + 2)))
    }
  }

  def capture(): Unit = {
    pending = OR(pending, release)
    val done = AND(pending, worker.mode.eqTo("done"))
    for ((result, resultIndex) <- results.zipWithIndex) {
      result.copyFrom(worker.flags.get, AND(done, batch.eqTo(resultIndex)))
    }
    pending = AND(pending, neg(done))
  }

  def commit(): Unit = {
    half.commit()
    clock.commit()
    results.foreach(_.commit())
    circuit.put(intervalKey, interval)
    circuit.put(batchKey, batch)
    circuit.put(aliveKey, Value.select(alive, Value.constant(true), Value.constant(false)))
    circuit.put(pendingKey, Value.select(pending, Value.constant(true), Value.constant(false)))
  }
}

/** Two dyadic PAL stages in one transition per original binary input. */
final class WindowPAL(val circuit: Circuit, val rates: BatchRates = GsBatchClock.DEFAULT_BATCH,
                      matcherFactory: (Circuit, String, Int) => WindowWorkerLike = ScaffoldWindowWorkers.matcher,
                      flagsFactory: (Circuit, String, Int) => WindowWorkerLike = ScaffoldWindowWorkers.flags) {
  private val defaults = GsBatchClock.DEFAULT_BATCH
  if (rates.k != defaults.k || rates.matching < defaults.matching || rates.flags < defaults.flags) {
    throw new IllegalArgumentException("the complete PAL source requires the derived k=8 service bounds")
  }
  val matchers: Vector[WindowWorkerLike] = Vector.tabulate(2)(i => matcherFactory(circuit, s"match$i", rates.matching))
  val flags: Vector[WindowWorkerLike] = Vector.tabulate(2)(i => flagsFactory(circuit, s"flag$i", rates.flags))
  private val historyPool = new StackPool(circuit, Vector("cells" -> 1))
  val history: Stack = new Stack(historyPool, "pal.history", Some("cells"))
  val power: Stack = new Stack(historyPool, "pal.power", Some("cells"))
  val nextBirth: Stack = new Stack(historyPool, "pal.next_birth", Some("cells"))
  val stages: Vector[WindowStage] = Vector.tabulate(2)(i => new WindowStage(circuit, i, historyPool, flags(i)))
  var powerReady: Expr = circuit.get(PREVIOUS, "pal.power_ready", Vector(false, true), false).eqTo(true)
  var slot: Value[Int] = circuit.get(PREVIOUS, "pal.slot", Vector(0, 1), 0)
  var small: Value[Int] = circuit.get(PREVIOUS, "pal.small", (0 to 4).toVector, 0)
  var first: Value[Boolean] = circuit.get(PREVIOUS, "pal.first", Vector(false, true), false)
  var output: Expr = TRUE

  def tick(): Unit = {
    val current = circuit.input().eqTo('b')
    first = Value.select(small.eqTo(0), Value.select(current, Value.constant(true), Value.constant(false)), first)
    small = small.map(n => math.min(4, n + 1))
    history.push()
    val firstRound = neg(powerReady)
    nextBirth.drop(powerReady)
    val birth = AND(powerReady, nextBirth.empty())
    for ((stage, stageIndex) <- stages.zipWithIndex) {
      stage.advance(AND(birth, slot.eqTo(stageIndex)), power)
    }
    power.copyFrom(history, OR(firstRound, birth))
    nextBirth.copyFrom(history, OR(firstRound, birth))
    powerReady = TRUE
    slot = Value.select(birth, slot.cycle(), slot)

    for (((stage, matching), flagging) <- stages.zip(matchers).zip(flags)) {
      matching.arrive()
      flagging.arrive()
      flagging.resetFlags(stage.birth)
      matching.start(stage.birth)
      flagging.start(stage.release)
      flagging.mark(stage.release)
      stage.consume()
      matching.service()
      flagging.service()
      stage.capture()
    }

    val active = stages.map(_.answering())
    circuit.require(AND(OR(active*), neg(AND(active*))), small.eqTo(4))
    val ordinary = OR(active.zip(stages).zip(matchers).map { case ((enabled, stage), matching) =>
      AND(enabled, stage.middle, matching.output)
    }*)
    val short = OR(small.eqTo(1), AND(OR(small.eqTo(2), small.eqTo(3)),
      choose(current, first.eqTo(true), first.eqTo(false))))
    output = choose(small.eqTo(4), ordinary, short)
  }

  def commit(): Unit = {
    for (((matching, flagging), stage) <- matchers.zip(flags).zip(stages)) {
      matching.commit()
      flagging.commit()
      stage.commit()
    }
    Vector(history, power, nextBirth).foreach(_.commit())
    circuit.put("pal.slot", slot)
    circuit.put("pal.small", small)
    circuit.put("pal.first", first)
    circuit.put("pal.power_ready", Value.select(powerReady, Value.constant(true), Value.constant(false)))
  }
}

object ScaffoldWindowPal {
  def build(rates: BatchRates = GsBatchClock.DEFAULT_BATCH): (Circuit, WindowPAL, Scaffold) = {
    val circuit = new Circuit("ab")
    val controller = new WindowPAL(circuit, rates)
    controller.tick()
    controller.commit()
    (circuit, controller, circuit.machine(controller.output, initialAccepting = true))
  }
}
