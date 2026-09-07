package pal

import scala.collection.mutable
import Expr.FALSE
import Ref.{NEW, PREVIOUS}
import ScaffoldCircuit.{conjunction, disjunction, neg, choose}

/** Full finite GS matcher with real input queues and frozen prefix heads.
  * The fixture loads a prefix, freezes it with !, and services instructions
  * with dots. It is a compiler/interface test, not the final PAL grammar.
  * Port of `scaffold_gs_matcher.py`; Python finalize is commit.
  */
final class GSMatcher(val circuit: Circuit, val prefix: String = "matcher") {
  val program: Program = GsMatchHeads.compileMatcher()
  val readers: ReaderLiveness = GsHeadLiveness.analyzeReaders(program)
  val distances = new LiveDistances(circuit, program, GsMatchHeads.MATCH_HEADS, prefix + ".distance",
    observePositions = false, availabilityDistance = false)
  private val names = Vector.tabulate(readers.registers)(i => s"$prefix.r$i")
  val streams = new StreamBank(circuit, Vector(prefix + ".begin", prefix + ".end") ++
    names.flatMap(name => Vector(name + ".pattern", name + ".text")))
  val begin: StreamHead = streams.heads(prefix + ".begin")
  val end: StreamHead = streams.heads(prefix + ".end")
  val registers: Vector[PatternTextHead] = names.map(new PatternTextHead(streams, _))
  val heads: Map[String, PatternTextHead] = readers.colors.map { case (head, color) => head -> registers(color) }
  val pcKey: String = prefix + ".pc"
  val phaseKey: String = prefix + ".phase"
  var pc: Value[Int] = circuit.get(PREVIOUS, pcKey, program.code.indices.toVector, program.start)
  var phase: Value[String] = circuit.get(PREVIOUS, phaseKey, Vector("idle", "broadcast", "maintenance", "run"), "idle")
  val activeKey: String = prefix + ".active"
  var active: Expr = circuit.get(PREVIOUS, activeKey, Vector(false, true), false).eqTo(true)
  val queueKey: String = prefix + ".queue"
  val remainingKey: String = prefix + ".remaining"
  private val queueNames = streams.queues.queues.keys.toVector
  var queue: Value[String] = circuit.get(PREVIOUS, queueKey, queueNames, queueNames.head)
  var remaining: Value[Int] = circuit.get(PREVIOUS, remainingKey, Vector(0, 1, 2, 3), 0)
  val returnKey: String = prefix + ".return"
  val indexKey: String = prefix + ".broadcast_index"
  var returnPhase: Value[String] = circuit.get(PREVIOUS, returnKey, Vector("broadcast", "run"), "broadcast")
  val broadcastQueues: Vector[String] = Vector(begin.queue.name) ++ registers.map(_.text.queue.name)
  var broadcastIndex: Value[Int] = circuit.get(PREVIOUS, indexKey, (0 to broadcastQueues.size).toVector, 0)
  val cellKey: String = prefix + ".input_cell"
  val outputKey: String = prefix + ".matched"
  var cell: Ref = circuit.getRef(PREVIOUS, cellKey)
  var output: Expr = circuit.get(PREVIOUS, outputKey, Vector(false, true), false).eqTo(true)

  def tick(symbols: Option[Value[Any]] = None): Unit = {
    val char = symbols.getOrElse(circuit.input())
    val arrival = disjunction(char.eqTo('a'), char.eqTo('b'))
    val start = char.eqTo('!')
    val dot = char.eqTo('.')
    circuit.require(disjunction(phase.eqTo("idle"), phase.eqTo("run")), disjunction(arrival, start))
    circuit.require(end.focus.present(), start)
    val oldPhase = phase
    val run = conjunction(dot, oldPhase.eqTo("run"))
    val broadcast = conjunction(dot, oldPhase.eqTo("broadcast"))
    val maintenance = conjunction(dot, oldPhase.eqTo("maintenance"))
    val events = program.code.indices.map(i => conjunction(run, pc.eqTo(i))).toVector
    val nextPc = mutable.LinkedHashMap.empty[Int, Expr]
    val copies = mutable.LinkedHashMap.empty[(Int, Int), Expr]
    val moves = mutable.LinkedHashMap.empty[(Int, Int), Expr]
    val requests = mutable.LinkedHashMap.empty[String, Expr]
    var matched = FALSE
    def edge(target: Int, guard: Expr): Unit = { nextPc(target) = disjunction(nextPc.getOrElse(target, FALSE), guard) }
    def request(name: String, guard: Expr): Unit = { requests(name) = disjunction(requests.getOrElse(name, FALSE), guard) }
    for (((enabled, Row(event, targets)), state) <- events.zip(program.code).zipWithIndex) {
      def branch(decision: Expr): Unit = {
        edge(targets(0), conjunction(enabled, neg(decision)))
        edge(targets(1), conjunction(enabled, decision))
      }
      event match {
        case Event.Available(head) => branch(heads(head).available())
        case Event.Symbols(left, right) =>
          val a = heads(left).read(enabled)
          val b = heads(right).read(enabled)
          circuit.require(conjunction(neg(a.eqTo(None)), neg(b.eqTo(None))), enabled)
          branch(a.equal(b))
        case Event.Equal(left, right) => branch(distances.equal(left, right))
        case Event.Less(left, right) => branch(distances.less(left, right))
        case Event.Halt => circuit.require(FALSE, enabled)
        case other =>
          edge(targets(0), enabled)
          other match {
            case Event.Copy(target, source) =>
              if (readers.after(state)(target)) {
                val pair = (readers.colors(target), readers.colors(source))
                if (pair._1 != pair._2) { copies(pair) = disjunction(copies.getOrElse(pair, FALSE), enabled) }
              }
            case Event.Move(batch) =>
              val Event.Movement(head, direction) = batch.head
              if (readers.after(state)(head)) {
                val key = (readers.colors(head), direction)
                moves(key) = disjunction(moves.getOrElse(key, FALSE), enabled)
              }
            case Event.AssertEqual(left, right) => circuit.require(distances.equal(left, right), enabled)
            case Event.Match(_) =>
              circuit.require(neg(heads("B").available()), enabled)
              matched = disjunction(matched, enabled)
            case _ => throw new IllegalArgumentException("unsupported GS matcher instruction")
          }
      }
    }
    distances.execute(events)
    for (((register, direction), enabled) <- moves) {
      val (name, needed) = registers(register).move(direction, enabled)
      request(name, needed)
    }
    for (((target, source), enabled) <- copies) { registers(target).copyFrom(registers(source), enabled) }
    val count = broadcastQueues.size
    val finished = choose(active, broadcastIndex.eqTo(count), broadcastIndex.eqTo(1))
    val push = conjunction(broadcast, neg(finished))
    for ((name, index) <- broadcastQueues.zipWithIndex) {
      val enabled = conjunction(push, broadcastIndex.eqTo(index))
      streams.queues.queues(name).push(cell, enabled)
      request(name, enabled)
    }
    for ((name, target) <- streams.queues.queues) { target.workUnit(conjunction(maintenance, queue.eqTo(name))) }
    end.followArrival(NEW, arrival)
    distances.loadOne(arrival)
    cell = Ref.select(arrival, NEW, cell)
    heads("Origin").start(end, start)
    heads("Tail").start(begin, start)
    distances.initialize(Map(("Origin", "Tail") -> Some((distances.length, -1))), start)
    pc = Value.select(run, Value(nextPc), pc)
    pc = Value.select(start, Value.constant(program.start), pc)
    active = disjunction(active, start)
    output = disjunction(conjunction(output, neg(disjunction(arrival, start))), matched)
    broadcastIndex = Value.select(push, broadcastIndex.map(n => math.min(n + 1, count)), broadcastIndex)
    broadcastIndex = Value.select(arrival, Value.constant(0), broadcastIndex)
    val finishedWork = conjunction(maintenance, remaining.eqTo(1))
    remaining = Value.select(maintenance, remaining.map(n => math.max(0, n - 1)), remaining)
    phase = Value.select(finishedWork, returnPhase, phase)
    phase = Value.select(conjunction(broadcast, finished),
      Value.select(active, Value.constant("run"), Value.constant("idle")), phase)
    val needed = disjunction(requests.values.toSeq*)
    queue = Value.select(needed, Value(requests), queue)
    remaining = Value.select(needed, Value.constant(3), remaining)
    returnPhase = Value.select(needed, Value.select(push, Value.constant("broadcast"), Value.constant("run")), returnPhase)
    phase = Value.select(needed, Value.constant("maintenance"), phase)
    phase = Value.select(arrival, Value.constant("broadcast"), phase)
    phase = Value.select(start, Value.constant("run"), phase)
  }

  def commit(): Unit = {
    distances.commit()
    streams.commit()
    registers.foreach(_.commit())
    for ((key, value) <- Vector[(String, Value[Any])](pcKey -> pc, phaseKey -> phase,
      queueKey -> queue, remainingKey -> remaining, returnKey -> returnPhase, indexKey -> broadcastIndex)) {
      circuit.put(key, value)
    }
    for ((key, value) <- Vector(activeKey -> active, outputKey -> output)) {
      circuit.put(key, Value.select(value, Value.constant(true), Value.constant(false)))
    }
    circuit.putRef(cellKey, cell)
  }
}

object ScaffoldGsMatcher {
  def fixture(): (Circuit, GSMatcher, Scaffold) = {
    val circuit = new Circuit("ab!.")
    circuit.put("input", Value.select(circuit.input().eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    val worker = new GSMatcher(circuit)
    worker.tick()
    worker.commit()
    (circuit, worker, circuit.machine(worker.output))
  }
}
