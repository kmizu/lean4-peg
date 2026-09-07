package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable
import Expr.{TRUE, FALSE}
import Ref.{NEW, PREVIOUS}
import ScaffoldCircuit.{conjunction, disjunction, neg}

/** Finite palindrome-prefix flag worker on an actual frozen mirror view.
  * The fixture loads a word, marks its lower endpoint with |, starts with !,
  * and executes local instructions with dots, building a persistent result stack.
  */
final class GSFlags(val circuit: Circuit, val prefix: String = "flags", val dual: Boolean = false) {
  val program: Program = if (dual) { GsDualFlags.compileDualFlags() } else { GsFlagHeads.compileFlags() }
  val readers: ReaderLiveness = GsHeadLiveness.analyzeReaders(program)
  val distances = new LiveDistances(circuit, program,
    if (dual) { GsDualFlags.DUAL_HEADS } else { GsFlagHeads.FLAG_HEADS }, prefix + ".distance")
  private val names = Vector.tabulate(readers.registers)(i => s"$prefix.r$i")
  private val rawNames = if (dual) { names } else { names.flatMap(name => Vector(name + ".forward", name + ".reverse")) }
  val streams = new StreamBank(circuit, Vector(prefix + ".begin", prefix + ".end") ++ rawNames)
  val begin: StreamHead = streams.heads(prefix + ".begin")
  val end: StreamHead = streams.heads(prefix + ".end")
  val registers: Vector[OrientedHead | MirrorHead] = names.map { name =>
    if (dual) { new OrientedHead(streams, name) } else { new MirrorHead(streams, name) }
  }
  val heads: Map[String, OrientedHead | MirrorHead] = readers.colors.map { case (head, color) => head -> registers(color) }
  val pcKey: String = prefix + ".pc"
  val phaseKey: String = prefix + ".phase"
  var pc: Value[Int] = circuit.get(PREVIOUS, pcKey, program.code.indices.toVector, program.start)
  var phase: Value[String] = circuit.get(PREVIOUS, phaseKey, Vector("idle", "broadcast", "maintenance", "run", "done"), "idle")
  val queueKey: String = prefix + ".queue"
  val remainingKey: String = prefix + ".remaining"
  private val queueNames = streams.queues.queues.keys.toVector
  var queue: Value[String] = circuit.get(PREVIOUS, queueKey, queueNames, queueNames.head)
  var remaining: Value[Int] = circuit.get(PREVIOUS, remainingKey, Vector(0, 1, 2, 3), 0)
  val returnKey: String = prefix + ".return"
  var returnPhase: Value[String] = circuit.get(PREVIOUS, returnKey, Vector("idle", "run", "done"), "idle")
  val postInputKey: String = prefix + ".post_input"
  var postInput: Value[String] = circuit.get(PREVIOUS, postInputKey, Vector("idle", "run", "done"), "idle")
  val cellKey: String = prefix + ".input_cell"
  var cell: Ref = circuit.getRef(PREVIOUS, cellKey)
  val initializedKey: String = prefix + ".initialized"
  var initialized: Expr = circuit.get(PREVIOUS, initializedKey, Vector(false, true), false).eqTo(true)
  val h = new Counter(distances.pool, prefix + ".h", Some("cells"))
  private val extraCounters: Vector[Counter] = if (dual) { Vector.empty } else {
    Vector("n", "b1", "bh1").map(name => new Counter(distances.pool, prefix + "." + name, Some("cells")))
  }
  val loadingCounters: Vector[Counter] = Vector(h, distances.length) ++ extraCounters
  val flagPool = new StackPool(circuit, Vector("cells" -> 1), Vector(false, true))
  val flags = new Stack(flagPool, prefix + ".output", Some("cells"))
  var emitted: Expr = FALSE

  private def read(head: String, enabled: Expr): Value[Any] = heads(head) match {
    case cursor: OrientedHead => cursor.read(enabled)
    case cursor: MirrorHead => cursor.read(enabled)
  }

  private def copy(target: Int, source: Int, enabled: Expr): Unit = {
    (registers(target), registers(source)) match {
      case (a: OrientedHead, b: OrientedHead) => a.copyFrom(b, enabled)
      case (a: MirrorHead, b: MirrorHead) => a.copyFrom(b, enabled)
      case _ => throw new IllegalStateException("mixed flag reader views")
    }
  }

  private def startHead(name: String, snapshot: StreamHead, reversed: Boolean, enabled: Expr): Unit = {
    heads(name) match {
      case cursor: OrientedHead => cursor.start(snapshot, reversed, enabled)
      case cursor: MirrorHead => cursor.start(begin, end, reversed, enabled)
    }
  }

  def tick(symbols: Option[Value[Any]] = None): Unit = {
    val char = symbols.getOrElse(circuit.input())
    val arrival = disjunction(char.eqTo('a'), char.eqTo('b'))
    val mark = char.eqTo('|')
    val start = char.eqTo('!')
    val dot = char.eqTo('.')
    val reset = char.eqTo('^')
    circuit.require(disjunction(Vector("idle", "run", "done").map(phase.eqTo)*), disjunction(arrival, mark))
    circuit.require(disjunction(phase.eqTo("idle"), phase.eqTo("done")), start)
    val oldPhase = phase
    val run = conjunction(dot, oldPhase.eqTo("run"))
    val broadcast = conjunction(dot, oldPhase.eqTo("broadcast"))
    val maintenance = conjunction(dot, oldPhase.eqTo("maintenance"))
    val events = program.code.indices.map(i => conjunction(run, pc.eqTo(i))).toVector
    val nextPc = mutable.LinkedHashMap.empty[Int, Expr]
    val copies = mutable.LinkedHashMap.empty[(Int, Int), Expr]
    val moves = mutable.LinkedHashMap.empty[(Int, Int), Expr]
    val requests = mutable.LinkedHashMap.empty[String, Expr]
    var halt = FALSE
    val flagEvents = VectorMap(false -> mutable.ArrayBuffer.empty[Expr], true -> mutable.ArrayBuffer.empty[Expr])
    def edge(target: Int, guard: Expr): Unit = { nextPc(target) = disjunction(nextPc.getOrElse(target, FALSE), guard) }
    def request(name: String, guard: Expr): Unit = { requests(name) = disjunction(requests.getOrElse(name, FALSE), guard) }
    for (((enabled, Row(event, targets)), state) <- events.zip(program.code).zipWithIndex) {
      def branch(decision: Expr): Unit = {
        edge(targets(0), conjunction(enabled, neg(decision)))
        edge(targets(1), conjunction(enabled, decision))
      }
      event match {
        case Event.Symbols(left, right) =>
          val a = read(left, enabled)
          val b = read(right, enabled)
          circuit.require(conjunction(neg(a.eqTo(None)), neg(b.eqTo(None))), enabled)
          branch(a.equal(b))
        case Event.Equal(left, right) => branch(distances.equal(left, right))
        case Event.Less(left, right) => branch(distances.less(left, right))
        case Event.Halt => halt = disjunction(halt, enabled)
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
            case Event.Flag(value) => flagEvents(value) += enabled
            case _ => throw new IllegalArgumentException("unsupported GS flag instruction")
          }
      }
    }
    distances.execute(events)
    for (((register, direction), enabled) <- moves) {
      val (name, needed) = registers(register) match {
        case cursor: OrientedHead => cursor.move(direction, enabled)
        case cursor: MirrorHead => cursor.move(direction, enabled)
      }
      request(name, needed)
    }
    for (((target, source), enabled) <- copies) { copy(target, source, enabled) }
    flags.clear(start)
    for ((value, conditions) <- flagEvents) {
      flags.push(data = Some(Value.constant(value)), enabled = disjunction(conditions.toSeq*), slot = Some(0))
    }
    emitted = disjunction(flagEvents.valuesIterator.flatMap(_.iterator).toSeq*)
    begin.queue.push(cell, broadcast)
    request(begin.queue.name, broadcast)
    for ((name, target) <- streams.queues.queues) { target.workUnit(conjunction(maintenance, queue.eqTo(name))) }
    end.followArrival(NEW, arrival)
    cell = Ref.select(arrival, NEW, cell)
    postInput = Value.select(arrival, Value(Vector("idle", "run", "done").map(name => name -> oldPhase.eqTo(name))), postInput)
    if (!dual) {
      val initial = neg(initialized)
      extraCounters(0).inc(initial, Some(0))
      extraCounters(0).inc(arrival, Some(1))
      extraCounters(0).inc(arrival, Some(2))
      extraCounters(1).inc(initial, Some(3))
      extraCounters(1).inc(arrival, Some(4))
      extraCounters(2).inc(initial, Some(5))
      extraCounters(2).inc(arrival, Some(6))
      extraCounters(2).inc(arrival, Some(7))
    }
    h.inc(arrival, Some(8))
    distances.loadOne(arrival)
    h.reset(mark)
    if (!dual) { extraCounters(2).copyFrom(extraCounters(1), mark) }
    initialized = TRUE
    val entry: VectorMap[(String, String), Option[(Counter, Int)]] = if (dual) {
      startHead("Origin", begin, false, start)
      startHead("TextOrigin", end, true, start)
      startHead("OriginalEnd", begin, true, start)
      VectorMap(("Lower", "Upper") -> Some((h, -1)),
        ("Origin", "OriginalEnd") -> Some((distances.length, -1)),
        ("Origin", "Upper") -> Some((distances.length, -1)),
        ("OriginalEnd", "Lower") -> Some((h, 1)),
        ("OriginalEnd", "TextOrigin") -> Some((distances.length, 1)),
        ("OriginalEnd", "Upper") -> None)
    } else {
      startHead("Origin", begin, false, start)
      startHead("OriginalEnd", end, true, start)
      VectorMap(("Origin", "OriginalEnd") -> Some((extraCounters(0), -1)),
        ("OriginalEnd", "Lower") -> Some((extraCounters(2), 1)),
        ("Origin", "Upper") -> Some((distances.length, -1)),
        ("OriginalEnd", "Upper") -> Some((extraCounters(1), 1)),
        ("Lower", "Upper") -> Some((h, -1)))
    }
    distances.initialize(entry, start)
    pc = Value.select(conjunction(run, neg(halt)), Value(nextPc), pc)
    pc = Value.select(start, Value.constant(program.start), pc)
    val finishedWork = conjunction(maintenance, remaining.eqTo(1))
    remaining = Value.select(maintenance, remaining.map(n => math.max(0, n - 1)), remaining)
    phase = Value.select(finishedWork, returnPhase, phase)
    val needed = disjunction(requests.values.toSeq*)
    queue = Value.select(needed, Value(requests), queue)
    remaining = Value.select(needed, Value.constant(3), remaining)
    returnPhase = Value.select(needed, Value.select(broadcast, postInput, Value.constant("run")), returnPhase)
    phase = Value.select(needed, Value.constant("maintenance"), phase)
    phase = Value.select(arrival, Value.constant("broadcast"), phase)
    phase = Value.select(start, Value.constant("run"), phase)
    phase = Value.select(halt, Value.constant("done"), phase)
    begin.reset(reset)
    end.reset(reset)
    loadingCounters.foreach(_.reset(reset))
    flags.clear(reset)
    phase = Value.select(reset, Value.constant("idle"), phase)
    initialized = conjunction(initialized, neg(reset))
  }

  def commit(): Unit = {
    distances.commit()
    loadingCounters.filterNot(_ eq distances.length).foreach(_.commit())
    streams.commit()
    registers.foreach {
      case cursor: OrientedHead => cursor.commit()
      case cursor: MirrorHead => cursor.commit()
    }
    flags.commit()
    for ((key, value) <- Vector[(String, Value[Any])](pcKey -> pc, phaseKey -> phase, queueKey -> queue,
      remainingKey -> remaining, returnKey -> returnPhase, postInputKey -> postInput)) { circuit.put(key, value) }
    circuit.put(initializedKey, Value.select(initialized, Value.constant(true), Value.constant(false)))
    circuit.putRef(cellKey, cell)
    circuit.put(prefix + ".emitted", Value.select(emitted, Value.constant(true), Value.constant(false)), Vector(false, true), false)
  }
}

object ScaffoldGsFlags {
  def fixture(dual: Boolean = false): (Circuit, GSFlags, Scaffold) = {
    val circuit = new Circuit("ab|!.^")
    circuit.put("input", Value.select(circuit.input().eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    val worker = new GSFlags(circuit, dual = dual)
    worker.tick()
    worker.commit()
    val (_, answer) = worker.flags.peek()
    (circuit, worker, circuit.machine(conjunction(worker.phase.eqTo("done"), neg(worker.flags.empty()), answer.eqTo(true))))
  }
}
