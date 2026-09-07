package pal

import scala.collection.immutable.VectorMap
import Expr.{FALSE, TRUE}
import Ref.PREVIOUS
import ScaffoldCircuit.{choose, conjunction as AND, disjunction as OR, neg}

/** GS matcher and proper-prefix flags on the original input-node stream.
  *
  * Every actual input character advances the global raw end once. Frozen views
  * are cursor snapshots into that stream: reverse views read just left of their
  * boundary cursor. They never copy, pad, or append synthetic input symbols.
  */
trait WindowWorkerLike {
  def output: Expr
  def mode: Value[String]
  def flagPool: Option[FlagPackets]
  def flags: Option[FlagStack]
  def arrive(): Unit
  def resetFlags(enabled: Expr): Unit
  def start(enabled: Expr): Unit
  def mark(enabled: Expr): Unit
  def service(): Unit
  def commit(): Unit
}

final class WindowWorker(val circuit: Circuit, val prefix: String, val quantum: Int,
                         val program: Program, names: Seq[String], val isFlags: Boolean = false)
  extends WindowWorkerLike {
  if (quantum < 1) {
    throw new IllegalArgumentException("a positive finite service quantum is required")
  }

  val readers: ReaderLiveness = GsHeadLiveness.analyzeReaders(program)
  val readerNames: Vector[String] = Vector.tabulate(readers.registers)(index => s"$prefix.data$index")
  private val movement = program.code.iterator.flatMap { instruction =>
    instruction.event match {
      case Event.Move(moves) => moves.iterator.map(move => math.abs(move.delta))
      case _ => Iterator.empty
    }
  }.maxOption.getOrElse(1)
  val hKey: String = prefix + ".h"
  val distances: WindowLiveDistances = new WindowLiveDistances(
    circuit, program, names, 1 + 2 * quantum * movement, prefix + ".distance",
    if (isFlags) { Vector(hKey) } else { Vector.empty }, availabilityDistance = false)
  val table: ROM = ScaffoldRom.controllerTable(
    program, names, Some(readers), readerNames, batched = true, augment = Some(distances.augmentRows))
  val stream: WindowStream = new WindowStream(
    circuit, Vector(prefix + ".begin", prefix + ".end") ++ readerNames,
    3 + quantum * movement, prefix + ".stream")
  val begin: WindowHead = stream.heads(prefix + ".begin")
  val end: WindowHead = stream.heads(prefix + ".end")
  val data: VectorMap[String, WindowHead] = VectorMap.from(readerNames.map(name => name -> stream.heads(name)))
  var reverse: VectorMap[String, Expr] = VectorMap.from(readerNames.map { name =>
    name -> circuit.get(PREVIOUS, name + ".reverse", Vector(false, true), false).eqTo(true)
  })
  val pcKey: String = prefix + ".pc"
  val modeKey: String = prefix + ".mode"
  var pc: Value[Int] = circuit.get(PREVIOUS, pcKey, program.code.indices.toVector, program.start)
  var mode: Value[String] = circuit.get(PREVIOUS, modeKey, Vector("idle", "run", "done"), "idle")
  var output: Expr = FALSE
  val flagPool: Option[FlagPackets] = if (isFlags) { Some(new FlagPackets(circuit, quantum, prefix + ".packets")) } else { None }
  val flags: Option[FlagStack] = flagPool.map(pool => new FlagStack(pool, prefix + ".output"))

  def arrive(): Unit = {
    end.move(1)
    distances.loadOne(TRUE)
    if (isFlags) { distances.values.add(hKey, 1) }
  }

  private def rawStart(head: String, source: WindowHead, reversed: Boolean, enabled: Expr): Unit = {
    val name = readerNames(readers.colors(head))
    data(name).copyFrom(source, enabled)
    reverse = reverse.updated(name, choose(enabled, if (reversed) { TRUE } else { FALSE }, reverse(name)))
  }

  def resetFlags(enabled: Expr): Unit = {
    val result = flags.getOrElse(throw new IllegalArgumentException("only flag workers have a segment builder"))
    begin.copyFrom(end, enabled)
    distances.values.reset(distances.lengthKey, enabled)
    distances.values.reset(hKey, enabled)
    result.clear(enabled)
    mode = Value.select(enabled, Value.constant("idle"), mode)
  }

  def start(enabled: Expr): Unit = {
    if (isFlags) {
      circuit.require(neg(mode.eqTo("run")), enabled)
      rawStart("Origin", begin, reversed = false, enabled)
      rawStart("TextOrigin", end, reversed = true, enabled)
      rawStart("OriginalEnd", begin, reversed = true, enabled)
      distances.initializeValues(VectorMap(
        ("Lower", "Upper") -> Some((hKey, -1)),
        ("Origin", "OriginalEnd") -> Some((distances.lengthKey, -1)),
        ("Origin", "Upper") -> Some((distances.lengthKey, -1)),
        ("OriginalEnd", "Lower") -> Some((hKey, 1)),
        ("OriginalEnd", "TextOrigin") -> Some((distances.lengthKey, 1)),
        ("OriginalEnd", "Upper") -> None), enabled)
      flags.foreach(_.clear(enabled))
    } else {
      rawStart("Origin", end, reversed = true, enabled)
      rawStart("Tail", end, reversed = false, enabled)
      distances.initializeValues(VectorMap(("Origin", "Tail") -> Some((distances.lengthKey, -1))), enabled)
    }
    pc = Value.select(enabled, Value.constant(program.start), pc)
    mode = Value.select(enabled, Value.constant("run"), mode)
  }

  def mark(enabled: Expr): Unit = distances.values.reset(hKey, enabled)

  private def orientation(which: Value[Any]): Expr = {
    OR(reverse.iterator.map { case (name, value) => AND(which.eqTo(name), value) }.toSeq*)
  }

  private def read(which: Value[Any], enabled: Expr): Value[Any] = {
    val head = stream.selectHead(which)
    head.offset = Bits.select(orientation(which), head.offset.add(-1), head.offset)
    head.read(enabled)
  }

  def service(): Unit = {
    val writer = flags.map(new PacketWriter(_))
    for (_ <- 0 until quantum) {
      step(mode.eqTo("run"), writer)
      Expr.clearExpressionCache()
    }
  }

  private def step(active: Expr, writer: Option[PacketWriter]): Unit = {
    val fields = table.read(pc.bits)
    val opcode = fields("op")
    val (equal, less) = distances.compare(fields)
    val symbolTest = AND(active, opcode.eqTo("symbols"))
    val a = read(fields("data_left"), symbolTest)
    val b = read(fields("data_right"), symbolTest)
    val available = stream.selectHead(fields("data_left")).available()
    val decision = choose(opcode.eqTo("equal"), equal,
      choose(opcode.eqTo("less"), less,
        choose(opcode.eqTo("available"), available, a.equal(b))))
    circuit.require(equal, AND(active, opcode.eqTo("assert_equal")))
    if (!isFlags) {
      val matched = AND(active, opcode.eqTo("match"))
      val bName = readerNames(readers.colors("B"))
      circuit.require(neg(data(bName).available()), matched)
      output = OR(output, matched)
    }
    distances.execute(fields, active)
    val source = stream.selectHead(fields("data_source"))
    val reverseSource = orientation(fields("data_source"))
    for ((name, head) <- data) {
      val rawDelta = fields("data_delta." + name)
      val delta = Value.select(reverse(name), rawDelta.map {
        case amount: Int => -amount
        case amount => throw new IllegalArgumentException(s"non-integer head delta: $amount")
      }, rawDelta)
      head.moveSelected(delta, active)
      val copying = AND(active, opcode.eqTo("copy"), fields("data_target").eqTo(name))
      head.copyFrom(source, copying)
      reverse = reverse.updated(name, choose(copying, reverseSource, reverse(name)))
    }
    if (isFlags) {
      writer.get.push(fields("bit").eqTo(true), AND(active, opcode.eqTo("flag")))
      mode = Value.select(AND(active, opcode.eqTo("halt")), Value.constant("done"), mode)
    } else {
      circuit.require(FALSE, AND(active, opcode.eqTo("halt")))
    }
    pc = Value.select(active, Value.select(decision, fields("yes").asInstanceOf[Value[Int]], fields("no").asInstanceOf[Value[Int]]), pc)
  }

  def commit(): Unit = {
    distances.commit()
    stream.commit()
    circuit.put(pcKey, pc)
    circuit.put(modeKey, mode)
    for ((name, bit) <- reverse) {
      circuit.put(name + ".reverse", Value.select(bit, Value.constant(true), Value.constant(false)))
    }
    flags.foreach(_.commit())
    circuit.put(prefix + ".matched", Value.select(output, Value.constant(true), Value.constant(false)), Vector(false, true), false)
  }
}

object ScaffoldWindowWorkers {
  def matcher(circuit: Circuit, prefix: String = "matcher", quantum: Int = 512): WindowWorker = {
    new WindowWorker(circuit, prefix, quantum, GsMatchHeads.compileMatcher(unit = false), GsMatchHeads.MATCH_HEADS)
  }
  def flags(circuit: Circuit, prefix: String = "flags", quantum: Int = 1024): WindowWorker = {
    new WindowWorker(circuit, prefix, quantum, GsDualFlags.compileDualFlags(unit = false), GsDualFlags.DUAL_HEADS, isFlags = true)
  }
}
