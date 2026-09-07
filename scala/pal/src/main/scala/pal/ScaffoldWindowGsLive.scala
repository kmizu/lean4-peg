package pal

import scala.collection.immutable.VectorMap

import Expr.clearExpressionCache
import GsHeads.HEADS
import ScaffoldCircuit.{choose, conjunction as AND, disjunction as OR, neg}

/** Windowed GS bursts with live difference registers and batch movement.
  *
  * The explicit `a`/`b`/`#`, `!`, `.` protocol remains a compiler integration
  * fixture. All instructions in one burst compile into one input-node transition.
  */
final class WindowGSLive(val circuit: Circuit, val quantum: Int = 4, val prefix: String = "gs",
                         suppliedProgram: Option[Program] = None) {
  require(quantum >= 1, "a positive fixed instruction quantum is required")
  val program: Program = suppliedProgram.getOrElse(GsHeads.compileController())
  val readers: ReaderLiveness = GsHeadLiveness.analyzeReaders(program)
  val readerNames: Vector[String] = Vector.tabulate(readers.registers)(i => s"$prefix.data$i")
  private val movement = program.code.iterator.collect { case Row(Event.Move(moves), _) =>
    moves.iterator.map(move => math.abs(move.delta)).maxOption.getOrElse(1)
  }.maxOption.getOrElse(1)
  val distances: WindowLiveDistances = new WindowLiveDistances(circuit, program, HEADS,
    1 + 2 * quantum * movement, prefix + ".distance")
  val table: ROM = ScaffoldRom.controllerTable(program, HEADS, Some(readers), readerNames,
    batched = true, augment = Some(distances.augmentRows))
  val stream: WindowStream = new WindowStream(circuit, Vector(prefix + ".begin", prefix + ".end") ++ readerNames,
    2 + quantum * movement, prefix + ".stream")
  val begin: WindowHead = stream.heads(prefix + ".begin")
  val end: WindowHead = stream.heads(prefix + ".end")
  val data: VectorMap[String, WindowHead] = VectorMap.from(readerNames.map(name => name -> stream.heads(name)))
  val pcKey: String = prefix + ".pc"
  val modeKey: String = prefix + ".mode"
  val foundKey: String = prefix + ".found"
  var pc: Value[Int] = circuit.get(Ref.PREVIOUS, pcKey, program.code.indices, program.start)
  var mode: Value[String] = circuit.get(Ref.PREVIOUS, modeKey, Vector("load", "run", "done"), "load")
  var found: Expr = circuit.get(Ref.PREVIOUS, foundKey, Vector(false, true), false).eqTo(true)

  def runRound(): Unit = {
    val char = circuit.input()
    val loading = AND(mode.eqTo("load"), OR("ab#".map(symbol => char.eqTo(symbol))*))
    val start = AND(mode.eqTo("load"), char.eqTo('!'))
    circuit.require(OR(loading, start, AND(neg(mode.eqTo("load")), char.eqTo('.'))))
    distances.loadOne(loading)
    end.move(1, loading)
    distances.initialize(start)
    for (head <- readers.before(program.start)) {
      val source = if (head == "OriginalEnd") { end } else { begin }
      data(readerNames(readers.colors(head))).copyFrom(source, start)
    }
    mode = Value.select(start, Value.constant("run"), mode)
    for (_ <- 0 until quantum) {
      step(AND(char.eqTo('.'), mode.eqTo("run")))
      clearExpressionCache()
    }
  }

  def step(active: Expr): Unit = {
    val fields = table.read(pc.bits)
    val opcode = fields("op")
    val (equal, less) = distances.compare(fields)
    val symbolTest = AND(active, opcode.eqTo("symbols"))
    val a = stream.selectHead(fields("data_left")).read(symbolTest)
    val b = stream.selectHead(fields("data_right")).read(symbolTest)
    val decision = choose(opcode.eqTo("equal"), equal, choose(opcode.eqTo("less"), less, a.equal(b)))
    distances.execute(fields, active)
    val source = stream.selectHead(fields("data_source"))
    for ((name, head) <- data) {
      head.moveSelected(fields("data_delta." + name), active)
      head.copyFrom(source, AND(active, opcode.eqTo("copy"), fields("data_target").eqTo(name)))
    }
    pc = Value.select(active, Value.select(decision, fields("yes"), fields("no")).asInstanceOf[Value[Int]], pc)
    found = OR(found, AND(active, opcode.eqTo("border")))
    mode = Value.select(AND(active, opcode.eqTo("halt")), Value.constant("done"), mode)
  }

  def commit(): Unit = {
    distances.commit()
    stream.commit()
    circuit.put(pcKey, pc)
    circuit.put(modeKey, mode)
    circuit.put(foundKey, Value.select(found, Value.constant(true), Value.constant(false)))
  }
}

object ScaffoldWindowGsLive {
  def fixture(quantum: Int = 4, program: Option[Program] = None): (Circuit, WindowGSLive, Scaffold) = {
    val circuit = new Circuit("ab#!.")
    val worker = new WindowGSLive(circuit, quantum, suppliedProgram = program)
    worker.runRound()
    worker.commit()
    (circuit, worker, circuit.machine(AND(worker.mode.eqTo("done"), worker.found)))
  }
}
