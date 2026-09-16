package pal

import scala.collection.immutable.VectorMap

import GsHeads.HEADS
import ScaffoldCircuit.{choose, conjunction as AND, disjunction as OR, neg}

/** A fixed burst of actual GS instructions in one ordinary input transition.
  *
  * `a`/`b`/`#` load the word, `!` freezes it, and each `.` performs `quantum`
  * instructions. Windowed positions and block cursors avoid per-instruction
  * heap cells and phase-address dispatch. This is a compiler integration test,
  * not the final PAL grammar; its input still includes the work protocol.
  */
final class WindowGS(val circuit: Circuit, val quantum: Int = 4, val prefix: String = "gs",
                     suppliedProgram: Option[Program] = None) {
  require(quantum >= 1, "a positive fixed instruction quantum is required")
  val program: Program = suppliedProgram.getOrElse(GsHeads.unitMoves(GsHeads.compileController()))
  val readers: ReaderLiveness = GsHeadLiveness.analyzeReaders(program)
  val readerNames: Vector[String] = Vector.tabulate(readers.registers)(i => s"$prefix.data$i")
  val table: ROM = ScaffoldRom.controllerTable(program, HEADS, Some(readers), readerNames)
  val positions: WindowPositions = new WindowPositions(circuit, HEADS, 2 * quantum + 4, prefix + ".positions")
  val stream: WindowStream = new WindowStream(circuit, Vector(prefix + ".begin", prefix + ".end") ++ readerNames,
    2 * quantum + 4, prefix + ".stream")
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
    positions.move("OriginalEnd", 1, loading)
    end.move(1, loading)
    for (head <- readers.before(program.start)) {
      val source = if (head == "OriginalEnd") { end } else { begin }
      data(readerNames(readers.colors(head))).copyFrom(source, start)
    }
    mode = Value.select(start, Value.constant("run"), mode)
    for (_ <- 0 until quantum) {
      step(AND(char.eqTo('.'), mode.eqTo("run")))
    }
  }

  def step(active: Expr): Unit = {
    val fields = table.read(pc.bits)
    val opcode = fields("op")
    val left = positions.selectPosition(fields("left"))
    val right = positions.selectPosition(fields("right"))
    val (equal, less) = positions.comparePositions(left, right)
    val symbolTest = AND(active, opcode.eqTo("symbols"))
    val a = stream.selectHead(fields("data_left")).read(symbolTest)
    val b = stream.selectHead(fields("data_right")).read(symbolTest)
    val decision = choose(opcode.eqTo("equal"), equal, choose(opcode.eqTo("less"), less, a.equal(b)))
    val moving = AND(active, opcode.eqTo("move"))
    val copying = AND(active, opcode.eqTo("copy"))
    val forward = fields("direction").eqTo(1)
    val backward = fields("direction").eqTo(-1)
    for (name <- HEADS) {
      val target = fields("left").eqTo(name)
      positions.move(name, 1, AND(moving, target, forward))
      positions.move(name, -1, AND(moving, target, backward))
      positions.copyPosition(name, right, AND(copying, target))
    }
    val source = stream.selectHead(fields("data_source"))
    for ((name, head) <- data) {
      val target = fields("data_move").eqTo(name)
      head.move(1, AND(moving, target, forward))
      head.move(-1, AND(moving, target, backward))
      head.copyFrom(source, AND(copying, fields("data_target").eqTo(name)))
    }
    pc = Value.select(active, Value.select(decision, fields("yes"), fields("no")).asInstanceOf[Value[Int]], pc)
    found = OR(found, AND(active, opcode.eqTo("border")))
    mode = Value.select(AND(active, opcode.eqTo("halt")), Value.constant("done"), mode)
  }

  def commit(): Unit = {
    positions.commit()
    stream.commit()
    circuit.put(pcKey, pc)
    circuit.put(modeKey, mode)
    circuit.put(foundKey, Value.select(found, Value.constant(true), Value.constant(false)))
  }
}

object ScaffoldWindowGs {
  def fixture(quantum: Int = 4, program: Option[Program] = None): (Circuit, WindowGS, Scaffold) = {
    val circuit = new Circuit("ab#!.")
    val worker = new WindowGS(circuit, quantum, suppliedProgram = program)
    worker.runRound()
    worker.commit()
    (circuit, worker, circuit.machine(AND(worker.mode.eqTo("done"), worker.found)))
  }
}
