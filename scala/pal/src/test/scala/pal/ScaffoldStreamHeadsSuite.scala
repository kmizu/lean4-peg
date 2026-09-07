package pal

import scala.collection.mutable

import Expr.FALSE
import ScaffoldCircuit.{conjunction, disjunction, neg, choose}
import Ref.{NEW, PREVIOUS}
import TestScaffoldCircuitProgram.scalar

/** Stream heads driven by a small worker that follows the `scaffold_gs_matcher` protocol.
  *
  * `scaffold_stream_heads.py` has no unit test of its own; here every public
  * method is exercised through three register kinds (`PatternTextHead`,
  * `OrientedHead`, `MirrorHead`), the lowered rule text is pinned against a
  * Python driver constructing the same fixture, and the machines are run against
  * a position model of what each head should read.
  */
object ScaffoldStreamHeadsSuite {

  val KINDS: Vector[String] = Vector("pattern", "oriented", "mirror")

  /** A register of the worker: one of the three head kinds behind a common interface. */
  sealed trait Register {
    def read(enabled: Expr): Value[Any]
    def move(direction: Int, enabled: Expr): (String, Expr)
    def copyFrom(other: Register, enabled: Expr): Unit
    def commit(): Unit
  }

  final case class PatternRegister(head: PatternTextHead) extends Register {
    def read(enabled: Expr): Value[Any] = head.read(enabled)
    def move(direction: Int, enabled: Expr): (String, Expr) = head.move(direction, enabled)
    def copyFrom(other: Register, enabled: Expr): Unit = {
      other match {
        case PatternRegister(source) => head.copyFrom(source, enabled)
        case _ => throw new IllegalArgumentException("register kinds differ")
      }
    }
    def commit(): Unit = head.commit()
  }

  final case class OrientedRegister(head: OrientedHead) extends Register {
    def read(enabled: Expr): Value[Any] = head.read(enabled)
    def move(direction: Int, enabled: Expr): (String, Expr) = head.move(direction, enabled)
    def copyFrom(other: Register, enabled: Expr): Unit = {
      other match {
        case OrientedRegister(source) => head.copyFrom(source, enabled)
        case _ => throw new IllegalArgumentException("register kinds differ")
      }
    }
    def commit(): Unit = head.commit()
  }

  final case class MirrorRegister(head: MirrorHead) extends Register {
    def read(enabled: Expr): Value[Any] = head.read(enabled)
    def move(direction: Int, enabled: Expr): (String, Expr) = head.move(direction, enabled)
    def copyFrom(other: Register, enabled: Expr): Unit = {
      other match {
        case MirrorRegister(source) => head.copyFrom(source, enabled)
        case _ => throw new IllegalArgumentException("register kinds differ")
      }
    }
    def commit(): Unit = head.commit()
  }

  /** Letters a/b arrive and are broadcast, `!` starts the two registers, `.` services one
    * broadcast push or maintenance unit, and `> < ] [ c ?` move r0/r1, copy r1 from r0 and
    * observe both reads (during the run phase only). Scheduling copies
    * `scaffold_gs_matcher.tick`: one queue operation per instruction, three work units per request.
    */
  final class StreamWorker(val circuit: Circuit, val kind: String, val prefix: String = "w") {
    private val suffixes: Vector[String] = kind match {
      case "pattern" => Vector(".pattern", ".text")
      case "oriented" => Vector("")
      case "mirror" => Vector(".forward", ".reverse")
      case other => throw new IllegalArgumentException(s"unknown register kind $other")
    }
    val registerNames: Vector[String] = Vector(prefix + ".r0", prefix + ".r1")
    val bank: StreamBank = new StreamBank(circuit, Vector(prefix + ".begin", prefix + ".end") ++
      registerNames.flatMap(name => suffixes.map(suffix => name + suffix)))
    val begin: StreamHead = bank.heads(prefix + ".begin")
    val end: StreamHead = bank.heads(prefix + ".end")
    val registers: Vector[Register] = registerNames.map { name =>
      kind match {
        case "pattern" => PatternRegister(new PatternTextHead(bank, name))
        case "oriented" => OrientedRegister(new OrientedHead(bank, name))
        case _ => MirrorRegister(new MirrorHead(bank, name))
      }
    }
    val phaseKey: String = prefix + ".phase"
    var phase: Value[String] = circuit.get(PREVIOUS, phaseKey, Vector("idle", "broadcast", "maintenance", "run"), "idle")
    val activeKey: String = prefix + ".active"
    var active: Expr = circuit.get(PREVIOUS, activeKey, Vector(false, true), false).eqTo(true)
    val queueKey: String = prefix + ".queue"
    val remainingKey: String = prefix + ".remaining"
    private val queueNames: Vector[String] = bank.queues.queues.keys.toVector
    var queue: Value[String] = circuit.get(PREVIOUS, queueKey, queueNames, queueNames.head)
    var remaining: Value[Int] = circuit.get(PREVIOUS, remainingKey, Vector(0, 1, 2, 3), 0)
    val returnKey: String = prefix + ".return"
    val indexKey: String = prefix + ".broadcast_index"
    var returnPhase: Value[String] = circuit.get(PREVIOUS, returnKey, Vector("broadcast", "run"), "broadcast")
    val broadcastQueues: Vector[String] = kind match {
      case "pattern" => begin.queue.name +: registers.map { case PatternRegister(head) => head.text.queue.name; case _ => "" }
      case _ => Vector(begin.queue.name)
    }
    var broadcastIndex: Value[Int] = circuit.get(PREVIOUS, indexKey, (0 to broadcastQueues.length).toVector, 0)
    val cellKey: String = prefix + ".input_cell"
    var cell: Ref = circuit.getRef(PREVIOUS, cellKey)
    val symbolKeys: Vector[String] = Vector(prefix + ".symbol0", prefix + ".symbol1")
    var symbols: Vector[Value[Any]] = symbolKeys.map(key => circuit.get[Any](PREVIOUS, key, Vector('a', 'b', '#', None), None))
    val availableKey: String = prefix + ".available"
    var available: Expr = circuit.get(PREVIOUS, availableKey, Vector(false, true), false).eqTo(true)
    val sameKey: String = prefix + ".same"
    var same: Expr = circuit.get(PREVIOUS, sameKey, Vector(false, true), false).eqTo(true)

    def tick(): Unit = {
      val c = circuit
      val char = c.input()
      val arrival = disjunction(char.eqTo('a'), char.eqTo('b'))
      val start = char.eqTo('!')
      val dot = char.eqTo('.')
      c.require(disjunction(phase.eqTo("idle"), phase.eqTo("run")), disjunction(arrival, start))
      c.require(end.focus.present(), start)
      val running = phase.eqTo("run")
      val broadcast = conjunction(dot, phase.eqTo("broadcast"))
      val maintenance = conjunction(dot, phase.eqTo("maintenance"))
      val requests = mutable.LinkedHashMap.empty[String, Expr]
      def request(name: String, guard: Expr): Unit = { requests(name) = disjunction(requests.getOrElse(name, FALSE), guard) }
      for ((command, register, direction) <- Vector(('>', 0, 1), ('<', 0, -1), (']', 1, 1), ('[', 1, -1))) {
        val enabled = conjunction(char.eqTo(command), running)
        c.require(running, char.eqTo(command))
        val (name, needed) = registers(register).move(direction, enabled)
        request(name, needed)
      }
      val copying = conjunction(char.eqTo('c'), running)
      c.require(running, char.eqTo('c'))
      registers(1).copyFrom(registers(0), copying)
      val query = conjunction(char.eqTo('?'), running)
      c.require(running, char.eqTo('?'))
      val reads = registers.map(register => register.read(query))
      symbols = reads.zip(symbols).map { case (value, previous) => Value.select(query, value, previous) }
      same = choose(query, reads(0).equal(reads(1)), same)
      if (kind == "pattern") {
        registers(0) match {
          case PatternRegister(head) => available = choose(query, head.available(), available)
          case _ => ()
        }
      }
      // One broadcast queue is updated in this instruction. The explicit
      // maintenance state services its three work units before proceeding.
      val count = broadcastQueues.length
      val finished = choose(active, broadcastIndex.eqTo(count), broadcastIndex.eqTo(1))
      val push = conjunction(broadcast, neg(finished))
      for ((name, index) <- broadcastQueues.zipWithIndex) {
        val enabled = conjunction(push, broadcastIndex.eqTo(index))
        bank.queues.queues(name).push(cell, enabled)
        request(name, enabled)
      }
      for ((name, target) <- bank.queues.queues) { target.workUnit(conjunction(maintenance, queue.eqTo(name))) }
      end.followArrival(NEW, arrival)
      cell = Ref.select(arrival, NEW, cell)
      (registers(0), registers(1)) match {
        case (PatternRegister(first), PatternRegister(second)) =>
          first.start(end, start)
          second.start(begin, start)
        case (OrientedRegister(first), OrientedRegister(second)) =>
          first.start(begin, false, start)
          second.start(end, true, start)
        case (MirrorRegister(first), MirrorRegister(second)) =>
          first.start(begin, end, false, start)
          second.start(begin, end, true, start)
        case _ => throw new IllegalStateException("mixed register kinds")
      }
      active = disjunction(active, start)
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

    /** Python `finalize()`. */
    def commit(): Unit = {
      bank.commit()
      registers.foreach(_.commit())
      circuit.put(phaseKey, phase)
      circuit.put(queueKey, queue)
      circuit.put(remainingKey, remaining)
      circuit.put(returnKey, returnPhase)
      circuit.put(indexKey, broadcastIndex)
      for ((key, value) <- symbolKeys.zip(symbols)) { circuit.put(key, value) }
      for ((key, value) <- Vector((activeKey, active), (availableKey, available), (sameKey, same))) {
        circuit.put(key, Value.select(value, Value.constant(true), Value.constant(false)))
      }
      circuit.putRef(cellKey, cell)
    }
  }

  val ALPHABET = "ab!.><][c?"

  def fixture(kind: String): (Circuit, StreamWorker, Scaffold) = {
    val circuit = new Circuit(ALPHABET)
    circuit.put("input", Value.select(circuit.input().eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    val worker = new StreamWorker(circuit, kind)
    worker.tick()
    worker.commit()
    (circuit, worker, circuit.machine(worker.active))
  }

  /** The same worker in Python; prints the three lowered machines. */
  val pythonDriver: String =
    """from scaffold_circuit import (Circuit, Value, Ref, NEW, PREVIOUS, TRUE, FALSE,
      |                              conjunction, disjunction, neg, choose)
      |from scaffold_stream_heads import StreamBank, PatternTextHead, OrientedHead, MirrorHead
      |from symbolic_sca2peg import share_expressions
      |
      |SUFFIXES = {"pattern": (".pattern", ".text"), "oriented": ("",), "mirror": (".forward", ".reverse")}
      |HEADS = {"pattern": PatternTextHead, "oriented": OrientedHead, "mirror": MirrorHead}
      |
      |
      |class StreamWorker:
      |  def __init__(self, circuit, kind, prefix="w"):
      |    self.circuit, self.kind, self.prefix = circuit, kind, prefix
      |    names = (prefix + ".r0", prefix + ".r1")
      |    self.bank = StreamBank(circuit, (prefix + ".begin", prefix + ".end",
      |                                     *(name + suffix for name in names for suffix in SUFFIXES[kind])))
      |    self.begin, self.end = self.bank.heads[prefix + ".begin"], self.bank.heads[prefix + ".end"]
      |    self.registers = [HEADS[kind](self.bank, name) for name in names]
      |    self.phase_key = prefix + ".phase"
      |    self.phase = circuit.get(PREVIOUS, self.phase_key, ("idle", "broadcast", "maintenance", "run"), "idle")
      |    self.active_key = prefix + ".active"
      |    self.active = circuit.get(PREVIOUS, self.active_key, (False, True), False).eq(True)
      |    self.queue_key, self.remaining_key = prefix + ".queue", prefix + ".remaining"
      |    qnames = tuple(self.bank.queues.queues)
      |    self.queue = circuit.get(PREVIOUS, self.queue_key, qnames, qnames[0])
      |    self.remaining = circuit.get(PREVIOUS, self.remaining_key, (0, 1, 2, 3), 0)
      |    self.return_key, self.index_key = prefix + ".return", prefix + ".broadcast_index"
      |    self.return_phase = circuit.get(PREVIOUS, self.return_key, ("broadcast", "run"), "broadcast")
      |    self.broadcast_queues = ((self.begin.queue.name, *(head.text.queue.name for head in self.registers))
      |                             if kind == "pattern" else (self.begin.queue.name,))
      |    self.broadcast_index = circuit.get(PREVIOUS, self.index_key, tuple(range(len(self.broadcast_queues) + 1)), 0)
      |    self.cell_key = prefix + ".input_cell"
      |    self.cell = circuit.get_ref(PREVIOUS, self.cell_key)
      |    self.symbol_keys = (prefix + ".symbol0", prefix + ".symbol1")
      |    self.symbols = [circuit.get(PREVIOUS, key, ("a", "b", "#", None), None) for key in self.symbol_keys]
      |    self.available_key = prefix + ".available"
      |    self.available = circuit.get(PREVIOUS, self.available_key, (False, True), False).eq(True)
      |    self.same_key = prefix + ".same"
      |    self.same = circuit.get(PREVIOUS, self.same_key, (False, True), False).eq(True)
      |
      |  def tick(self):
      |    c = self.circuit
      |    char = c.input()
      |    arrival = disjunction(char.eq("a"), char.eq("b"))
      |    start, dot = char.eq("!"), char.eq(".")
      |    c.require(disjunction(self.phase.eq("idle"), self.phase.eq("run")), disjunction(arrival, start))
      |    c.require(self.end.focus.present(), start)
      |    running = self.phase.eq("run")
      |    broadcast = conjunction(dot, self.phase.eq("broadcast"))
      |    maintenance = conjunction(dot, self.phase.eq("maintenance"))
      |    requests = {}
      |
      |    def request(name, guard):
      |      requests[name] = disjunction(requests.get(name, FALSE), guard)
      |
      |    for command, register, direction in ((">", 0, 1), ("<", 0, -1), ("]", 1, 1), ("[", 1, -1)):
      |      enabled = conjunction(char.eq(command), running)
      |      c.require(running, char.eq(command))
      |      name, needed = self.registers[register].move(direction, enabled)
      |      request(name, needed)
      |    copying = conjunction(char.eq("c"), running)
      |    c.require(running, char.eq("c"))
      |    self.registers[1].copy_from(self.registers[0], copying)
      |    query = conjunction(char.eq("?"), running)
      |    c.require(running, char.eq("?"))
      |    reads = [register.read(query) for register in self.registers]
      |    self.symbols = [Value.select(query, value, previous) for value, previous in zip(reads, self.symbols)]
      |    self.same = choose(query, reads[0].equal(reads[1]), self.same)
      |    if self.kind == "pattern":
      |      self.available = choose(query, self.registers[0].available(), self.available)
      |    count = len(self.broadcast_queues)
      |    finished = choose(self.active, self.broadcast_index.eq(count), self.broadcast_index.eq(1))
      |    push = conjunction(broadcast, neg(finished))
      |    for index, name in enumerate(self.broadcast_queues):
      |      enabled = conjunction(push, self.broadcast_index.eq(index))
      |      self.bank.queues.queues[name].push(self.cell, enabled)
      |      request(name, enabled)
      |    for name, target in self.bank.queues.queues.items():
      |      target.work_unit(conjunction(maintenance, self.queue.eq(name)))
      |    self.end.follow_arrival(NEW, arrival)
      |    self.cell = Ref.select(arrival, NEW, self.cell)
      |    first, second = self.registers
      |    if self.kind == "pattern":
      |      first.start(self.end, start)
      |      second.start(self.begin, start)
      |    elif self.kind == "oriented":
      |      first.start(self.begin, False, start)
      |      second.start(self.end, True, start)
      |    else:
      |      first.start(self.begin, self.end, False, start)
      |      second.start(self.begin, self.end, True, start)
      |    self.active = disjunction(self.active, start)
      |    self.broadcast_index = Value.select(push, self.broadcast_index.map(lambda n: min(n + 1, count)), self.broadcast_index)
      |    self.broadcast_index = Value.select(arrival, Value.constant(0), self.broadcast_index)
      |    finished_work = conjunction(maintenance, self.remaining.eq(1))
      |    self.remaining = Value.select(maintenance, self.remaining.map(lambda n: max(0, n - 1)), self.remaining)
      |    self.phase = Value.select(finished_work, self.return_phase, self.phase)
      |    self.phase = Value.select(conjunction(broadcast, finished),
      |                              Value.select(self.active, Value.constant("run"), Value.constant("idle")), self.phase)
      |    needed = disjunction(*requests.values())
      |    self.queue = Value.select(needed, Value(requests), self.queue)
      |    self.remaining = Value.select(needed, Value.constant(3), self.remaining)
      |    self.return_phase = Value.select(needed, Value.select(push, Value.constant("broadcast"), Value.constant("run")), self.return_phase)
      |    self.phase = Value.select(needed, Value.constant("maintenance"), self.phase)
      |    self.phase = Value.select(arrival, Value.constant("broadcast"), self.phase)
      |    self.phase = Value.select(start, Value.constant("run"), self.phase)
      |
      |  def finalize(self):
      |    self.bank.finalize()
      |    for register in self.registers:
      |      register.finalize()
      |    for key, value in ((self.phase_key, self.phase), (self.queue_key, self.queue),
      |                       (self.remaining_key, self.remaining), (self.return_key, self.return_phase),
      |                       (self.index_key, self.broadcast_index)):
      |      self.circuit.put(key, value)
      |    for key, value in zip(self.symbol_keys, self.symbols):
      |      self.circuit.put(key, value)
      |    for key, value in ((self.active_key, self.active), (self.available_key, self.available), (self.same_key, self.same)):
      |      self.circuit.put(key, Value.select(value, Value.constant(True), Value.constant(False)))
      |    self.circuit.put_ref(self.cell_key, self.cell)
      |
      |
      |def fixture(kind):
      |  circuit = Circuit("ab!.><][c?")
      |  circuit.put("input", Value.select(circuit.input().eq("b"), Value.constant("b"), Value.constant("a")), tuple("ab"), "a")
      |  worker = StreamWorker(circuit, kind)
      |  worker.tick()
      |  worker.finalize()
      |  return circuit, worker, circuit.machine(worker.active)
      |
      |
      |for kind in ("pattern", "oriented", "mirror"):
      |  with share_expressions():
      |    _, _, machine = fixture(kind)
      |  print(machine.compile(), end="")
      |""".stripMargin

  /** What each register should read: a frozen view string and a position in it. */
  final class RegisterModel(var view: String, var position: Int) {
    def read: Any = if (position < view.length) { view.charAt(position) } else { None }
  }

  /** The two registers' views after `!` on `prefix`, per kind (see the head Scaladocs). */
  def model(kind: String, prefix: String): Vector[RegisterModel] = {
    kind match {
      case "pattern" => Vector(new RegisterModel(prefix.reverse, 0), new RegisterModel(prefix.reverse, prefix.length))
      case "oriented" => Vector(new RegisterModel(prefix, 0), new RegisterModel(prefix.reverse, 0))
      case _ =>
        val mirror = prefix + "#" + prefix.reverse
        Vector(new RegisterModel(mirror, 0), new RegisterModel(mirror, mirror.length))
    }
  }
}

class ScaffoldStreamHeadsSuite extends munit.FunSuite {
  import ScaffoldStreamHeadsSuite.*

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  private lazy val fixtures: Map[String, (Circuit, StreamWorker, Scaffold)] = KINDS.map(kind => kind -> Expr.share { fixture(kind) }).toMap

  test("every head kind lowers to the same rules as the Python driver") {
    val out = new StringBuilder
    for (kind <- KINDS) { out.append(fixtures(kind)._3.compile()) }
    PyDiff.assertSameAsPython(out.toString, "-c", pythonDriver)
  }

  /** Runs one fixture: loads letters, starts, then executes commands with maintenance drains. */
  private final class Run(kind: String) {
    val (circuit, worker, machine) = fixtures(kind)
    var node: Node = machine.initialNode()
    val prefix = new StringBuilder

    def phase: Any = scalar(circuit, node, worker.phaseKey)

    def step(char: Char): Unit = {
      node = machine.step(node, char).get
      assertEquals(scalar(circuit, node, "circuit.fault"), false, (kind, char))
    }

    def drain(target: String): Unit = {
      var budget = 200
      while (phase != target) {
        assert(budget > 0, (kind, phase, target))
        step('.')
        budget -= 1
      }
    }

    def load(letters: String): Unit = {
      for (char <- letters) {
        step(char)
        drain("idle")
        prefix.append(char)
      }
    }

    def start(): Vector[RegisterModel] = {
      step('!')
      drain("run")
      model(kind, prefix.toString)
    }

    def arrive(char: Char, registers: Vector[RegisterModel]): Unit = {
      step(char)
      drain("run")
      // Only pattern/text heads see text that arrives after the start.
      if (kind == "pattern") { registers.foreach(register => register.view += char) }
    }

    def command(char: Char, registers: Vector[RegisterModel]): Unit = {
      char match {
        case '>' => registers(0).position += 1
        case '<' => registers(0).position -= 1
        case ']' => registers(1).position += 1
        case '[' => registers(1).position -= 1
        case 'c' =>
          registers(1).view = registers(0).view
          registers(1).position = registers(0).position
        case _ => ()
      }
      step(char)
      drain("run")
      if (char == '?') {
        for ((register, key) <- registers.zip(worker.symbolKeys)) {
          assertEquals(scalar(circuit, node, key), register.read, (kind, key, register.view, register.position))
        }
        assertEquals(scalar(circuit, node, worker.sameKey), registers(0).read == registers(1).read, kind)
        if (kind == "pattern") {
          assertEquals(scalar(circuit, node, worker.availableKey), registers(0).position < registers(0).view.length, kind)
        }
      }
    }
  }

  test("pattern/text registers read the reversed prefix, then the text, in both directions") {
    val run = new Run("pattern")
    run.load("abb")
    val registers = run.start()
    for (char <- "?>?>?>?") { run.command(char, registers) }
    run.arrive('b', registers)
    run.arrive('a', registers)
    for (char <- "?>?]?>?<?<?<?<?c?]?[?[?") { run.command(char, registers) }
  }

  test("oriented registers read forward from the beginning and backward from the end") {
    val run = new Run("oriented")
    run.load("abb")
    val registers = run.start()
    for (char <- "?>?>?>?<?]?]?]?[?c?]?[?[?[?") { run.command(char, registers) }
  }

  test("mirror registers read u # reverse(u) from either end") {
    val run = new Run("mirror")
    run.load("ab")
    val registers = run.start()
    for (char <- "?>?>?>?>?>?<?<?[?[?[?[?[?]?c?]?]?") { run.command(char, registers) }
  }

  test("commands outside the run phase and moves past the ends are faults") {
    val (circuit, _, machine) = fixtures("mirror")
    val idle = machine.step(machine.initialNode(), '>').get
    assertEquals(scalar(circuit, idle, "circuit.fault"), true)
    val run = new Run("mirror")
    run.load("a")
    val registers = run.start()
    for (char <- ">>>") { run.command(char, registers) }
    val past = machine.step(run.node, '>').get
    assertEquals(scalar(circuit, past, "circuit.fault"), true)
  }
}
