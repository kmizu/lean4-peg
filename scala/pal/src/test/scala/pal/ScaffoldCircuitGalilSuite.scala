package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable
import TestScaffoldCircuitProgram.scalar
import ScaffoldCircuitGalil.{Built, Views}

/** State-level comparison against the original SCAVM source.
  *
  * Python supplies only native state samples and expected transitions. Encoding,
  * execution of the lowered circuit, and every field/stack/focus assertion run in
  * Scala. The sample words and mode-discrimination keys are exactly those of
  * test_scaffold_circuit_galil.py, including the old experimental match clock.
  */
object ScaffoldCircuitGalilSuite {
  final case class Field(key: String, original: String, kind: String)
  final case class Layout(stacks: Vector[(Stack, String)], fields: Vector[Field], focuses: Vector[String]) {
    def specification: Json = Json.obj(
      "stacks" -> Json.Arr(stacks.map { case (stack, kind) => Json.strings(Vector(stack.name, kind)) }),
      "fields" -> Json.Arr(fields.map(field => Json.strings(Vector(field.key, field.original, field.kind)))),
      "focuses" -> Json.strings(focuses))
  }

  def layout(v: Views): Layout = {
    val stacks = mutable.ArrayBuffer.empty[(Stack, String)]
    val fields = mutable.ArrayBuffer.empty[Field]
    val focuses = mutable.ArrayBuffer.empty[String]
    val s = v.search
    val ch = v.chain
    val counters = mutable.ArrayBuffer.from(v.counters ++ Vector(s.lower, s.span, s.work, s.debt,
      ch.h, ch.lag, ch.distance, ch.boundary, ch.last, ch.margin, ch.cycle))
    for (head <- v.heads) {
      val inner = head.head
      val queue = inner.incoming
      fields += Field(head.gapKey, head.gapKey, "bool")
      fields += Field(queue.phaseKey, queue.phaseKey, "str")
      focuses += inner.focusKey
      stacks ++= (Vector(inner.leftStack, inner.rightStack) ++ queue.stacks.values).map(_ -> "input")
      counters ++= Vector(queue.m, queue.c)
    }
    for (counter <- counters) { stacks ++= Vector(counter.positiveStack -> "counter", counter.negativeStack -> "counter") }
    for (program <- Vector(v.fpp, s.program)) {
      fields += Field(program.pcKey, program.pcKey, "int")
      fields += Field(program.doneKey, program.name + ".halted", "bool")
    }
    for (tape <- v.fpp.tapes ++ s.program.tapes ++ Vector(ch.period)) {
      fields += Field(tape.symbolKey, tape.symbolKey, "str")
      stacks ++= Vector(tape.left -> tape.name, tape.right -> tape.name)
    }
    fields ++= Vector("g.mode" -> "str", "g.clock" -> "int", "g.out" -> "bool", "g.replaying" -> "bool",
      "g.odd" -> "bool", "g.pair" -> "int", "sp.mode" -> "str", "sp.final" -> "bool", "sp.quarter" -> "int",
      "ch.mode" -> "str", "ch.dir" -> "int", "ch.phase" -> "int", "ch.only" -> "bool").map {
      case (key, kind) => Field(key, key, kind)
    }
    Layout(stacks.toVector, fields.toVector, focuses.toVector)
  }

  private def json(value: Any): Json = value match {
    case None => Json.Null
    case b: Boolean => Json.Bool(b)
    case i: Int => Json.Num(i.toLong)
    case c: Char => Json.Str(c.toString)
    case s: String => Json.Str(s)
    case other => throw new IllegalArgumentException(s"unsupported observer value: $other")
  }

  def circuitValues(circuit: Circuit, root: Node, stack: Stack, kind: String): Vector[Json] = {
    var current = root.pointers(stack.rootKey)
    var tag = scalar(circuit, root, stack.tagKey).asInstanceOf[CellTag]
    val result = Vector.newBuilder[Json]
    while (current.nonEmpty) {
      val cell = current.get
      val value = if (kind == "input") {
        cell.pointers(stack.pool.key(tag, "value")).fold[Json](Json.Null)(node => json(scalar(circuit, node, "input")))
      } else { json(scalar(circuit, cell, stack.pool.key(tag, "data"))) }
      result += value
      val below = cell.pointers(stack.pool.key(tag, "below"))
      tag = scalar(circuit, cell, stack.pool.key(tag, "tag")).asInstanceOf[CellTag]
      current = below
    }
    result.result()
  }

  def snapshot(circuit: Circuit, root: Node, views: Layout): Json.Obj = Json.obj(
    "fields" -> Json.Obj(views.fields.map(field => field.key -> json(scalar(circuit, root, field.key)))),
    "focuses" -> Json.Obj(views.focuses.map(key => key -> root.pointers(key).fold[Json](Json.Null)(node => json(scalar(circuit, node, "input"))))),
    "stacks" -> Json.Obj(views.stacks.map { case (stack, kind) => stack.name -> Json.Arr(circuitValues(circuit, root, stack, kind)) }))

  private def asObject(value: Json): Json.Obj = value match {
    case obj: Json.Obj => obj
    case _ => throw new IllegalArgumentException("expected state object")
  }

  /** Re-encode immutable stacks by contents; allocation slots and sharing are immaterial. */
  def encode(built: Built, views: Layout, previous: Json, input: Json, newInput: Boolean,
             budget: Int, ready: Option[Boolean] = None, pending: Boolean = false): Node = {
    if (previous == Json.Null) { return built.machine.initialNode() }
    val circuit = built.circuit
    val defaults = built.machine.initial
    val nulls = VectorMap.from(built.machine.pointers.keys.map(_ -> Option.empty[Node]))
    def put(labels: VectorMap[String, Boolean], key: String, value: Any): VectorMap[String, Boolean] = {
      val domain = circuit.domains(key)._1
      val index = domain.indexOf(value)
      require(index >= 0, s"$key has no variant $value in $domain")
      labels ++ (0 until ScaffoldCircuit.bitWidth(domain.size)).map(bit => circuit.labelIds((key, bit)) -> ((index & (1 << bit)) != 0))
    }
    def decoded(key: String, value: Json): Any = value match {
      case Json.Null => None
      case Json.Bool(b) => b
      case Json.Num(n) => n.toInt
      case Json.Str(s) =>
        if (s.length == 1 && circuit.domains(key)._1.contains(s.head)) { s.head } else { s }
      case _ => throw new IllegalArgumentException("expected scalar value")
    }
    def inputNode(symbol: Json): Option[Node] = symbol match {
      case Json.Null => None
      case _ => Some(new Node(put(defaults, "input", decoded("input", symbol)), nulls))
    }
    val prev = asObject(previous)
    val oldFields = asObject(prev("fields"))
    val oldFocuses = asObject(prev("focuses"))
    val oldStacks = asObject(prev("stacks"))
    var labels = defaults
    var pointers = nulls
    for (field <- views.fields) { labels = put(labels, field.key, decoded(field.key, oldFields(field.key))) }
    labels = put(labels, "input", decoded("input", if (input == Json.Null) { Json.Str("a") } else { input }))
    ready match {
      case None => labels = put(labels, "arrival.phase", if (newInput) { budget - 1 } else { 0 })
      case Some(value) =>
        labels = put(labels, "online.ready", value)
        labels = put(labels, "online.pending", pending)
    }
    for (key <- views.focuses) { pointers = pointers.updated(key, inputNode(oldFocuses(key))) }
    for ((stack, kind) <- views.stacks) {
      val tag = stack.pool.tags.head
      var below: Option[Node] = None
      val values = oldStacks(stack.name) match {
        case Json.Arr(items) => items
        case _ => throw new IllegalArgumentException("expected stack array")
      }
      for (value <- values.reverse) {
        var cellLabels = put(defaults, stack.pool.key(tag, "tag"), tag)
        val dataKey = stack.pool.key(tag, "data")
        cellLabels = put(cellLabels, dataKey, if (kind == "input" || kind == "counter") { None } else { decoded(dataKey, value) })
        val cellPointers = nulls.updated(stack.pool.key(tag, "below"), below)
          .updated(stack.pool.key(tag, "value"), if (kind == "input") { inputNode(value) } else { None })
        below = Some(new Node(cellLabels, cellPointers))
      }
      pointers = pointers.updated(stack.rootKey, below)
      labels = put(labels, stack.tagKey, tag)
    }
    new Node(labels, pointers)
  }

  /** Original native sample selection and reference step; no circuit lowering runs here. */
  val oracle: String = """import json, sys
    |from types import SimpleNamespace
    |from dataclasses import replace
    |from unittest.mock import patch
    |import scaffold_galil as reference
    |import scaffold_search
    |from scaffold_program import ProgramView
    |from scavm import VM
    |from test_scaffold_circuit_galil import native_values
    |from fpp_subroutine import build_marked_program
    |from dp_finite import build_dp_program
    |spec, online, coarse = json.loads(sys.argv[1]), sys.argv[2] == 'true', sys.argv[3] == 'true'
    |convert = {'str': str, 'bool': bool, 'int': int}
    |def snapshot(root):
    |  if root is None: return None
    |  return {'fields': {key: convert[kind](root.label[original]) for key, original, kind in spec['fields']},
    |          'focuses': {key: None if root.ptr[key] is None else root.ptr[key].label['input'] for key in spec['focuses']},
    |          'stacks': {name: native_values(root, SimpleNamespace(name=name), kind) for name, kind in spec['stacks']}}
    |seen, samples = set(), [(None, 'a', True, False)]
    |kernels = build_marked_program('abs'), build_dp_program('abs')
    |if online:
    |  for word in ('ab', 'abba', 'a' * 12, 'ab' * 10, 'a' * 8 + 'b' + 'a' * 8):
    |    source = reference.OnlineGalil()
    |    for char in word:
    |      while True:
    |        previous, ready, pending = source.vm.top, source.input_ready, source._output_pending
    |        event = char if ready else '.'
    |        if previous is not None:
    |          lab = previous.label
    |          key = (lab['g.mode'], lab['sp.mode'], lab['ch.mode'], lab['ch.only'],
    |                 lab['g.replaying'], lab['g.odd'], lab['g.pair'], lab['g.clock'] == '1', ready, pending)
    |          if key not in seen:
    |            seen.add(key); samples.append((previous, event, ready, pending))
    |        result = source.read(char) if ready else source.work()
    |        if result.input_ready: break
    |else:
    |  for word in ('ab', 'abba', 'a' * 16, 'ab' * 12, 'ab' + 'a' * 20 + 'ba'):
    |    vm = VM()
    |    for char in word:
    |      new_input, caught = True, False
    |      while not caught:
    |        previous = vm.top
    |        if previous is not None:
    |          lab = previous.label
    |          key = (lab['g.mode'], lab['sp.mode'], lab['ch.mode'], lab['ch.only'],
    |                 lab['g.replaying'], lab['g.odd'], lab['g.pair'], lab['g.clock'] == '1')
    |          if key not in seen:
    |            seen.add(key); samples.append((previous, char, new_input, False))
    |        _, caught, _ = reference.step(vm, char, new_input, kernels)
    |        new_input = False
    |class ReadProgramView(ProgramView):
    |  def step(self): self.step_read_block()
    |program_view = ReadProgramView if coarse else ProgramView
    |timing = replace(reference.DEFAULT_TIMING, quantum=1)
    |results = []
    |with patch.object(reference, 'DEFAULT_TIMING', timing), patch.object(reference, 'ProgramView', program_view), patch.object(scaffold_search, 'ProgramView', program_view):
    |  for previous, char, arrival, pending in samples:
    |    record = {'previous': snapshot(previous), 'input': previous.label['input'] if previous else None,
    |              'char': char, 'arrival': arrival, 'pending': pending}
    |    if online:
    |      source = reference.OnlineGalil(quantum=1)
    |      source.vm.top, source.vm.t = previous, -1 if previous is None else previous.t
    |      source.input_ready, source._output_pending = arrival, pending
    |      expected = source.read(char) if char != '.' else source.work()
    |      record.update(expected=snapshot(source.vm.top), accepting=expected.output == 1,
    |                    event=expected.output is not None, ready=expected.input_ready, next_pending=source._output_pending)
    |    else:
    |      vm = VM()
    |      vm.top, vm.t = previous, -1 if previous is None else previous.t
    |      report, _, _ = reference.step(vm, char, arrival, kernels)
    |      record.update(expected=snapshot(vm.top), accepting=bool(report))
    |    results.append(record)
    |print(json.dumps(results))
    |""".stripMargin
}

class ScaffoldCircuitGalilSuite extends munit.FunSuite {
  import ScaffoldCircuitGalilSuite.*
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  private def compare(online: Boolean, coarse: Boolean = false, sharedCells: Boolean = false): Unit = Expr.share {
    val built = if (online) { ScaffoldCircuitGalil.buildOnlineWithViews(quantum = 1, sharedCells = sharedCells) }
      else { ScaffoldCircuitGalil.buildWithViews(quantum = 1, coarse = coarse) }
    val views = layout(built.views)
    val records = Json.parse(PyDiff.python("-c", oracle, Json.dumps(views.specification), online.toString, coarse.toString)) match {
      case Json.Arr(items) => items.map {
        case record: Json.Obj => record
        case _ => fail("expected sample object")
      }
      case _ => fail("expected samples")
    }
    assert(records.size > 20, s"only ${records.size} mode samples")
    if (!online) {
      val modes = records.tail.map { record =>
        record("previous").asInstanceOf[Json.Obj]("fields").asInstanceOf[Json.Obj]("g.mode")
      }.toSet
      val expectedModes: Set[Json] = Set("scan", "shift", "copy", "home", "fpp", "mark_end", "choose", "rewind", "replay_start")
        .map(name => Json.Str(name): Json)
      assertEquals(modes, expectedModes)
    }
    for ((record, index) <- records.zipWithIndex) {
      val char = record("char").asInstanceOf[Json.Str].value.head
      val arrival = record("arrival").asInstanceOf[Json.Bool].value
      val pending = record("pending").asInstanceOf[Json.Bool].value
      val root = encode(built, views, record("previous"), record("input"), if (online) { char != '.' } else { arrival },
        if (online) { 2 } else { 2048 }, if (online) { Some(arrival) } else { None }, pending)
      val actual = built.machine.step(root, char).get
      assertEquals(scalar(built.circuit, actual, "circuit.fault"), false, s"sample $index")
      assertEquals(Json.Bool(actual.labels(built.machine.accepting)), record("accepting"), s"sample $index")
      if (online) {
        assertEquals(Json.Bool(scalar(built.circuit, actual, "online.event") == true), record("event"), s"sample $index")
        assertEquals(Json.Bool(scalar(built.circuit, actual, "online.ready") == true), record("ready"), s"sample $index")
        assertEquals(Json.Bool(scalar(built.circuit, actual, "online.pending") == true), record("next_pending"), s"sample $index")
      }
      val actualState = snapshot(built.circuit, actual, views)
      val expectedState = record("expected").asInstanceOf[Json.Obj]
      for (section <- Vector("fields", "focuses", "stacks")) {
        val actualFields = actualState(section).asInstanceOf[Json.Obj]
        for ((key, value) <- expectedState(section).asInstanceOf[Json.Obj].fields) {
          assertEquals(actualFields(key), value, s"sample $index, $section, $key")
        }
      }
    }
  }

  test("online read/work/output and all state match source") { compare(online = true) }
  test("online state with shared instruction cells matches source") { compare(online = true, sharedCells = true) }
  test("whole transition matches native modes, tapes, heads, counters") { compare(online = false) }
  test("read-block transition matches native modes, tapes, heads, counters") { compare(online = false, coarse = true) }
  test("invalid quantum and clocks retain Python diagnostics") {
    assertEquals(intercept[IllegalArgumentException](ScaffoldCircuitGalil.build(quantum = 0)).getMessage,
      "positive finite instruction quantum required")
    for ((delay, budget) <- Vector((1, 2), (3, 2), (2, 1), (2, 6))) {
      assertEquals(intercept[IllegalArgumentException](ScaffoldCircuitGalil.build(matchDelay = delay, budget = budget)).getMessage,
        "clocks must be powers of two of at least two")
    }
  }
}
