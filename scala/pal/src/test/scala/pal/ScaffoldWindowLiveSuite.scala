package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

object ScaffoldWindowLiveSuite {
  val names: Vector[String] = Vector("A", "B", "OriginalEnd")
  val program: Program = Program(Vector(
    Row(Event.Less("A", "B"), Vector(1, 1)),
    Row(Event.move(Event.Movement("A", 2), Event.Movement("B", -1)), Vector(2)),
    Row(Event.Copy("B", "A"), Vector(3)),
    Row(Event.Equal("B", "A"), Vector(4, 4)),
    Row(Event.Available("A"), Vector(5, 5)),
    Row(Event.AssertEqual("B", "OriginalEnd"), Vector(6)),
    Row(Event.Equal("A", "A"), Vector(0, 0))), 0, 1)

  val pythonProgram: String =
    """from gs_heads import Program
      |from scaffold_window_live import WindowLiveDistances
      |from scaffold_circuit import Circuit, Value, TRUE
      |from scaffold_rom import controller_table
      |from symbolic_sca2peg import share_expressions
      |names = ('A', 'B', 'OriginalEnd')
      |program = Program(((('less','A','B'),(1,1)),
      | (('move',(('A',2),('B',-1))),(2,)),
      | (('copy','B','A'),(3,)),
      | (('equal','B','A'),(4,4)),
      | (('available','A'),(5,5)),
      | (('assert_equal','B','OriginalEnd'),(6,)),
      | (('equal','A','A'),(0,0))), 0, 1)
      |""".stripMargin

  def fixture(availability: Boolean): Scaffold = {
    val c = new Circuit("abcdefg")
    val distances = new WindowLiveDistances(c, program, names, 16, extra = Vector("extra"), availabilityDistance = availability)
    val table = ScaffoldRom.controllerTable(program, names, batched = true, augment = Some(distances.augmentRows))
    val char = c.input()
    distances.loadOne(Expr.TRUE)
    distances.values.add("extra", 2)
    distances.initialize(char.eqTo('a'))
    val mapping = VectorMap.from(distances.analysis.before(program.start).toVector.sorted.map { pair =>
      pair -> (if (pair._2 == "OriginalEnd") { Some(("extra", -1)) } else { None })
    })
    distances.initializeValues(mapping, char.eqTo('g'))
    val fields = table.read(char.map(ch => "abcdefg".indexOf(ch)).bits)
    val (zero, less) = distances.compare(fields)
    c.put("zero", Value.select(zero, Value.constant(true), Value.constant(false)), Vector(false, true), true)
    c.put("less", Value.select(less, Value.constant(true), Value.constant(false)), Vector(false, true), false)
    distances.execute(fields, Expr.TRUE)
    distances.commit()
    c.machine(less)
  }
}

class ScaffoldWindowLiveSuite extends munit.FunSuite {
  import ScaffoldWindowLiveSuite.*
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  private def json(value: Any): Json = value match {
    case value: String => Json.Str(value)
    case value: Boolean => Json.Bool(value)
    case value: Int => Json.Num(value.toLong)
    case None => Json.Null
    case values: Seq[?] => Json.Arr(values.toVector.map(json))
    case _ => throw new IllegalArgumentException(s"unsupported ROM cell $value")
  }
  test("augmented ROM rows and domain order match Python in both availability modes") {
    val actual = Vector(true, false).map { availability =>
      val d = new WindowLiveDistances(new Circuit(), program, names, 16, availabilityDistance = availability)
      val rows = Vector.fill(program.code.size)(mutable.LinkedHashMap.empty[String, Any])
      val domains: ScaffoldRom.Domains = mutable.LinkedHashMap.empty
      d.augmentRows(rows, domains)
      Json.dumps(Json.Obj(Vector(
        "rows" -> Json.Arr(rows.map(row => Json.Obj(row.toVector.map { case (key, value) => key -> json(value) }))),
        "domains" -> Json.Obj(domains.toVector.map { case (key, value) => key -> json(value) })))) + "\n"
    }.mkString
    PyDiff.assertSameAsPython(actual, "-c", pythonProgram +
      "import json\nfor availability in (True, False):\n d = WindowLiveDistances(Circuit(), program, names, 16, availability_distance=availability)\n rows = [{} for _ in program.code]\n domains = {}\n d.augment_rows(rows, domains)\n print(json.dumps(dict(rows=rows, domains=domains), indent=2))\n")
  }
  test("ROM-driven initialization comparison and simultaneous transfer PEGs match Python bytes") {
    val actual = Vector(true, false).map(availability => Expr.share { fixture(availability) }.compile()).mkString
    PyDiff.assertSameAsPython(actual, "-c", pythonProgram +
      """for availability in (True, False):
        | with share_expressions():
        |  c = Circuit('abcdefg')
        |  d = WindowLiveDistances(c, program, names, 16, extra=('extra',), availability_distance=availability)
        |  table = controller_table(program, names, batched=True, augment=d.augment_rows)
        |  char = c.input()
        |  d.load_one(TRUE)
        |  d.values.add('extra', 2)
        |  d.initialize(char.eq('a'))
        |  mapping = {pair: ('extra', -1) if pair[1]=='OriginalEnd' else None for pair in sorted(d.analysis.before[program.start])}
        |  d.initialize_values(mapping, char.eq('g'))
        |  fields = table.read(char.map(lambda ch: 'abcdefg'.index(ch)).bits)
        |  zero, less = d.compare(fields)
        |  c.put('zero', Value.select(zero, Value.constant(True), Value.constant(False)), (False,True), True)
        |  c.put('less', Value.select(less, Value.constant(True), Value.constant(False)), (False,True), False)
        |  d.execute(fields, TRUE)
        |  d.finalize()
        |  m = c.machine(less)
        | print(m.compile(), end='')
        |""".stripMargin)
  }
  test("initialization requires every live entry source") {
    val distances = new WindowLiveDistances(new Circuit(), program, names, 16)
    intercept[IllegalArgumentException] { distances.initializeValues(Map.empty, Expr.TRUE) }
  }
  test("absent comparison source is exactly zero in either orientation") {
    val distances = new WindowLiveDistances(new Circuit(), program, names, 16)
    for (reverse <- Vector(false, true)) {
      val fields = Map("distance.test" -> Value.constant(None), "distance.reverse" -> Value.constant(reverse))
      assertEquals(distances.compare(fields), (Expr.TRUE, Expr.FALSE))
    }
  }
}
