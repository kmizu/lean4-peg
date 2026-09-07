package pal

import scala.collection.immutable.VectorMap

class ScaffoldLiveDistancesSuite extends munit.FunSuite {
  private val names = Vector("A", "B", "C")
  private val program = Program(Vector(
    Row(Event.move(Event.Movement("A", 1)), Vector(4)),
    Row(Event.move(Event.Movement("B", -1)), Vector(4)),
    Row(Event.Copy("C", "A"), Vector(4)),
    Row(Event.Copy("A", "B"), Vector(4)),
    Row(Event.Equal("A", "B"), Vector(5, 5)),
    Row(Event.Equal("A", "C"), Vector(6, 6)),
    Row(Event.Equal("B", "C"), Vector(0, 0))), 0, 4)

  private def fixture(): Scaffold = Expr.share {
    val circuit = new Circuit("abcd")
    val distances = new LiveDistances(circuit, program, names)
    distances.execute(program.code.indices.map(i => if (i < 4) circuit.input().eqTo("abcd"(i)) else Expr.FALSE))
    for (left <- names; right <- names) {
      circuit.labels(s"eq.$left.$right") = distances.equal(left, right)
      circuit.labels(s"lt.$left.$right") = distances.less(left, right)
      circuit.initial(s"eq.$left.$right") = true
      circuit.initial(s"lt.$left.$right") = false
    }
    distances.commit()
    circuit.machine(distances.equal("A", "C"))
  }

  test("live differences and simultaneous copies compile identically to Python") {
    PyDiff.assertSameAsPython(fixture().compile(), "-c", """
      |from gs_heads import Program
      |from scaffold_circuit import Circuit
      |from scaffold_live_distances import LiveDistances
      |from symbolic_sca2peg import FALSE, share_expressions
      |code = ((('move', (('A',1),)), (4,)), (('move', (('B',-1),)), (4,)),
      | (('copy','C','A'), (4,)), (('copy','A','B'), (4,)),
      | (('equal','A','B'), (5,5)), (('equal','A','C'), (6,6)), (('equal','B','C'), (0,0)))
      |with share_expressions():
      | c = Circuit('abcd')
      | d = LiveDistances(c, Program(code,0,4), ('A','B','C'))
      | d.execute([c.input().eq('abcd'[i]) if i < 4 else FALSE for i in range(len(code))])
      | for left in d.names:
      |  for right in d.names:
      |   c.labels[f'eq.{left}.{right}'] = d.equal(left,right)
      |   c.labels[f'lt.{left}.{right}'] = d.less(left,right)
      |   c.initial[f'eq.{left}.{right}'] = True
      |   c.initial[f'lt.{left}.{right}'] = False
      | d.finalize()
      | machine = c.machine(d.equal('A','C'))
      |print(machine.compile(), end='')
      |""".stripMargin)
  }

  test("live counter observations agree with integer head positions") {
    val machine = fixture()
    PyItertools.wordsBelow("abcd", 5).filter(_.nonEmpty).foreach { word =>
      val positions = scala.collection.mutable.Map("A" -> 0, "B" -> 0, "C" -> 0)
      word.foreach {
        case 'a' => positions("A") += 1
        case 'b' => positions("B") -= 1
        case 'c' => positions("C") = positions("A")
        case 'd' => positions("A") = positions("B")
        case _ => ()
      }
      val node = machine.evaluate(word).get
      for (left <- names; right <- names) {
        assertEquals(node.labels(s"eq.$left.$right"), positions(left) == positions(right), word)
        assertEquals(node.labels(s"lt.$left.$right"), positions(left) < positions(right), word)
      }
    }
  }

  test("entry initialization requires exactly the live pairs and can load signed lengths") {
    val circuit = new Circuit()
    val distances = new LiveDistances(circuit, program, names)
    intercept[IllegalArgumentException](distances.initialize(VectorMap.empty, Expr.TRUE))
    distances.loadOne(Expr.TRUE)
    val values = VectorMap.from(distances.analysis.before(program.start).toVector.sorted.map { pair =>
      pair -> (if (pair == (("A", "B"))) Some((distances.length, -1)) else None)
    })
    distances.initialize(values, Expr.TRUE)
    distances.commit()
    val machine = circuit.machine(distances.less("A", "B"))
    assert(machine.run("a"))
    intercept[IllegalArgumentException](distances.execute(Vector.empty))
    val invalid = Program(Vector(Row(Event.move(Event.Movement("A", 2)), Vector(0))), 0, 4)
    val bad = new LiveDistances(new Circuit(), invalid, names)
    intercept[IllegalArgumentException](bad.execute(Vector(Expr.TRUE)))
  }
}
