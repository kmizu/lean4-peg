package pal

import scala.collection.immutable.VectorMap
import TestScaffoldCircuitProgram.scalar
import ScaffoldWindowCounterSuite.decode
import ScaffoldHeadDistancesSuite.{ACTIONS, actionChars, initialPositions, apply as applyCommand, Move, Copy}

object ScaffoldWindowPositionsSuite {
  def fixture(quantum: Int = 5): (Circuit, WindowPositions, VectorMap[(String, String, String), String], Scaffold) = {
    val circuit = new Circuit(actionChars.mkString)
    val positions = new WindowPositions(circuit, Vector("A", "B", "C"), 6 * quantum)
    for (_ <- 0 until quantum; (char, action) <- ACTIONS) {
      val guard = circuit.input().eqTo(char)
      action match {
        case Move(head, amount) => positions.move(head, amount, guard)
        case Copy(target, source) => positions.copy(target, source, guard)
      }
    }
    val observations = VectorMap.from(for (left <- positions.names; right <- positions.names; (relation, condition) <- {
      val (equal, less) = positions.compare(left, right)
      Vector("eq" -> equal, "lt" -> less)
    }) yield {
      val key = s"$relation.$left.$right"
      circuit.put(key, Value.select(condition, Value.constant(true), Value.constant(false)), Vector(false, true), relation == "eq")
      (relation, left, right) -> key
    })
    val answer = positions.less("A", "B")
    positions.commit()
    (circuit, positions, observations, circuit.machine(answer))
  }
}

class ScaffoldWindowPositionsSuite extends munit.FunSuite {
  import ScaffoldWindowPositionsSuite.fixture
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  test("orders and final distances after conditional copies") {
    val (circuit, bank, observations, machine) = Expr.share { fixture() }
    var root = machine.initialNode()
    val values = initialPositions()
    val rng = new PyRandom(917)
    val word = "a" * 100 + "b" * 150 + "fed" + "g" * 180 + "h" * 100 + Vector.fill(300)(rng.choice(actionChars)).mkString
    for ((char, index) <- word.zipWithIndex) {
      for (_ <- 0 until 5) { applyCommand(values, char) }
      root = machine.step(root, char).get
      for (((relation, left, right), key) <- observations) {
        val expected = if (relation == "eq") { values(left) == values(right) } else { values(left) < values(right) }
        assertEquals(scalar(circuit, root, key), expected, (index, char, key, values))
      }
      for (((left, right), counter) <- bank.counters) {
        assertEquals(decode(circuit, root, counter), BigInt(values(left) - values(right)), (index, char, left, right))
      }
    }
  }
  test("ordinary PEG compares the current heads") {
    val (_, _, _, machine) = Expr.share { fixture(2) }
    val grammar = new Grammar(machine.compile())
    val rng = new PyRandom(918)
    for (_ <- 0 until 50) {
      val word = Vector.fill(rng.randrange(40))(rng.choice(actionChars)).mkString
      val values = initialPositions()
      for (char <- word; _ <- 0 until 2) { applyCommand(values, char) }
      assertEquals(grammar.accepts(word.reverse), values("A") < values("B"), (word, values))
    }
  }
  test("both fixture PEGs are byte identical to Python") {
    val actual = Vector(5, 2).map(q => Expr.share { fixture(q)._4 }.compile()).mkString
    PyDiff.assertSameAsPython(actual, "-c",
      "from test_scaffold_window_positions import fixture\nfrom symbolic_sca2peg import share_expressions\nfor q in (5, 2):\n with share_expressions():\n  _, _, _, m = fixture(q)\n print(m.compile(), end='')")
  }
  test("selected positions preserve snapshots and construction bounds") {
    val positions = new WindowPositions(new Circuit(), Vector("A", "B"), 3)
    positions.move("A", 3)
    val selected = positions.selectPosition(Value.constant("A"))
    positions.copy("A", "B")
    positions.copyPosition("B", selected)
    assertEquals(positions.heads("B").radius, BigInt(3))
    intercept[IllegalArgumentException] { positions.move("B", 1) }
    assertEquals(positions.compare("A", "A"), (Expr.TRUE, Expr.FALSE))
    intercept[IllegalArgumentException] { new WindowPositions(new Circuit(), Vector("A"), 3) }
    intercept[IllegalArgumentException] { new WindowPositions(new Circuit(), Vector("A", "B"), -1) }
  }
}
