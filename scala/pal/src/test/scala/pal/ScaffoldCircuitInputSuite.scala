package pal

import Expr.TRUE
import Ref.NEW
import ScaffoldCircuit.*
import ScaffoldCircuitInput.PlaceHead
import TestScaffoldCircuitProgram.{scalar, stack}

object ScaffoldCircuitInputSuite {
  def fixture(): (Circuit, Vector[PlaceHead], Scaffold) = {
    val c = new Circuit("abrlRLc.")
    val char = c.input()
    val arrival = disjunction(char.eqTo('a'), char.eqTo('b'))
    c.put("input", Value.select(arrival, Value("ab".toVector.map(s => s -> char.eqTo(s))), Value.constant('a')), Vector('a', 'b'), 'a')
    val names = Vector("X", "Y")
    val heads = new StackPool(c, names.flatMap(name => Vector("l", "r").map(side => s"$name.$side" -> 1)))
    val queues = new StackPool(c, names.flatMap(name => Vector("F" -> 0, "B" -> 1, "B2" -> 1, "Fr" -> 12,
      "Br" -> 24, "WF" -> 0, "WB" -> 0).map { case (role, count) => s"$name.in.$role" -> count }))
    val counters = new StackPool(c, names.flatMap(name => Vector("m.pos" -> 12, "m.neg" -> 13, "c.pos" -> 24,
      "c.neg" -> 2).map { case (role, count) => s"$name.in.$role" -> count }))
    val x = new PlaceHead(heads, queues, counters, "X")
    val y = new PlaceHead(heads, queues, counters, "Y")
    Vector(x, y).foreach(_.append(NEW, arrival))
    for ((head, right, left) <- Vector((x, 'r', 'l'), (y, 'R', 'L'))) {
      head.right(conjunction(char.eqTo(right), head.canRight()))
      head.left(conjunction(char.eqTo(left), neg(head.read().eqTo(None))))
    }
    y.copyFrom(x, char.eqTo('c'))
    x.commit()
    y.commit()
    (c, Vector(x, y), c.machine(TRUE, initialAccepting = true))
  }
}

class ScaffoldCircuitInputSuite extends munit.FunSuite {
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(180, "s")
  test("two clonable place heads match integer observer on Python's seeded commands") {
    val (circuit, heads, machine) = ScaffoldCircuitInputSuite.fixture()
    var root = machine.initialNode()
    val commands = "abrrrRcLrRl" + PyDiff.python("-c", "import random; random.seed(94); print(''.join(random.choices('abrlRLc.', k=100)), end='')")
    var word = ""
    val positions = Array(0, 0)
    for (command <- commands) {
      if ("ab".contains(command)) { word += command }
      for (((right, left), i) <- Vector(('r', 'l'), ('R', 'L')).zipWithIndex) {
        if (command == right) { positions(i) = math.min(positions(i) + 1, 2 * word.length) }
        if (command == left) { positions(i) = math.max(positions(i) - 1, 0) }
      }
      if (command == 'c') { positions(1) = positions(0) }
      root = machine.step(root, command).get
      assert(root.labels(machine.accepting), command.toString)
      for ((head, i) <- heads.zipWithIndex) {
        val place = root.pointers(head.head.focusKey) match {
          case None => 0
          case Some(focus) =>
            val depth = stack(circuit, root, head.head.leftStack).size
            assertEquals(scalar(circuit, focus, "input"), word(depth - 1))
            2 * depth - 1 + (if (scalar(circuit, root, head.gapKey) == true) { 1 } else { 0 })
        }
        assertEquals(place, positions(i), command.toString)
      }
    }
  }

  test("clonable input-head fixture emits byte-identical Python PEG") {
    Expr.share {
      val machine = ScaffoldCircuitInputSuite.fixture()._3
      PyDiff.assertSameAsPython(machine.compile(), "-c", "from symbolic_sca2peg import share_expressions; from test_scaffold_circuit_input import fixture\nwith share_expressions(): print(fixture()[2].compile(), end='')")
    }
  }
}
