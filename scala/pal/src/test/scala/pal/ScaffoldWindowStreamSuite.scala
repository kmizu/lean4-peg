package pal

import scala.collection.mutable
import TestScaffoldCircuitProgram.scalar
import ScaffoldWindowStream.fixture

object ScaffoldWindowStreamSuite {
  def applyCommand(positions: mutable.Map[String, Int], char: Char, size: Int, quantum: Int): Unit = {
    char match {
      case 'a' => positions("x") = math.min(size, positions("x") + quantum)
      case 'b' => positions("x") = math.max(0, positions("x") - quantum)
      case 'c' => positions("y") = positions("x")
      case 'd' => positions("x") = positions("y")
      case 'e' => positions("y") = math.min(size, positions("y") + 1)
      case 'f' => positions("y") = math.max(0, positions("y") - 1)
      case _ => ()
    }
  }
}

class ScaffoldWindowStreamSuite extends munit.FunSuite {
  import ScaffoldWindowStreamSuite.*
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  test("positions block crossings live blocks and copied heads") {
    for (quantum <- Vector(1, 3, 9)) {
      val (circuit, stream, observations, machine) = Expr.share { fixture(quantum) }
      var root = machine.initialNode()
      var data = ""
      val positions = mutable.Map("x" -> 0, "y" -> 0)
      val identities = mutable.Map(root -> 0)
      val rng = new PyRandom(913)
      val word = "a" * 35 + "b" * 2 + "h" * 70 + "a" * 40 + "b" * 45 + "cd" + Vector.fill(170)(rng.choice("abcdefgh")).mkString
      for ((char, zeroIndex) <- word.zipWithIndex) {
        val index = zeroIndex + 1
        data += char
        applyCommand(positions, char, index, quantum)
        root = machine.step(root, char).get
        identities(root) = index
        assertEquals(scalar(circuit, root, "circuit.fault"), false, (quantum, index, char, positions))
        for (name <- stream.names) {
          val state = stream.states(name)
          val low = (0 until stream.width).filter(bit => scalar(circuit, root, s"$name.offset.$bit") == true).map(bit => BigInt(1) << bit).sum
          val actual = if (scalar(circuit, root, state.liveKey) == true) {
            (index / stream.base) * stream.base + low
          } else {
            identities(root.pointers(state.focusKey).get) - stream.base + low
          }
          assertEquals(actual, BigInt(positions(name)), (quantum, index, char, name))
          val expected: Any = if (actual < index) { data(actual.toInt) } else { None }
          assertEquals(scalar(circuit, root, observations(name)), expected, (quantum, index, char, name, actual))
        }
      }
    }
  }
  test("ordinary PEG uses unexpanded input") {
    val machine = Expr.share { ScaffoldOptimize.optimize(fixture(1)._4)._1 }
    val grammar = new Grammar(machine.compile())
    val words = Vector("", "a", "b", "ha", "ab", "haabc", "aaaaabhhha", "ahhbhhha", "h" * 17 + "a" * 10 + "b" * 6 + "cdeaf")
    for (word <- words) {
      val positions = mutable.Map("x" -> 0, "y" -> 0)
      for ((char, index) <- word.zipWithIndex) { applyCommand(positions, char, index + 1, 1) }
      val expected = positions("x") < word.length && word(positions("x")) == 'a'
      assertEquals(grammar.accepts(word.reverse), expected, (word, positions))
    }
  }
  test("persisted heap does not grow with number of internal moves") {
    val (small, large) = Expr.share { (fixture(1)._4, fixture(15)._4) }
    assert(large.pointers.size - small.pointers.size <= 20)
    assert(large.labels.size - small.labels.size <= 30)
  }
  test("raw and optimized stream PEGs are byte identical to Python") {
    val actual = Vector(1, 3).map { q =>
      Expr.share {
        val machine = fixture(q)._4
        machine.compile() + ScaffoldOptimize.optimize(machine)._1.compile()
      }
    }.mkString
    PyDiff.assertSameAsPython(actual, "-c",
      "from scaffold_window_stream import fixture\nfrom scaffold_optimize import optimize\nfrom symbolic_sca2peg import share_expressions\nfor q in (1, 3):\n with share_expressions():\n  _, _, _, m = fixture(q)\n  projected, _ = optimize(m)\n print(m.compile(), end='')\n print(projected.compile(), end='')")
  }
  test("head selection relative reads and selected motion match Python bytes") {
    val machine = Expr.share {
      val c = new Circuit("ab")
      val bank = new WindowStream(c, Vector("x", "y"), 7)
      bank.heads("x").move(1)
      val which = Value.select(c.input().eqTo('a'), Value.constant("x"), Value.constant("y"))
      val selected = bank.selectHead(which)
      val value = selected.readRelative(-1, c.input().eqTo('a'))
      val amount = Value.select(c.input().eqTo('a'), Value.constant(1), Value.constant(0))
      bank.heads("y").moveSelected(amount)
      val answer = value.eqTo('a')
      bank.commit()
      c.machine(answer)
    }
    PyDiff.assertSameAsPython(machine.compile(), "-c",
      """from scaffold_circuit import Circuit, Value
        |from scaffold_window_stream import WindowStream
        |from symbolic_sca2peg import share_expressions
        |with share_expressions():
        | c = Circuit('ab')
        | bank = WindowStream(c, ('x','y'), 7)
        | bank.heads['x'].move(1)
        | which = Value.select(c.input().eq('a'), Value.constant('x'), Value.constant('y'))
        | selected = bank.select_head(which)
        | value = selected.read_relative(-1, c.input().eq('a'))
        | amount = Value.select(c.input().eq('a'), Value.constant(1), Value.constant(0))
        | bank.heads['y'].move_selected(amount)
        | answer = value.eq('a')
        | bank.finalize()
        | m = c.machine(answer)
        |print(m.compile(), end='')
        |""".stripMargin)
  }
  test("invalid stream declarations copies and movement bounds") {
    intercept[IllegalArgumentException] { new WindowStream(new Circuit(), Vector("x"), -1) }
    intercept[IllegalArgumentException] { new WindowStream(new Circuit(), Vector("x", "x"), 1) }
    val a = new WindowStream(new Circuit(), Vector("x"), 1)
    val b = new WindowStream(new Circuit(), Vector("x"), 1)
    intercept[IllegalArgumentException] { a.heads("x").copyFrom(b.heads("x")) }
    intercept[IllegalArgumentException] { a.heads("x").move(2) }
    intercept[IllegalArgumentException] { a.heads("x").moveSelected(Value.constant(2)) }
    intercept[IllegalArgumentException] { a.heads("x").readRelative(2) }
    intercept[IllegalArgumentException] { a.jump(0) }
  }
}
