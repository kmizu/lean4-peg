package pal

import ScaffoldWindowCounterSuite.decode
import TestScaffoldCircuitProgram.scalar

object ScaffoldWindowGsSuite {
  val twoEndedProgram: Program = Program(Vector(
    Row(Event.Copy("A", "Origin"), Vector(1)),
    Row(Event.Copy("B", "OriginalEnd"), Vector(2)),
    Row(Event.Less("A", "B"), Vector(7, 3)),
    Row(Event.move(Event.Movement("B", -1)), Vector(4)),
    Row(Event.Symbols("A", "B"), Vector(8, 5)),
    Row(Event.move(Event.Movement("A", 1)), Vector(6)),
    Row(Event.Less("A", "B"), Vector(7, 3)),
    Row(Event.Border("B"), Vector(8)),
    Row(Event.Halt, Vector.empty)), 0, 8)

  private def binaryWords(maxLengthExclusive: Int): Vector[String] = {
    (0 until maxLengthExclusive).toVector.flatMap { length =>
      Vector.tabulate(1 << length) { bits =>
        Vector.tabulate(length)(index => if ((bits & (1 << index)) == 0) { 'a' } else { 'b' }).mkString
      }
    }
  }

  val words: Vector[String] = binaryWords(5) ++ Vector("ababbaba", "a" * 17, "ab" * 9, "abba" * 5)
}

class ScaffoldWindowGsSuite extends munit.FunSuite {
  import ScaffoldWindowGs.fixture
  import ScaffoldWindowGsSuite.*

  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(900, "s")

  test("burst pc positions and plain PEG") {
    val quantum = 5
    val (circuit, worker, machine, projected) = Expr.share {
      val (circuit, worker, machine) = fixture(quantum, Some(twoEndedProgram))
      (circuit, worker, machine, ScaffoldOptimize.optimize(machine)._1)
    }
    val grammar = new Grammar(projected.compile())
    for (word <- words) {
      val observer = new HeadVM(word.toIndexedSeq, twoEndedProgram)
      var node = machine.evaluate(word + "!").get
      var trace = word + "!"
      var rounds = 0
      while (scalar(circuit, node, worker.modeKey) != "done" && rounds < 4 * word.length + 10) {
        node = machine.step(node, '.').get
        trace += "."
        for (_ <- 0 until quantum if !observer.done) { observer.step() }
        assertEquals(scalar(circuit, node, "circuit.fault"), false, (word, trace))
        assertEquals(scalar(circuit, node, worker.pcKey), observer.state, word)
        for (head <- Vector("A", "B", "OriginalEnd")) {
          val distance = worker.positions.counters(("Origin", head))
          assertEquals(-decode(circuit, node, distance), BigInt(observer.positions(head)), (word, head))
        }
        rounds += 1
      }
      assertEquals(scalar(circuit, node, worker.modeKey), "done", word)
      val expected = word == word.reverse
      assertEquals(node.labels(machine.accepting), expected, word)
      assertEquals(grammar.accepts(trace.reverse), expected, word)
    }
    assert(!grammar.accepts("a.a!..".reverse))
  }

  test("small generated PEG is byte identical to Python") {
    val small = Program(Vector(
      Row(Event.Copy("A", "Origin"), Vector(1)),
      Row(Event.Border("A"), Vector(2)),
      Row(Event.Halt, Vector.empty)), 0, 8)
    val actual = Expr.share { fixture(1, Some(small))._3.compile() }
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import Program\nfrom scaffold_window_gs import fixture\nfrom symbolic_sca2peg import share_expressions\np=Program(((('copy','A','Origin'),(1,)),(('border','A'),(2,)),(('halt',),())),0,8)\nwith share_expressions(): print(fixture(1,p)[2].compile(),end='')")
  }
}
