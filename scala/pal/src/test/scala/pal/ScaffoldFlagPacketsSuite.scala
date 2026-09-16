package pal

import scala.collection.mutable

import ScaffoldFlagPackets.fixture
import TestScaffoldCircuitProgram.scalar

/** Port of `test_scaffold_flag_packets.py`. */
class ScaffoldFlagPacketsSuite extends munit.FunSuite {

  private def decode(circuit: Circuit, root: Node, view: FlagStack): Vector[Boolean] = {
    var node = root.pointers(view.rootKey)
    var index = scalar(circuit, root, view.indexKey).asInstanceOf[Int]
    val result = mutable.ArrayBuffer.empty[Boolean]
    while (node.nonEmpty) {
      val (bitKey, previousKey) = view.pool.fields(index)
      result += scalar(circuit, node.get, bitKey).asInstanceOf[Boolean]
      index = scalar(circuit, node.get, previousKey).asInstanceOf[Int]
      if (index == -1) {
        index = scalar(circuit, node.get, view.pool.indexKey).asInstanceOf[Int]
        node = node.get.pointers(view.pool.backKey)
      }
    }
    result.toVector
  }

  private def applyCommand(stacks: Array[mutable.ArrayBuffer[Boolean]], char: Char, capacity: Int): Boolean = {
    var answer = false
    char match {
      case '!' => stacks(0).clear()
      case 'c' => stacks(1) = stacks(0).clone()
      case 'r' => stacks(0) = stacks(1).clone()
      case '<' if stacks(0).nonEmpty => answer = stacks(0).remove(0)
      case '>' if stacks(1).nonEmpty => answer = stacks(1).remove(0)
      case 'a' | 'b' =>
        for (slot <- 0 until capacity if char == 'a' || slot % 3 != 1) {
          stacks(0).prepend(if (slot % 2 == 0) { char == 'a' } else { char == 'b' })
        }
      case _ =>
    }
    answer
  }

  test("sparse pushes packet boundaries and immutable copies") {
    val (circuit, _, views, machine) = Expr.share { fixture() }
    val rng = new PyRandom(919)
    val word = "abca" + "<" * 30 + ">" * 20 + "br<ac" + ">" * 20 + "!r" + rng.word("ab<>cr!", 250)
    var root = machine.initialNode()
    val stacks = Array(mutable.ArrayBuffer.empty[Boolean], mutable.ArrayBuffer.empty[Boolean])
    for ((char, index) <- word.zipWithIndex) {
      val expected = applyCommand(stacks, char, 7)
      root = machine.step(root, char).get
      assertEquals(scalar(circuit, root, "circuit.fault"), false, (index, char))
      assertEquals(root.labels(machine.accepting), expected, (index, char))
      for ((view, wanted) <- Vector(views._1, views._2).zip(stacks)) {
        assertEquals(decode(circuit, root, view), wanted.toVector, (index, char, view.name))
      }
    }
  }

  test("ordinary PEG on original commands") {
    val (_, _, _, machine) = Expr.share { fixture(5) }
    val grammar = new Grammar(machine.compile())
    val rng = new PyRandom(920)
    val words = mutable.ArrayBuffer("", "a<", "b<", "ac<>", "bc" + "<" * 7 + ">", "aac!r<")
    for (_ <- 0 until 40) { words += rng.word("ab<>cr!", 40) + "<" }
    for (word <- words) {
      val stacks = Array(mutable.ArrayBuffer.empty[Boolean], mutable.ArrayBuffer.empty[Boolean])
      var expected = false
      for (char <- word) { expected = applyCommand(stacks, char, 5) }
      assertEquals(grammar.accepts(word.reverse), expected, word)
    }
  }

  test("fixture compile output matches Python byte-for-byte") {
    val actual = Expr.share {
      val (_, _, _, machine) = fixture()
      machine.compile()
    }
    val script =
      """from scaffold_flag_packets import fixture
        |from symbolic_sca2peg import share_expressions
        |with share_expressions():
        |  _, _, _, machine = fixture()
        |print(machine.compile(), end="")
        |""".stripMargin
    PyDiff.assertSameAsPython(actual, "-c", script)
  }
}
