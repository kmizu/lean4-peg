package pal

import scala.collection.mutable

import ScaffoldQueueRegisters.fixture
import TestScaffoldCircuitProgram.scalar

/** A bank of shared-cell queues checked against deques (port of `test_scaffold_queue_registers.py`). */
class ScaffoldQueueRegistersSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  /** Python `setUpClass`: one shared fixture built under expression sharing. */
  private lazy val (circuit: Circuit, machine: Scaffold) = Expr.share {
    val (circuit, _, machine) = fixture()
    (circuit, machine)
  }

  private def commands(): String = {
    val rng = new PyRandom(914)
    val out = new StringBuilder
    for (c <- "a" * 40 + "b" * 30) { out.append(c).append("...") }
    out.append("x")
    for (i <- 0 until 95) { out.append(if (i % 2 != 0) { ">..." } else { "],,," }) }
    // A copy may preserve an in-flight rotation. Service both snapshots before
    // their next public operation; advancing one must not mutate the other.
    out.append("a.x..,,," + "b.y..,,,")
    for (_ <- 0 until 180) {
      val command = rng.choice("abAB>]xy")
      out.append(command)
      if ("ab>".contains(command)) {
        out.append("...")
      } else if ("AB]".contains(command)) {
        out.append(",,,")
      }
    }
    out.toString
  }

  test("independent queues and copies during rotations") {
    var root = machine.initialNode()
    val queues = Array(mutable.Queue.empty[Char], mutable.Queue.empty[Char])
    for (command <- commands()) {
      var expected = false
      if ("abAB".contains(command)) {
        queues(if (command.isUpper) { 1 } else { 0 }).enqueue(command.toLower)
      } else if (">]".contains(command)) {
        val queue = queues(if (command == ']') { 1 } else { 0 })
        if (queue.nonEmpty) { expected = queue.dequeue() == 'a' }
      } else if (command == 'x') {
        queues(1) = queues(0).clone()
      } else if (command == 'y') {
        queues(0) = queues(1).clone()
      }
      root = machine.step(root, command).get
      assertEquals(scalar(circuit, root, "circuit.fault"), false, command)
      assertEquals(root.labels("accept"), expected, command)
    }
  }

  test("shared queue kernel executes as plain PEG") {
    val source = machine.compile()
    assert(source.length < 250000)
    val grammar = new Grammar(source)
    for ((trace, expected) <- Seq(("a...>", true), ("b...>", false),
                                  ("a...b...>...>", false), ("a.x..,,,]", true),
                                  ("A,,,y>", true))) {
      assertEquals(grammar.accepts(trace.reverse), expected, trace)
    }
  }

  test("the bank's rule list matches the Python fixture") {
    val script =
      """from scaffold_queue_registers import fixture
        |from symbolic_sca2peg import share_expressions
        |with share_expressions():
        |  _, _, machine = fixture()
        |print(machine.compile(), end="")
        |""".stripMargin
    PyDiff.assertSameAsPython(machine.compile(), "-c", script)
  }
}
