package pal

import TestScaffoldCircuitProgram.scalar

class ScaffoldGsMatcherSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  private lazy val built = Expr.share { ScaffoldGsMatcher.fixture() }

  test("real queues and every matching instruction") {
    val (circuit, worker, machine) = built
    for ((prefix, text) <- Vector("a" -> "baaa", "abb" -> "bbabba")) {
      var node = machine.initialNode()
      def step(char: Char): Unit = {
        node = machine.step(node, char).get
        assertEquals(scalar(circuit, node, "circuit.fault"), false)
      }
      for (char <- prefix) {
        step(char)
        while (scalar(circuit, node, worker.phaseKey) != "idle") { step('.') }
      }
      step('!')
      val observer = new StreamingMatcher(prefix.reverse, Some(worker.program))
      def drain(): Unit = {
        var ticks = 0
        while (scalar(circuit, node, worker.phaseKey) != "run" || !observer.waiting) {
          assert(ticks < 100000, "test interpreter exceeded its watchdog")
          ticks += 1
          val phase = scalar(circuit, node, worker.phaseKey)
          step('.')
          if (phase == "run") { observer.step() }
          assertEquals(scalar(circuit, node, worker.pcKey), observer.state)
        }
      }
      drain()
      for ((char, index) <- text.zipWithIndex) {
        observer.append(char)
        step(char)
        drain()
        val end = index + 1
        val expected = end >= prefix.length && text.slice(end - prefix.length, end) == prefix.reverse
        assertEquals(node.labels("accept"), expected, (prefix, text, end))
      }
    }
  }

  test("ordinary matcher grammar is byte-identical to Python") {
    PyDiff.assertSameAsPython(built._3.compile(), "-c", "from scaffold_gs_matcher import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = fixture()[2]\nprint(m.compile(), end='')")
  }
}
