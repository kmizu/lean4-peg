package pal

import TestScaffoldCircuitProgram.scalar
import ScaffoldGsHeadsSuite.stack

class ScaffoldGsFlagsSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  for (dual <- Vector(false, true)) {
    test(s"${if (dual) "oppositely oriented" else "frozen mirror"} views and entire flag stack, with Python byte comparison") {
      val (circuit, worker, machine) = Expr.share { ScaffoldGsFlags.fixture(dual) }
      for ((word, lower) <- Vector("abba" -> 2, "ababa" -> 2)) {
        var node = machine.initialNode()
        def step(char: Char): Unit = {
          node = machine.step(node, char).get
          assertEquals(scalar(circuit, node, "circuit.fault"), false)
        }
        for ((char, index) <- word.zipWithIndex) {
          if (index == lower) { step('|') }
          step(char)
          while (scalar(circuit, node, worker.phaseKey) != "idle") { step('.') }
        }
        step('!')
        val observer: HeadVM[?] = if (dual) {
          new DualFlagVM(word, lower, word.length, Some(worker.program))
        } else { new FlagVM(word, lower, word.length, Some(worker.program)) }
        var ticks = 0
        while (scalar(circuit, node, worker.phaseKey) != "done") {
          assert(ticks < 100000, "test interpreter exceeded its watchdog")
          ticks += 1
          val phase = scalar(circuit, node, worker.phaseKey)
          step('.')
          if (phase == "run" && !observer.done) { observer.step() }
          assertEquals(scalar(circuit, node, worker.pcKey), observer.state)
        }
        val expected = (lower until word.length).map(n => word.take(n) == word.take(n).reverse).toVector
        assertEquals(stack(circuit, node, worker.flags), expected)
      }
      val argument = if (dual) { "True" } else { "False" }
      PyDiff.assertSameAsPython(machine.compile(), "-c", s"from scaffold_gs_flags import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = fixture(dual=$argument)[2]\nprint(m.compile(), end='')")
    }
  }
}
