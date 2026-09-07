package pal

import TestScaffoldCircuitProgram.scalar

/** The source has no dedicated delayed-circuit suite; cover its construction,
  * fixed round clock and short-word answers without claiming arbitrary PAL.
  */
class ScaffoldDelayedPalSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  test("derived power-of-two schedule constraints") {
    for (rates <- Vector(Rates(4, 1, 1, 1, 32), Rates(8, 1, 1, 64, 32), Rates(8, 1, 1, 1, 16), Rates(8, 1, 1, 1, 33))) {
      interceptMessage[IllegalArgumentException]("the current worker tables require the derived k=8 power-of-two schedule") {
        new ScaffoldDelayedPal(new Circuit(), rates)
      }
    }
  }

  for (dual <- Vector(false, true)) {
    test(s"two-stage local controller at derived rates compiles byte-identically to Python, dual=$dual") {
      val (_, _, machine) = Expr.share { ScaffoldDelayedPal.build(dualFlags = dual) }
      val argument = if (dual) { "True" } else { "False" }
      PyDiff.assertSameAsPython(machine.compile(), "-c", s"from scaffold_delayed_pal import build\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = build(dual_flags=$argument)[2]\nprint(m.compile(), end='')")
    }
  }

  test("ready transitions delimit a whole round and short-word answers") {
    val rates = Rates(8, 1, 1, 32, 32)
    val (circuit, _, machine) = Expr.share { ScaffoldDelayedPal.build(Some(rates)) }
    assert(machine.run(""))
    for (word <- Words.upTo("ab", 3).filter(_.nonEmpty)) {
      var root = machine.initialNode()
      for (char <- word) {
        assertEquals(scalar(circuit, root, "pal.phase"), "ready")
        root = machine.step(root, char).get
        var transitions = 1
        while (scalar(circuit, root, "pal.phase") != "ready") {
          assert(transitions < rates.round)
          root = machine.step(root, if (char == 'a') { 'b' } else { 'a' }).get
          transitions += 1
        }
        assertEquals(transitions, rates.round)
        assertEquals(scalar(circuit, root, "circuit.fault"), false)
      }
      assertEquals(root.labels(machine.accepting), word == word.reverse, word)
    }
  }
}
