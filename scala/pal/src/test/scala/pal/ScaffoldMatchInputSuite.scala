package pal

import TestScaffoldCircuitProgram.scalar

class ScaffoldMatchInputSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  private lazy val built = Expr.share { ScaffoldMatchInput.fixture() }

  test("frozen reverse prefix frontier and copied heads") {
    val (circuit, _, machine) = built
    var root = machine.initialNode()
    val rng = new PyRandom(913)
    var globalWord = ""
    var pattern = ""
    var text = ""
    val positions = Array(0, 0)
    var active = false
    val commands = "abba!a>>b>>a[]x>y["
    for (tick <- 0 until 150) {
      var command = if (tick < commands.length) { commands(tick) } else { rng.choice("ab!<>[]xy.".toVector) }
      if ("ab".contains(command)) {
        globalWord += command
        if (active) { text += command }
      } else if (command == '!') {
        pattern = globalWord.reverse
        text = ""
        positions(0) = 0
        positions(1) = pattern.length
        active = true
      } else if ("<>[]".contains(command)) {
        val index = if ("[]".contains(command)) { 1 } else { 0 }
        if ("<[".contains(command) && positions(index) == 0) { command = '.' }
        else if (">]".contains(command)) { positions(index) = math.min(positions(index) + 1, pattern.length + text.length) }
        else { positions(index) -= 1 }
      } else if (command == 'x') { positions(0) = positions(1) }
      else if (command == 'y') { positions(1) = positions(0) }
      root = machine.step(root, command).get
      assertEquals(scalar(circuit, root, "circuit.fault"), false, (tick, command))
      val word = pattern + text
      for ((name, position) <- Vector("A", "B").zip(positions)) {
        val expected: Any = if (active && position < word.length) { word(position) } else { None }
        assertEquals(scalar(circuit, root, name + ".observed"), expected, (tick, command, name, position, word))
      }
    }
  }

  test("match input grammar is byte-identical to Python") {
    PyDiff.assertSameAsPython(built._3.compile(), "-c", "from scaffold_match_input import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = fixture()[2]\nprint(m.compile(), end='')")
  }

  test("nonunit movement is rejected") {
    interceptMessage[IllegalArgumentException]("unit direction required") { built._2._1.move(0) }
  }
}
