package pal

import TestScaffoldCircuitProgram.{fixture, scalar, stack}
import FppFinite.{LEFT, END, BLANK}

class ScaffoldCircuitProgramSuite extends munit.FunSuite {
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(180, "s")

  private def compare(quantum: Int, coarse: Boolean = false, sharedCells: Boolean = false): Unit = Expr.share {
    val (circuit, lowered, machine) = fixture(quantum, coarse, sharedCells)
    val source = machine.compile()
    assert(source.length < 6000000)
    assert(new Grammar(source).accepts("."))
    PyDiff.assertSameAsPython(source, "-c",
      s"from test_scaffold_circuit_program import fixture; print(fixture($quantum, ${if (coarse) { "True" } else { "False" }}, ${if (sharedCells) { "True" } else { "False" }})[2].compile(), end='')")
    for (word <- Vector("", "a", "abba", "aababa")) {
      var root = machine.evaluate(LEFT + word + END + "<" * (word.length + 2) + "!").get
      val tapes = FppFinite.Tape.fresh(lowered.tapes.size)
      tapes(FppSubroutine.SOURCE) = FppFinite.Tape.bounded(word)
      val expected = lowered.kernel.execution(tapes.toVector, Array.fill(tapes.length)(0))
      val adapted = new ReadBlocks.Execution {
        val program: ReadBlocks.Program = ScaffoldCircuitProgram.readBlockProgram(lowered.kernel)
        def state: Int = expected.state
        def done: Boolean = expected.done
        def step(): Unit = expected.step()
      }
      var ticks = 0
      while (!expected.done && ticks < 100000) {
        for (_ <- 0 until quantum if !expected.done) {
          if (coarse) { ReadBlocks.step(adapted) } else { expected.step() }
        }
        root = machine.step(root, '.').get
        assertEquals(scalar(circuit, root, lowered.pcKey), expected.state)
        assertEquals(scalar(circuit, root, lowered.doneKey), expected.done)
        for ((tape, index) <- lowered.tapes.zipWithIndex) {
          assertEquals(scalar(circuit, root, tape.symbolKey), expected.tapes(index).read(expected.positions(index)))
        }
        ticks += 1
      }
      assert(expected.done)
      for ((tape, index) <- lowered.tapes.zipWithIndex) {
        val left = stack(circuit, root, tape.left)
        val right = stack(circuit, root, tape.right)
        assertEquals(left.length, expected.positions(index))
        val contents = left.reverse ++ Vector(scalar(circuit, root, tape.symbolKey)) ++ right
        val actual = contents.zipWithIndex.collect { case (value, i) if value != BLANK => i -> value }.toMap
        val wanted: Map[Int, Any] = expected.tapes(index).toMap.filter(_._2 != BLANK)
        assertEquals(actual, wanted, (word, index).toString)
      }
    }
  }

  test("real FPP table matches each instruction and final tape; byte-identical PEG") {
    compare(1)
    compare(3)
  }
  test("read blocks match raw instructions with shared local slots; byte-identical PEG") {
    compare(1, coarse = true)
    compare(3, coarse = true)
  }
  test("mutually exclusive tape moves share instruction cells; byte-identical PEG") {
    compare(1, sharedCells = true)
    compare(3, sharedCells = true)
  }
  test("shared coarse cells and exhausted instruction layout fail like Python") {
    val kernel = FppSubroutine.buildMarkedProgram("ab")
    val error = intercept[IllegalArgumentException] {
      new ScaffoldCircuitProgram.Program(new Circuit(), kernel, "f", coarse = true, sharedCells = true)
    }
    assertEquals(error.getMessage, "shared instruction cells require one raw instruction per step")
    val program = new ScaffoldCircuitProgram.Program(new Circuit(), kernel, "f", sharedCells = true)
    program.step()
    assertEquals(intercept[IllegalArgumentException](program.step()).getMessage, "finite instruction cell layout exhausted")
  }
}
