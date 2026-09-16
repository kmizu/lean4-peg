package pal

import scala.collection.immutable.VectorMap

import ReadBlocks.*
import ReadBlocks.Instruction.*

/** read_blocks.py has no Python test; expectations were computed with python3 on the
  * same stub program (`read_blocks.analyze` on an object with `code` and `ntapes`).
  */
class ReadBlocksSuite extends munit.FunSuite {

  private final class StubProgram(val code: Vector[Instruction], val ntapes: Int) extends Program

  private val sample = new StubProgram(Vector(
    Read(0, VectorMap("a" -> 1, "b" -> 3, "c" -> 1)),
    Move(0, 1, 2),
    Write(1, "x", 5),
    Move(1, -1, 4),
    Move(1, -1, 6),
    Halt,
    Move(0, 1, 5)), 2)

  test("analyze matches python3 read_blocks.analyze on a stub program") {
    // python3: (0, 5, 1, 3, 2, 4, 6) [0, 5] {1: 0, 3: 0, 4: 1, 6: 0} (1, 0, 0, 2) 4
    val result = analyze(sample)
    assertEquals(result.order, Vector(0, 5, 1, 3, 2, 4, 6))
    assertEquals(result.cuts, Set(0, 5))
    assertEquals(result.slots.toVector, Vector(1 -> 0, 3 -> 0, 4 -> 1, 6 -> 0))
    assertEquals(result.bounds, Vector(1, 0, 0, 2))
    assertEquals(result.maxInstructions, 4)
  }

  test("analyze agrees with python3 on the printed summary") {
    val result = analyze(sample)
    val got = s"${PyFormat.intListRepr(result.order)} ${PyFormat.intListRepr(result.cuts.toVector.sorted)} " +
      s"${result.slots.map { case (k, v) => s"$k: $v" }.mkString("{", ", ", "}")} " +
      s"${PyFormat.intListRepr(result.bounds)} ${result.maxInstructions}\n"
    PyDiff.assertSameAsPython(got, "-c",
      """from read_blocks import analyze
        |class P: pass
        |p = P(); p.ntapes = 2
        |p.code = [("read", 0, {"a": 1, "b": 3, "c": 1}), ("move", 0, 1, 2), ("write", 1, "x", 5),
        |          ("move", 1, -1, 4), ("move", 1, -1, 6), ("halt",), ("move", 0, 1, 5)]
        |r = analyze(p)
        |print(list(r["order"]), sorted(r["cuts"]), r["slots"], list(r["bounds"]), r["max_instructions"])
        |""".stripMargin)
  }

  test("a non-reading cycle is rejected") {
    val error = intercept[IllegalArgumentException](analyze(new StubProgram(Vector(Move(0, 1, 0)), 1)))
    assertEquals(error.getMessage, "non-reading instruction cycle has no finite block bound")
  }

  test("emit is rejected") {
    val error = intercept[IllegalArgumentException](analyze(new StubProgram(Vector(Emit(0)), 1)))
    assertEquals(error.getMessage, "read blocks require read/write/move/halt instructions")
  }

  test("step runs one block: the entry instruction and everything up to the next read/halt") {
    val blockProgram = new StubProgram(Vector(
      Read(0, VectorMap("a" -> 1)),
      Move(0, 1, 2),
      Write(0, "x", 3),
      Read(0, VectorMap("x" -> 4)),
      Halt), 1)
    final class StubExecution(val program: Program) extends Execution {
      var state: Int = 0
      var done: Boolean = false
      var trace: Vector[Int] = Vector.empty
      def step(): Unit = {
        trace :+= state
        program.code(state) match {
          case Read(_, choices) => state = choices.values.head
          case Move(_, _, next) => state = next
          case Write(_, _, next) => state = next
          case Emit(next) => state = next
          case Halt => done = true
        }
      }
    }
    val execution = new StubExecution(blockProgram)
    step(execution)
    assertEquals(execution.trace, Vector(0, 1, 2))
    assertEquals(execution.state, 3)
    step(execution)
    assertEquals(execution.trace, Vector(0, 1, 2, 3))
    assertEquals(execution.state, 4)
    step(execution)
    assert(execution.done)
  }
}
