package pal

import FppFinite.Instruction.*
import FppSubroutine.*

/** FPP with actual input preparation and marked output on independent tapes. (test_fpp_subroutine.py) */
class FppSubroutineSuite extends munit.FunSuite {

  def expectedMarks(word: String): Vector[Int] =
    (1 to word.length).map(i => if (word.take(i) == word.take(i).reverse) { 1 } else { 0 }).toVector

  /** Python: `MarkedProgram(alphabet, ntapes)` with `code`, `start`, `source_alphabet` assigned from the file. */
  def savedMarkedProgram(): MarkedProgram = {
    val saved = ControllerArtifacts.load(PyDiff.readGolden("generated/fpp-marked-controller.json"))
    val routine = new MarkedProgram(saved.alphabet, saved.ntapes)
    routine.sourceAlphabet = saved.sourceAlphabet
    routine.copyCodeFrom(saved)
    routine.start = saved.start
    routine
  }

  test("marks all prefix palindromes from plain input") {
    val routine = savedMarkedProgram()
    routine.validate()
    for (n <- 0 until 11) {
      for (word <- Fpp.binaryWords(n)) {
        val result = routine.runMarked(word)
        assertEquals(result.marks, expectedMarks(word), word)
        assertEquals(result.prepared, word + "#" + word.reverse, word)
        assertEquals(result.positions(MARKS), 0)
        assert(result.steps < 300 * (n + 1), word)
      }
    }
  }

  test("no emit or host reverse in transition table") {
    val routine = buildMarkedProgram()
    assert(routine.instructions.forall {
      case Read(_, _) | Write(_, _, _) | Move(_, _, _) | Halt => true
      case Emit(_) => false
    })
    routine.validate()
  }

  test("long runs and periodic inputs") {
    val routine = buildMarkedProgram()
    for (n <- Seq(32, 128, 512, 2048)) {
      for (word <- Seq("a" * n, "ab" * n,
        "b" * n + "a" + "b" * (n / 2) + "aa" + "b" * n)) {
        val result = routine.runMarked(word)
        assertEquals(result.marks, expectedMarks(word), word.take(40))
        assert(result.steps < 300 * (word.length + 1))
      }
    }
  }
}
