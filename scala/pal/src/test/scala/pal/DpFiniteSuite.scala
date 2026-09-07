package pal

import DpFinite.*

/** Oracle: two marked prefix lengths, with a strict unary lower bound. (test_dp_finite.py) */
class DpFiniteSuite extends munit.FunSuite {
  import DpFiniteSuite.expected

  /** Python: `DpProgram(alphabet, ntapes)` with `code`, `start`, `source_alphabet`, `found` from the file. */
  def savedDpProgram(): DpProgram = {
    val saved = ControllerArtifacts.load(PyDiff.readGolden("generated/dp-place-controller.json"))
    val machine = new DpProgram(saved.alphabet, saved.ntapes)
    machine.sourceAlphabet = saved.sourceAlphabet
    machine.copyCodeFrom(saved)
    machine.start = saved.start
    machine.found = saved.found
    machine
  }

  test("all short words and lower bounds") {
    val machine = buildDpProgram()
    for (n <- 0 until 11) {
      for (word <- Fpp.binaryWords(n)) {
        for (lower <- 0 until n / 4 + 2) {
          val result = machine.runDp(word, lower)
          assertEquals(result.h, expected(word, lower), (word, lower))
          assert(result.steps < 400 * (n + 1), (word, lower))
        }
      }
    }
  }

  test("place encoded windows") {
    val machine = savedDpProgram()
    machine.validate()
    for (n <- 1 until 9) {
      for (symbols <- Fpp.binaryWords(n)) {
        // s is Galil's special inter-symbol place, renamed from reserved _.
        val word = symbols.mkString("s")
        for (lower <- Seq(0, 1, 2, n)) {
          assertEquals(machine.runDp(word, lower).h, expected(word, lower))
        }
      }
    }
  }

  test("long chain skips strict lower bound") {
    val machine = buildDpProgram()
    for (n <- Seq(32, 128, 512, 2048)) {
      val word = "a" * n
      for (lower <- Seq(0, 1, n / 8, n / 4)) {
        val result = machine.runDp(word, lower)
        assertEquals(result.h, expected(word, lower))
        assert(result.steps < 400 * (n + 1))
      }
    }
  }
}

object DpFiniteSuite {

  /** The least h > lower with prefix palindromes of lengths 2h+1 and 4h+1. */
  def expected(word: String, lower: Int): Option[Int] =
    (lower + 1 to Math.floorDiv(word.length - 1, 4)).find { h =>
      word.take(2 * h + 1) == word.take(2 * h + 1).reverse &&
        word.take(4 * h + 1) == word.take(4 * h + 1).reverse
    }
}
