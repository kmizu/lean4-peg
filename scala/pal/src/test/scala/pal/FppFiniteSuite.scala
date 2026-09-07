package pal

import FppFinite.*

/** The finite controller must agree with string definitions, not the prototype. (test_fpp_finite.py) */
class FppFiniteSuite extends munit.FunSuite {

  /** Proper borders of `word`, longest first. */
  def borders(word: String): Vector[Int] =
    (word.length - 1 to 1 by -1).filter(k => word.take(k) == word.takeRight(k)).toVector

  /** Palindromic prefix lengths of `word`, longest first. */
  def palindromicPrefixes(word: String): Vector[Int] =
    (word.length to 1 by -1).filter(k => word.take(k) == word.take(k).reverse).toVector

  test("exhaustive complete border chain") {
    val program = buildProgram("ab#")
    program.validate()
    for (n <- 0 until 12) {
      for (word <- Fpp.binaryWords(n)) {
        val result = program.run(word)
        assertEquals(result.borders, borders(word), word)
        assert(result.steps < 250 * (n + 1), word)
      }
    }
  }

  test("fpp: execute the checked-in finite table, not a Scala algorithm callback") {
    val program = ControllerArtifacts.load(PyDiff.readGolden("generated/fpp-offline-controller.json"))
    program.validate()
    for (n <- 0 until 10) {
      for (word <- Fpp.binaryWords(n)) {
        val result = program.run(word + "#" + word.reverse)
        assertEquals(result.borders, palindromicPrefixes(word), word)
      }
    }
  }

  test("long fallback and queue refill") {
    val program = buildProgram("ab#")
    for (n <- Seq(32, 128, 512, 2048)) {
      for (word <- Seq("a" * n, "a" * n + "b", "ab" * n,
        "b" * n + "a" + "b" * (n / 2) + "aa" + "b" * n)) {
        val result = program.run(word)
        assertEquals(result.borders, borders(word))
        assert(result.steps < 250 * (word.length + 1))
      }
    }
  }
}
