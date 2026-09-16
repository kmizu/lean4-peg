package pal

import FppTape.{borderMachine, singleHeadBorderMachine, initialPalindromes}

/** Independent oracles for the Fischer–Paterson local-head experiment. (test_fpp_tape.py) */
class FppTapeSuite extends munit.FunSuite {

  /** Proper borders, longest first. */
  def borders(word: String): Vector[Int] =
    (word.length - 1 to 1 by -1).filter(b => word.take(b) == word.takeRight(b)).toVector

  /** Longest proper border (0 if none). */
  def longestBorder(word: String): Int = borders(word).headOption.getOrElse(0)

  test("single head lowering") {
    for (n <- 0 until 12) {
      for (word <- Fpp.binaryWords(n)) {
        val result = singleHeadBorderMachine(word, true)
        assertEquals(result.borders, borders(word), word)
        assert(result.operations <= 200 * (n + 1), word)
      }
    }
  }

  test("all initial palindromes") {
    for (n <- 0 until 12) {
      for (word <- Fpp.binaryWords(n)) {
        val expected = (n to 1 by -1).filter(k => word.take(k) == word.take(k).reverse).toVector
        for (singleHead <- Seq(false, true)) {
          val result = initialPalindromes(word, singleHead = singleHead)
          assertEquals(result.borders, expected, word)
          assert(result.operations <= 300 * (n + 1), word)
        }
      }
    }
  }

  test("every binary word through length twelve") {
    for (n <- 0 until 13) {
      for (word <- Fpp.binaryWords(n)) {
        val result = borderMachine(word)
        assertEquals(result.border, longestBorder(word), word)
        assert(result.operations <= 100 * (n + 1), word)
      }
    }
  }

  test("nonperiodic palindromes") {
    for (n <- 1 until 22) {
      for (half <- Fpp.binaryWords((n + 1) / 2)) {
        val word = half + (if (n % 2 == 1) { half.dropRight(1) } else { half }).reverse
        val expected = longestBorder(word)
        if (n - expected > n / 2.0) {
          assertEquals(borderMachine(word).border, expected, word)
        }
      }
    }
  }

  test("long runs and repeated fallback") {
    for (n <- Seq(16, 64, 256, 1024, 4096)) {
      val words = Seq("a" * n, "a" * (n - 1) + "b", "ab" * n,
        "b" * n + "a" + "b" * (n / 2) + "aa" + "b" * n)
      for (word <- words) {
        val expected = longestBorder(word)
        val result = borderMachine(word)
        assertEquals(result.border, expected, word.take(60))
        assert(result.operations <= 100 * (word.length + 1))
        val single = singleHeadBorderMachine(word, true)
        assertEquals(single.border, expected, word.take(60))
        assert(single.operations <= 200 * (word.length + 1))
      }
    }
  }
}
