package pal

import FppFinite.*
import DpSearchFinite.WINDOW
import MoveCenterFinite.{buildMoveCenterProgram, boundary, decode}

/** Local nonchain center selection must preserve text and avoid coordinates. (test_move_center_finite.py) */
class MoveCenterFiniteSuite extends munit.FunSuite {

  /** Longest odd palindromic suffix length. */
  def longestOddSuffix(word: String): Int =
    (1 to word.length by 2).filter(k => word.takeRight(k) == word.takeRight(k).reverse).max

  /** Run the controller on `word` placed at `base`; returns the step count. */
  def check(p: Program, word: String, base: Int = 5): Int = {
    val tapes = Tape.fresh(p.ntapes)
    val positions = Array.fill(p.ntapes)(0)
    val left = base
    val right = base + word.length - 1
    for ((c, k) <- word.zipWithIndex) {
      val i = left + k
      tapes(WINDOW).write(i, (if (i % 2 == 1) { "C:" } else { "P:" }) + c)
    }
    tapes(WINDOW).write(left, boundary(word.head.toString, left = true, right = left == right))
    if (left != right) {
      tapes(WINDOW).write(right, boundary(word.last.toString, right = true))
    }
    tapes(WINDOW).write(left - 1, "outside-left")
    tapes(WINDOW).write(right + 1, "outside-right")
    positions(WINDOW) = right
    val result = p.execute(tapes, positions, 700 * (word.length + 1))
    val longest = longestOddSuffix(word)
    val center = right - (longest - 1) / 2
    assertEquals(result.positions(WINDOW), center, word)
    assertEquals((left to right).map(i => decode(result.tapes(WINDOW)(i))).mkString, word)
    for (i <- left to right) {
      val expected = (if (i == center && center == right) { "CRR:" } else if (i == center) { "C:" }
        else if (i == right) { "RR:" } else { "" }) + word(i - left)
      assertEquals(result.tapes(WINDOW)(i), expected, (word, i))
    }
    assertEquals(result.tapes(WINDOW)(left - 1), "outside-left")
    assertEquals(result.tapes(WINDOW)(right + 1), "outside-right")
    for (tape <- 0 until p.ntapes) {
      if (tape != WINDOW) {
        assertEquals(result.positions(tape), 0)
        assert(result.tapes(tape).values.forall(_ == BLANK), (word, tape))
      }
    }
    assert(result.steps < 500 * (word.length + 1))
    result.steps
  }

  test("all short binary intervals") {
    val p = buildMoveCenterProgram("ab")
    for (n <- 1 until 10) {
      for (word <- Fpp.binaryWords(n)) {
        check(p, word)
      }
    }
  }

  test("place intervals and translation do not change local work") {
    val p = buildMoveCenterProgram("abs")
    for (word <- Seq("a", "s", "asbsa", "asbsasbsa", "ssabss", "ab" * 64, "a" * 513)) {
      assertEquals(check(p, word, 11), check(p, word, 100011))
    }
  }

  test("colon is a valid source symbol") {
    val p = buildMoveCenterProgram("a:")
    for (word <- Seq(":", "a:", ":::a:", ":a:")) {
      check(p, word)
    }
  }

  test("saved table runs without the builder") {
    val p = ControllerArtifacts.load(PyDiff.readGolden("generated/move-center-controller.json"))
    p.validate()
    for (word <- Seq("a", "asbsa", "ab" * 17, "a" * 32 + "b" + "a" * 31)) {
      check(p, word, 0)
    }
  }

  test("reuses the same scratch tapes") {
    val p = buildMoveCenterProgram("abs")
    val tapes = Tape.fresh(p.ntapes)
    val positions = Array.fill(p.ntapes)(0)
    for (word <- Seq("asbsa" * 30, "b", "abs", "a" * 64, "sas")) {
      tapes(WINDOW) = Tape.of(word.map(_.toString))
      tapes(WINDOW).write(0, boundary(word.head.toString, left = true, right = word.length == 1))
      if (word.length > 1) {
        tapes(WINDOW).write(word.length - 1, boundary(word.last.toString, right = true))
      }
      positions(WINDOW) = word.length - 1
      val result = p.execute(tapes, positions, 700 * (word.length + 1))
      val longest = longestOddSuffix(word)
      assertEquals(result.positions(WINDOW), word.length - 1 - (longest - 1) / 2)
      for (t <- 0 until p.ntapes) {
        if (t != WINDOW) {
          assertEquals(positions(t), 0)
          assert(tapes(t).values.forall(_ == BLANK))
        }
      }
    }
  }
}
