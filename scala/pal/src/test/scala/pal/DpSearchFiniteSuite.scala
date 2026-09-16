package pal

import FppFinite.*
import DpFinite.{LOWER, OUTPUT}
import DpSearchFinite.*

/** Compare local doubling search with the defining suffix-palindrome test. (test_dp_search_finite.py) */
class DpSearchFiniteSuite extends munit.FunSuite {
  import DpSearchFiniteSuite.{execute, expected}

  def checkSearch(p: Program, prefix: String, suffix: String, lower: Int): Unit = {
    val (h, result, original) = execute(p, prefix, suffix, lower)
    assertEquals(h, expected(prefix, lower), (prefix, lower))
    assertEquals(result.state, if (h.isDefined) { p.found.get } else { p.missed.get })
    assertEquals(result.positions(WINDOW), prefix.length)
    assertEquals(result.tapes(LOWER), Tape.bounded("1" * lower))
    var want = original.zipWithIndex.map(_.swap).toMap
    for (found <- h) {
      for (multiple <- 1 to 4) {
        val index = prefix.length - multiple * found
        want = want.updated(index, periodSymbol(want(index)))
      }
      assertEquals(result.positions(OUTPUT), 0)
    }
    assertEquals(result.tapes(WINDOW).toMap.filter(_._2 != BLANK), want)
  }

  test("saved table without builder") {
    val p = ControllerArtifacts.load(PyDiff.readGolden("generated/dp-search-controller.json"))
    p.validate()
    for ((prefix, lower) <- Seq(("asasa", 0), ("as" * 35, 3), ("aabasbbbs" * 12, 0), ("b", 1))) {
      checkSearch(p, prefix, "babas", lower)
    }
  }

  test("all short binary prefixes and lower bounds") {
    val p = buildSearchProgram("ab")
    for (n <- 1 until 8) {
      for (word <- Fpp.binaryWords(n)) {
        for (lower <- Seq(0, 1, n)) {
          checkSearch(p, word, "baba", lower)
        }
      }
    }
  }

  test("places final boundary and multiple doublings") {
    val p = buildSearchProgram()
    val words = Seq("a", "aaaaa", "aab" * 20, "aaaab" * 12,
      "a" * 65, "ababbb" * 20, "aababbabbbab")
    for (word <- words) {
      val places = word.mkString("s")
      for (prefix <- Seq(places, places + "s")) {
        for (lower <- Seq(0, 1, 3, prefix.length)) {
          checkSearch(p, prefix, "sbasa", lower)
        }
      }
    }
  }

  test("first answer after multiple doublings") {
    val p = buildSearchProgram("ab")
    for ((h, root) <- Seq((3, "aabb"), (5, "abbbab"), (9, "abbababbaa"))) {
      val word = (0 until 4 * h + 1).map(j => root(math.min(j % (2 * h), 2 * h - j % (2 * h)))).mkString
      assertEquals(expected(word, 0), Some(h))
      checkSearch(p, word, "ba", 0)
    }
  }

  test("window access stays local to distant center") {
    class GuardedWindow(center: Int, initial: Iterable[(Int, String)]) extends Tape(initial) {
      private def guard(kind: String, key: Int): Unit = {
        if (!(center - 9 <= key && key <= center)) {
          throw new AssertionError((s"nonlocal $kind", key, center))
        }
      }
      override def read(position: Int): String = { guard("read", position); super.read(position) }
      override def write(position: Int, symbol: String): Unit = { guard("write", position); super.write(position, symbol) }
    }

    val p = buildSearchProgram("ab")
    val counts = Vector.newBuilder[Int]
    for (center <- Seq(19, 1009, 100009)) {
      val window = new GuardedWindow(center, (center - 9 until center).map(i => i -> "a"))
      window.write(center, centerSymbol("a"))
      val tapes = Tape.fresh(p.ntapes)
      tapes(WINDOW) = window
      tapes(LOWER) = new Tape(Seq(0 -> LEFT, 1 -> END))
      val positions = Array.fill(p.ntapes)(0)
      positions(WINDOW) = center
      val result = p.execute(tapes, positions, 5000)
      assertEquals(Some(result.state), p.found)
      assertEquals(result.positions(WINDOW), center)
      assertEquals(tapes(OUTPUT).values.count(_ == "1"), 1)
      counts += result.steps
    }
    assertEquals(counts.result().distinct.size, 1)
  }
}

object DpSearchFiniteSuite {

  /** Load `^prefix suffix$` with the centre tag, run, and decode the unary answer if found. */
  def execute(p: Program, prefix: String, suffix: String = "", lower: Int = 0): (Option[Int], Run, Vector[String]) = {
    val tapes = Tape.fresh(p.ntapes)
    val center = prefix.length
    val plain = ((LEFT +: (prefix + suffix).map(_.toString)) :+ END).toVector
    val tokens = plain.updated(center, centerSymbol(plain(center)))
    tapes(WINDOW) = Tape.of(tokens)
    tapes(LOWER) = Tape.bounded("1" * lower)
    val positions = Array.fill(p.ntapes)(0)
    positions(WINDOW) = center
    val result = p.execute(tapes, positions, 3000 * (prefix.length + lower + 1))
    val h = if (p.found.contains(result.state)) {
      Some(tapes(OUTPUT).values.count(_ == "1"))
    } else {
      None
    }
    (h, result, tokens)
  }

  /** The least h > lower with suffix palindromes of lengths 2h+1 and 4h+1. */
  def expected(prefix: String, lower: Int): Option[Int] =
    (lower + 1 to Math.floorDiv(prefix.length - 1, 4)).find { h =>
      prefix.takeRight(2 * h + 1) == prefix.takeRight(2 * h + 1).reverse &&
        prefix.takeRight(4 * h + 1) == prefix.takeRight(4 * h + 1).reverse
    }
}
