package pal

import ScaffoldPal.run

/** Port of `test_scaffold_pal.py`: whole-prefix palindrome correctness using
  * finite FPP, without KMP addresses. The controller is also driven in Python on
  * the same words and budgets and its outputs and statistics compared line by line.
  */
class ScaffoldPalSuite extends munit.FunSuite {
  import ScaffoldGalilFixture.prefixAnswers

  // 127 words, each drained to completion (unbounded FPP work per letter)
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  private val restartWords = Vector("abbaabba", "ababaabababa", "aaaaaaa", "abbbbbbbba", "aababbabbaa")

  test("all binary prefixes through length six") {
    for (word <- Words.upTo("ab", 6)) {
      assertEquals(run(word).outputs, prefixAnswers(word), word)
    }
  }

  test("online control handles both parities and multiple FPP restarts") {
    for (word <- restartWords) {
      val result = run(word)
      assertEquals(result.outputs, prefixAnswers(word), word)
      assert(result.fppCalls > 0, result)
      assert(result.stats.radius <= 391, result.stats)
      assert(result.stats.fields <= 396, result.stats)
    }
  }

  test("fixed work does not drain an unbounded backlog") {
    val result = run("ab" * 10, Some(3))
    assertEquals(result.outputs.length, 20)
    assertEquals(result.stats.steps, 60)
    assertEquals(result.maxMicrosteps, 3)
    // A bounded node count alone is not real-time recognition: this concrete
    // positive is missed while the real finite fallback is still executing.
    assertEquals(run("aa", Some(3)).outputs, Vector(1, 0))
  }

  test("outputs and statistics match python for drained and budgeted runs") {
    def pyList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")
    val out = new StringBuilder
    for (word <- Vector("", "a", "ab", "aa", "abba") ++ restartWords) {
      val result = run(word)
      out.append(s"'$word' ${pyList(result.outputs)} ${result.pythonRepr}\n")
    }
    for ((word, budget) <- Seq(("ab" * 10, 3), ("aa", 3), ("aaaa", 50))) {
      val result = run(word, Some(budget))
      out.append(s"'$word' $budget ${pyList(result.outputs)} ${result.pythonRepr}\n")
    }
    PyDiff.assertSameAsPython(out.toString, "-c",
      """from scaffold_pal import run
        |for word in ("", "a", "ab", "aa", "abba", "abbaabba", "ababaabababa", "aaaaaaa", "abbbbbbbba", "aababbabbaa"):
        |  outputs, stats = run(word); print(repr(word), outputs, stats)
        |for word, budget in (("ab" * 10, 3), ("aa", 3), ("aaaa", 50)):
        |  outputs, stats = run(word, budget=budget); print(repr(word), budget, outputs, stats)
        |""".stripMargin)
  }
}
