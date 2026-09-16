package pal

/** Port of `test_gs_dual_flags.py`, plus a state-count check against Python. */
class GsDualFlagsSuite extends munit.FunSuite {
  import GsDualFlags.{compileDualFlags, dualFlagController}
  import GsHeads.{compileController, unitMoves}
  import GsLocalClock.DEFAULT_DUAL

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  def isPalindrome(word: String): Boolean = word == word.reverse

  test("palindrome prefix intervals and single length clock") {
    val program = compileDualFlags()
    val rng = new PyRandom(921)
    val words = PyItertools.wordsBelow("ab", 10) ++
      (0 until 30).map(_ => rng.word("ab", 512)) ++
      Vector("a" * 2048, "ab" * 2048, ("a" * 8 + "b") * 8 + "b")
    words.foreach { word =>
      Vector(0, word.length / 2, 3 * word.length / 4).foreach { lower =>
        val observer = new DualFlagVM(word, lower, word.length, Some(program))
        val expected = (word.length - 1 to lower by -1).map(n => isPalindrome(word.take(n))).toVector
        assertEquals(observer.runFlags(), expected, (word.take(30), word.length, lower))
        assert(observer.steps <= DEFAULT_DUAL.flagView * math.max(1, word.length) + 1)
      }
    }
  }

  test("state counts agree with the Python compiler") {
    val actual = Vector(4, 8).map { k =>
      val reduced = compileController(k, controller = k => dualFlagController(k))
      s"$k ${reduced.code.size} ${reduced.constructionStates} ${unitMoves(reduced).code.size}"
    }.mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import compile_controller, unit_moves\nfrom gs_dual_flags import dual_flag_controller\n" +
        "for k in (4, 8):\n  p = compile_controller(k, controller=dual_flag_controller)\n" +
        "  print(k, len(p.code), p.construction_states, len(unit_moves(p).code))")
    intercept[IllegalArgumentException](new DualFlagVM("ab", 0, 3, Some(compileDualFlags())))
  }
}
