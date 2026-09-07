package pal

/** Port of `test_gs_flag_heads.py`, plus a state-count check against Python. */
class GsFlagHeadsSuite extends munit.FunSuite {
  import GsFlagHeads.{compileFlags, flagController}
  import GsHeads.{compileController, unitMoves}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  lazy val program: Program = compileFlags()

  def isPalindrome(word: String): Boolean = word == word.reverse

  test("all prefix flags and intervals") {
    val rng = new PyRandom(911)
    val words = PyItertools.wordsBelow("ab", 9) ++
      (0 until 30).map(_ => rng.word("ab", 120)) ++
      Vector("a" * 257, "ab" * 257, ("a" * 8 + "b") * 8 + "a" * 8)
    words.foreach { word =>
      Vector((0, word.length + 1), (0, word.length), (word.length / 2, word.length)).foreach { case (lower, upper) =>
        val vm = new FlagVM(word, lower, upper, Some(program))
        val expected = (upper - 1 to lower by -1).map(n => isPalindrome(word.take(n))).toVector
        assertEquals(vm.runFlags(), expected, (word.take(30), word.length, lower, upper))
      }
    }
  }

  test("state counts agree with the Python compiler") {
    val actual = Vector(4, 8).map { k =>
      val reduced = compileController(k, controller = k => flagController(k))
      s"$k ${reduced.code.size} ${reduced.constructionStates} ${unitMoves(reduced).code.size}"
    }.mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import compile_controller, unit_moves\nfrom gs_flag_heads import flag_controller\n" +
        "for k in (4, 8):\n  p = compile_controller(k, controller=flag_controller)\n" +
        "  print(k, len(p.code), p.construction_states, len(unit_moves(p).code))")
    intercept[IllegalArgumentException](new FlagVM("ab", 2, 1, Some(program)))
  }
}
