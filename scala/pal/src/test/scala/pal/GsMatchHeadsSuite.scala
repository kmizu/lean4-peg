package pal

/** Port of `test_gs_match_heads.py`, plus a state-count check against Python. */
class GsMatchHeadsSuite extends munit.FunSuite {
  import GsMatchHeads.{MATCH_TESTS, compileMatcher, matcherController}
  import GsHeads.{compileController, unitMoves}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  lazy val program: Program = compileMatcher()

  def compare(pattern: String, text: String): Unit = {
    val vm = new StreamingMatcher(pattern, Some(program))
    vm.drain()
    text.zipWithIndex.foreach { case (char, index) =>
      val end = index + 1
      vm.append(char)
      val before = vm.outputs.size
      vm.drain()
      val expected = end >= pattern.length && text.substring(end - pattern.length, end) == pattern
      assertEquals(vm.outputs.drop(before), if (expected) Vector(end) else Vector.empty[Int], (pattern, end))
    }
  }

  test("incremental matches and overlap restart") {
    val rng = new PyRandom(910)
    val patterns = (1 until 7).flatMap(PyItertools.words("ab", _))
    patterns.foreach { pattern =>
      val text = rng.word("ab", 60)
      compare(pattern, text)
    }
  }

  test("nonempty short prefix and periodic reuse") {
    val patterns = Vector("a" * 8 + "b", "a" * 8 + "b" + "a" * 8 + "c", ("a" * 8 + "b") * 8 + "c")
    patterns.foreach { pattern =>
      compare(pattern, pattern * 20)
      compare(pattern, "b" * 200 + pattern * 7)
    }
  }

  test("initial short prefix offset waits for real input") {
    val pattern = ("a" * 8 + "b") * 8 + "b"
    val vm = new StreamingMatcher(pattern, Some(program))
    vm.drain()
    assert(vm.positions("Cut") > 0)
    assert(vm.waiting)
    assertEquals(vm.positions("B"), pattern.length)
    compare(pattern, pattern * 2)
  }

  test("state counts agree with the Python compiler") {
    val actual = Vector(4, 8).map { k =>
      val reduced = compileController(k, controller = k => matcherController(k), tests = MATCH_TESTS)
      s"$k ${reduced.code.size} ${reduced.constructionStates} ${unitMoves(reduced).code.size}"
    }.mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import compile_controller, unit_moves\nfrom gs_match_heads import matcher_controller, MATCH_TESTS\n" +
        "for k in (4, 8):\n  p = compile_controller(k, controller=matcher_controller, tests=MATCH_TESTS)\n" +
        "  print(k, len(p.code), p.construction_states, len(unit_moves(p).code))")
    intercept[IllegalArgumentException](new StreamingMatcher("", Some(program)))
  }
}
