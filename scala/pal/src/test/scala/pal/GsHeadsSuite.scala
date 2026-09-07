package pal

/** Port of `test_gs_heads.py`, plus fidelity checks of the compiled tables
  * against the Python compiler: state counts, and row-by-row identity of the
  * unreduced and the reduced unit tables of all four controllers (border,
  * matcher, flag, dual).
  */
class GsHeadsSuite extends munit.FunSuite {
  import Event.*
  import GsHeads.{compileController, unitMoves}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  lazy val program: Program = compileController()
  lazy val unit: Program = unitMoves(program)

  test("complete finite table and unit lowering") {
    assert(program.code.size < 1200)
    unit.code.foreach { case Row(event, targets) =>
      targets.foreach(target => assert(0 <= target && target < unit.code.size))
      event match {
        case Move(moves) =>
          assertEquals(moves.size, 1)
          assert(moves(0).delta == -1 || moves(0).delta == 1)
        case _ => ()
      }
    }
  }

  test("all borders exhaustive and periodic") {
    val rng = new PyRandom(909)
    val samples = PyItertools.wordsBelow("ab", 10) ++
      (0 until 35).map(_ => rng.word("ab#", rng.randrange(1, 500))) ++
      Vector("a" * 1024, "ab" * 513, ("a" * 8 + "b") * 37, ("a" * 8 + "b" + "a" * 8 + "c") * 21)
    samples.foreach { word =>
      val expected = GsOverlap.iterBorders(word.toIndexedSeq, k = 8)
      val clue = (word.take(50), word.length)
      assertEquals(new HeadVM(word.toIndexedSeq, program).run(), expected, clue)
      assertEquals(new HeadVM(word.toIndexedSeq, unit).run(), expected, clue)
    }
  }

  /** `(reduced states, construction states, unit states)` for each k. */
  private def shape(k: Int): String = {
    val reduced = compileController(k)
    s"$k ${reduced.code.size} ${reduced.constructionStates} ${unitMoves(reduced).code.size}"
  }

  test("state counts agree with the Python compiler for k = 4, 5, 6, 8") {
    val actual = Vector(4, 5, 6, 8).map(shape).mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import compile_controller, unit_moves\n" +
        "for k in (4, 5, 6, 8):\n" +
        "  p = compile_controller(k)\n" +
        "  print(k, len(p.code), p.construction_states, len(unit_moves(p).code))")
  }

  test("k < 4 is rejected on the first activation, not at construction, as in Python") {
    val controller = GsHeads.borderController(3)
    intercept[IllegalArgumentException](controller.send(None))
    intercept[IllegalArgumentException](compileController(3))
    assertEquals(GsHeads.borderController(4).send(None), Yielded(copy("End", "OriginalEnd")))
  }

  /** The Python preamble shared by the row-identity tests: the four controllers
    * and a `dump` printing one table as `render` does.
    */
  private val preamble: String =
    "from gs_heads import compile_controller, unit_moves\n" +
      "from gs_match_heads import matcher_controller, compile_matcher, MATCH_TESTS\n" +
      "from gs_flag_heads import flag_controller, compile_flags\n" +
      "from gs_dual_flags import dual_flag_controller, compile_dual_flags\n" +
      "def show(e):\n" +
      "  if e[0] == 'move': return 'move ' + ' '.join(f'{h}{d:+d}' for h, d in e[1])\n" +
      "  if e[0] == 'flag': return 'flag ' + str(e[1]).lower()\n" +
      "  return ' '.join(map(str, e))\n" +
      "def dump(name, p):\n" +
      "  print('==', name, len(p.code), p.start, p.k, p.construction_states)\n" +
      "  for event, targets in p.code: print(show(event), ','.join(map(str, targets)))\n"

  /** `dump(name, program)`: a header line and one line per row. */
  private def dump(name: String, program: Program): String = {
    val header = s"== $name ${program.code.size} ${program.start} ${program.k} ${program.constructionStates}\n"
    header + program.code.map(row => s"${render(row.event)} ${row.targets.mkString(",")}\n").mkString
  }

  test("the unreduced tables of all four controllers are identical to Python's, row by row") {
    val actual = dump("border", compileController(8, reduce = false)) +
      dump("matcher", compileController(8, reduce = false, controller = k => GsMatchHeads.matcherController(k),
        tests = GsMatchHeads.MATCH_TESTS)) +
      dump("flag", compileController(8, reduce = false, controller = k => GsFlagHeads.flagController(k))) +
      dump("dual", compileController(8, reduce = false, controller = k => GsDualFlags.dualFlagController(k)))
    PyDiff.assertSameAsPython(actual, "-c", preamble +
      "dump('border', compile_controller(8, reduce=False))\n" +
      "dump('matcher', compile_controller(8, reduce=False, controller=matcher_controller, tests=MATCH_TESTS))\n" +
      "dump('flag', compile_controller(8, reduce=False, controller=flag_controller))\n" +
      "dump('dual', compile_controller(8, reduce=False, controller=dual_flag_controller))\n")
  }

  test("the reduced and unit tables of all four controllers are identical to Python's, row by row") {
    val actual = dump("border", program) + dump("border-unit", unit) +
      dump("matcher", GsMatchHeads.compileMatcher(unit = false)) + dump("matcher-unit", GsMatchHeads.compileMatcher()) +
      dump("flag-unit", GsFlagHeads.compileFlags()) +
      dump("dual", GsDualFlags.compileDualFlags(unit = false)) + dump("dual-unit", GsDualFlags.compileDualFlags())
    PyDiff.assertSameAsPython(actual, "-c", preamble +
      "p = compile_controller()\ndump('border', p)\ndump('border-unit', unit_moves(p))\n" +
      "dump('matcher', compile_matcher(unit=False))\ndump('matcher-unit', compile_matcher())\n" +
      "dump('flag-unit', compile_flags())\n" +
      "dump('dual', compile_dual_flags(unit=False))\ndump('dual-unit', compile_dual_flags())\n")
  }

  /** The Python `show` rendering above. */
  def render(event: Event): String = {
    event match {
      case Move(moves) => "move " + moves.map(m => s"${m.head}${if (m.delta >= 0) "+" else ""}${m.delta}").mkString(" ")
      case Copy(target, source) => s"copy $target $source"
      case Equal(left, right) => s"equal $left $right"
      case Less(left, right) => s"less $left $right"
      case Symbols(left, right) => s"symbols $left $right"
      case Border(head) => s"border $head"
      case Flag(value) => s"flag $value"
      case Available(head) => s"available $head"
      case AssertEqual(left, right) => s"assert_equal $left $right"
      case Match(head) => s"match $head"
      case Halt => "halt"
    }
  }
}
