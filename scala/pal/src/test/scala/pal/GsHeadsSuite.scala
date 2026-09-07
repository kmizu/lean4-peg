package pal

/** Port of `test_gs_heads.py`, plus fidelity checks of the compiled tables
  * against the Python compiler (state counts before and after reduction).
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

  test("the unreduced table is identical to Python's, row by row") {
    val raw = compileController(8, reduce = false)
    val rendered = raw.code.map(row => s"${render(row.event)} ${row.targets.mkString(",")}").mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(rendered, "-c",
      "from gs_heads import compile_controller\n" +
        "def show(e):\n" +
        "  if e[0] == 'move': return 'move ' + ' '.join(f'{h}{d:+d}' for h, d in e[1])\n" +
        "  if e[0] == 'flag': return 'flag ' + str(e[1]).lower()\n" +
        "  return ' '.join(map(str, e))\n" +
        "for event, targets in compile_controller(8, reduce=False).code:\n" +
        "  print(show(event), ','.join(map(str, targets)))")
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
