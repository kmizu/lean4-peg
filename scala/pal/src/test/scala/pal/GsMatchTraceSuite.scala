package pal

/** Byte-identity of `GsMatchTrace.trace` with `gs_match_trace.trace` (the
  * Python module has no test of its own), plus the reader-liveness register
  * count it depends on.
  */
class GsMatchTraceSuite extends munit.FunSuite {

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  test("match traces are identical to Python") {
    val program = GsMatchHeads.compileMatcher()
    val cases = Vector(("a", ""), ("a", "aab"), ("ab", "abab"), ("aba", "babab"), ("aaaaaaaab", "aaaaaaaabaaaaaaaab"),
      ("abaab", "abaababaab"))
    val actual = cases.map { case (prefix, text) => GsMatchTrace.trace(prefix, text, Some(program)) }.mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_match_trace import trace\nfrom gs_match_heads import compile_matcher\nprogram = compile_matcher()\n" +
        "cases = [('a', ''), ('a', 'aab'), ('ab', 'abab'), ('aba', 'babab'), ('aaaaaaaab', 'aaaaaaaabaaaaaaaab'),\n" +
        "         ('abaab', 'abaababaab')]\n" +
        "for prefix, text in cases: print(trace(prefix, text, program))")
    intercept[IllegalArgumentException](GsMatchTrace.trace("", "ab", Some(program)))
    intercept[IllegalArgumentException](GsMatchTrace.trace("a", "abc", Some(program)))
  }

  test("head liveness registers agree with gs_head_liveness.py") {
    val matcher = GsMatchHeads.compileMatcher()
    val border = GsHeads.unitMoves(GsHeads.compileController())
    val flags = GsFlagHeads.compileFlags()
    val dual = GsDualFlags.compileDualFlags()
    def show(program: Program, names: Vector[String]): String = {
      val live = GsHeadLiveness.analyze(program, names)
      val readers = GsHeadLiveness.analyzeReaders(program)
      val colors = live.colors.map { case ((left, right), color) => s"$left-$right=$color" }.mkString(" ")
      val readerColors = readers.colors.map { case (head, color) => s"$head=$color" }.mkString(" ")
      s"${live.registers} ${live.before.map(_.size).sum} ${live.after.map(_.size).sum} $colors | " +
        s"${readers.registers} ${readers.before.map(_.size).sum} $readerColors"
    }
    val actual = Vector(show(border, GsHeads.HEADS), show(matcher, GsMatchHeads.MATCH_HEADS),
      show(flags, GsFlagHeads.FLAG_HEADS), show(dual, GsDualFlags.DUAL_HEADS)).mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_heads import compile_controller, unit_moves, HEADS\nfrom gs_match_heads import compile_matcher, MATCH_HEADS\n" +
        "from gs_flag_heads import compile_flags, FLAG_HEADS\nfrom gs_dual_flags import compile_dual_flags, DUAL_HEADS\n" +
        "from gs_head_liveness import analyze, analyze_readers\n" +
        "def show(program, names):\n" +
        "  live, readers = analyze(program, names), analyze_readers(program)\n" +
        "  colors = ' '.join(f'{l}-{r}={c}' for (l, r), c in live.colors.items())\n" +
        "  rc = ' '.join(f'{h}={c}' for h, c in readers.colors.items())\n" +
        "  print(live.registers, sum(map(len, live.before)), sum(map(len, live.after)), colors, '|',\n" +
        "        readers.registers, sum(map(len, readers.before)), rc)\n" +
        "show(unit_moves(compile_controller()), HEADS)\nshow(compile_matcher(), MATCH_HEADS)\n" +
        "show(compile_flags(), FLAG_HEADS)\nshow(compile_dual_flags(), DUAL_HEADS)")
    assertEquals(GsHeadLiveness.analyze(border).canonical("B", "A"), (Some(("A", "B")), -1))
    assertEquals(GsHeadLiveness.analyze(border).canonical("A", "A"), (None, 1))
  }
}
