package pal

/** Byte-identity of `GsFlagTrace.trace` with `gs_flag_trace.trace` (the Python
  * module has no test of its own).
  */
class GsFlagTraceSuite extends munit.FunSuite {

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  test("flag traces are identical to Python for both workers") {
    val flags = GsFlagHeads.compileFlags()
    val dual = GsDualFlags.compileDualFlags()
    val cases = Vector(("", 0), ("a", 0), ("a", 1), ("aa", 0), ("aba", 1), ("abab", 0), ("abba", 2),
      ("aaaaaaaab", 3), ("abaabaaba", 0), ("ab" * 9 + "a", 4))
    val actual = cases.flatMap { case (word, lower) =>
      Vector(GsFlagTrace.trace(word, lower, Some(flags)), GsFlagTrace.trace(word, lower, Some(dual), dual = true))
    }.mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_flag_trace import trace\nfrom gs_flag_heads import compile_flags\nfrom gs_dual_flags import compile_dual_flags\n" +
        "flags, dual = compile_flags(), compile_dual_flags()\n" +
        "cases = [('', 0), ('a', 0), ('a', 1), ('aa', 0), ('aba', 1), ('abab', 0), ('abba', 2),\n" +
        "         ('aaaaaaaab', 3), ('abaabaaba', 0), ('ab' * 9 + 'a', 4)]\n" +
        "for word, lower in cases:\n  print(trace(word, lower, flags))\n  print(trace(word, lower, dual, True))")
    intercept[IllegalArgumentException](GsFlagTrace.trace("abc", 0, Some(flags)))
    intercept[IllegalArgumentException](GsFlagTrace.trace("ab", 3, Some(flags)))
  }
}
