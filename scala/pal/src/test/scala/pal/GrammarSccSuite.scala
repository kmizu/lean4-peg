package pal

import java.nio.file.Files

/** analysis/grammar_scc.py has no Python test; its stdout on a small grammar is pinned.
  * The elapsed-seconds suffix of the progress lines is normalised on both sides.
  */
class GrammarSccSuite extends munit.FunSuite {

  private val elapsed = " \\d+s$".r

  private def normalise(text: String): String = {
    text.linesIterator.map(line => elapsed.replaceAllIn(line, " Ts")).mkString("", "\n", "\n")
  }

  test("generated/midpoint.peg: printed analysis is identical to Python (modulo timings)") {
    val got = GrammarScc.run(PyDiff.pyDir.resolve("generated/midpoint.peg"))
    val expected = PyDiff.python("analysis/grammar_scc.py", "generated/midpoint.peg")
    assertEquals(normalise(got), normalise(expected))
  }

  test("generated/midpoint.peg: pinned figures with a frozen clock") {
    val got = GrammarScc.run(PyDiff.pyDir.resolve("generated/midpoint.peg"), () => 0.0)
    assertEquals(got,
      "rules 9949 0s\n" +
        "bytecode ints 64657 0s\n" +
        "reverse edges 23658 0s\n" +
        "worklist gfp: evals 19639, flips 9895, consuming rules 54 0s\n" +
        "edges 23658, guarded by consumption 203 0s\n" +
        "reachable from S: 9940 rules; SCCs: 401, nontrivial (size>1): 4, largest: 9275\n" +
        "edges inside SCCs: consuming-guarded 198, unguarded 21808 0s\n" +
        "sample rules of the largest SCC: ['B_0', 'B_1', 'B_2', 'B_3', 'B_4', 'B_5']\n")
  }

  test("a tiny grammar with an unguarded cycle, against the Python script") {
    val grammar =
      "S = A / \"x\" S;\n" +
        "A = B* \"a\" / &C D;\n" +
        "B = \"b\" / !\"c\" A;\n" +
        "C = [cd]+ / \"\";\n" +
        "D = (C / A)? \"d\";\n"
    val file = Files.createTempFile("scc", ".peg")
    try {
      Files.writeString(file, grammar)
      val got = GrammarScc.run(file, () => 0.0)
      val expected = PyDiff.python("analysis/grammar_scc.py", file.toString)
      assertEquals(normalise(got), normalise(expected))
      assert(got.contains("reachable from S: 5 rules"), got)
    } finally {
      Files.deleteIfExists(file)
      ()
    }
  }

  test("a grammar without a start rule S is rejected") {
    val file = Files.createTempFile("scc", ".peg")
    try {
      Files.writeString(file, "T = \"x\";\n")
      intercept[NoSuchElementException](GrammarScc.run(file, () => 0.0))
    } finally {
      Files.deleteIfExists(file)
      ()
    }
  }

  test("timings use Python's %.0f rounding") {
    var calls = 0
    val clock = () => { calls += 1; if (calls == 1) 0.0 else 2.5 }
    val file = Files.createTempFile("scc", ".peg")
    try {
      Files.writeString(file, "S = \"x\";\n")
      val got = GrammarScc.run(file, clock)
      assert(got.startsWith("rules 1 2s\n"), got)
    } finally {
      Files.deleteIfExists(file)
      ()
    }
  }

}
