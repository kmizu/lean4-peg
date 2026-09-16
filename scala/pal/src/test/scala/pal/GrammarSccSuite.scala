package pal

import java.nio.file.Files

/** analysis/grammar_scc.py has no Python test; its stdout on a small grammar is pinned.
  * The elapsed-seconds suffix of the progress lines is normalised on both sides.
  */
class GrammarSccSuite extends munit.FunSuite {

  private val elapsed = " -?\\d+s$".r // negative when the wall clock is adjusted mid-run

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

  private def withGrammar(text: String)(body: java.nio.file.Path => Unit): Unit = {
    val file = Files.createTempFile("scc", ".peg")
    try {
      Files.writeString(file, text)
      body(file)
    } finally {
      Files.deleteIfExists(file)
      ()
    }
  }

  test("a 20,000-rule synthetic grammar, streamed from disk, matches the Python script") {
    withGrammar(SyntheticGrammar(20000)) { file =>
      val got = GrammarScc.run(file, () => 0.0)
      val expected = PyDiff.python("analysis/grammar_scc.py", file.toString)
      assertEquals(normalise(got), normalise(expected))
      assert(got.contains("nontrivial (size>1): 1, largest: 20000"), got)
    }
  }

  test("a 30,000-element sequence is evaluated like Python's recursive ev/walk") {
    withGrammar("S = " + Vector.fill(30000)("\"a\"").mkString(" ") + ";\nT = S* !.;\n") { file =>
      val got = GrammarScc.run(file, () => 0.0)
      val expected = PyDiff.python("analysis/grammar_scc.py", file.toString)
      assertEquals(normalise(got), normalise(expected))
    }
  }

  test("a 300,000-element sequence needs no recursion at all (Python's limit is 100,000)") {
    withGrammar("S = " + Vector.fill(300000)("\"a\"").mkString(" ") + ";\nT = S* !.;\n") { file =>
      assertEquals(GrammarScc.run(file, () => 0.0),
        "rules 2 0s\n" +
          "bytecode ints 600005 0s\n" +
          "reverse edges 1 0s\n" +
          "worklist gfp: evals 2, flips 1, consuming rules 1 0s\n" +
          "edges 1, guarded by consumption 0 0s\n" +
          "reachable from S: 1 rules; SCCs: 1, nontrivial (size>1): 0, largest: 1\n" +
          "edges inside SCCs: consuming-guarded 0, unguarded 0 0s\n" +
          "sample rules of the largest SCC: ['S']\n")
    }
  }
}

/** The synthetic grammar of the scaling measurement: ~16 bytecode ints per rule (as the
  * real PAL grammar), every rule reachable from S in one big SCC, guarded and unguarded
  * edges, literals, classes, predicates and suffixes.
  */
object SyntheticGrammar {
  def apply(n: Int): String = {
    val sb = new StringBuilder("S = R_0 (\"a\" / \"b\")* !.;\n")
    for (i <- 0 until n) {
      val j = (i + 1) % n
      val k = (i * 7 + 3) % n
      val l = (i * 13 + 5) % n
      val body = i % 5 match {
        case 0 => s"&. R_$j / \"a\" R_$k / !R_$l \"b\""
        case 1 => s"(\"a\" / \"b\") R_$j / &(R_$k \"a\") R_$l?"
        case 2 => s"!\"c\" R_$j* \"a\" / [ab]+ R_$k"
        case 3 => s"R_$j R_$k / \"\""
        case _ => s"&(!.) / \"b\" R_$j / R_$l &\"a\""
      }
      sb.append(s"R_$i = $body;\n")
    }
    sb.toString
  }
}
