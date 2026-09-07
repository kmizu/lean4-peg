package pal

/** analysis/grammar_closure.py has no Python test; its stdout on a small grammar is pinned. */
class GrammarClosureSuite extends munit.FunSuite {

  test("generated/midpoint.peg: printed summary is byte-identical to Python") {
    val report = GrammarClosure.analyzeFile(PyDiff.pyDir.resolve("generated/midpoint.peg"))
    assertEquals(report.rules, 9949)
    PyDiff.assertSameAsPython(report.text, "analysis/grammar_closure.py", "generated/midpoint.peg")
  }

  test("literals and classes are blanked; missing and unused rules are reported") {
    val report = GrammarClosure.analyze(Vector(
      "S = A \"B\" [C] D;",
      "A = \"x\";",
      "U = A;",
      "not a rule").iterator)
    assertEquals(report.rules, 3)
    assertEquals(report.defined, 3)
    assertEquals(report.referenced, 2)
    assertEquals(report.missing, Vector("D"))
    assertEquals(report.unused, Vector("U"))
    assertEquals(report.text,
      "rules=3 defined=3 referenced=2 MISSING=1 unused_defs=1\nmissing sample: [b'D']\n")
  }

  test("the small grammar summary matches the Python script on the same file") {
    val file = java.nio.file.Files.createTempFile("closure", ".peg")
    try {
      java.nio.file.Files.writeString(file, "S = A \"B\" [C] D;\nA = \"x\";\nU = A;\nnot a rule\n")
      val report = GrammarClosure.analyzeFile(file)
      PyDiff.assertSameAsPython(report.text, "analysis/grammar_closure.py", file.toString)
    } finally {
      java.nio.file.Files.deleteIfExists(file)
      ()
    }
  }

  test("a 20,000-rule synthetic grammar, streamed from disk, matches the Python script") {
    val file = java.nio.file.Files.createTempFile("closure", ".peg")
    try {
      java.nio.file.Files.writeString(file, SyntheticGrammar(20000))
      val report = GrammarClosure.analyzeFile(file)
      assertEquals((report.rules, report.defined, report.referenced, report.missing.size, report.unused.size),
        (20001, 20001, 20000, 0, 0))
      PyDiff.assertSameAsPython(report.text, "analysis/grammar_closure.py", file.toString)
    } finally {
      java.nio.file.Files.deleteIfExists(file)
      ()
    }
  }
}
