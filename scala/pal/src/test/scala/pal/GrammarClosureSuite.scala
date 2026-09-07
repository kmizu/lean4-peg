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
    assertEquals(report.defined, Set("S", "A", "U"))
    assertEquals(report.referenced, Set("A", "D"))
    assertEquals(report.missing, Set("D"))
    assertEquals(report.unusedDefs, Set("U"))
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
}
