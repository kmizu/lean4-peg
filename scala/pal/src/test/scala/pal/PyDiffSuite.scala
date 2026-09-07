package pal

class PyDiffSuite extends munit.FunSuite {

  test("python() runs in docs/palindromes-in-peg and returns stdout") {
    assertEquals(PyDiff.python("-c", "print('x')"), "x\n")
    assert(PyDiff.pyDir.resolve("symbolic_sca2peg.py").toFile.exists())
  }

  test("assertSameAsPython reports the first differing line") {
    val message = PyDiff.firstDifference("a\nb\n", "a\nc\n", "t")
    assert(message.contains("line 2"), message)
  }

  test("large stderr is drained without contaminating successful stdout") {
    assertEquals(PyDiff.python("-c", "import sys; sys.stderr.write('x' * 262144); print('ok')"), "ok\n")
  }

  test("large failing stderr is retained through its final diagnostic") {
    val error = intercept[IllegalStateException] {
      PyDiff.python("-c", "import sys; sys.stderr.write('x' * 262144 + '\\nFINAL_DIAGNOSTIC\\n'); sys.exit(7)")
    }
    assert(error.getMessage.contains("exited 7"))
    assert(error.getMessage.endsWith("FINAL_DIAGNOSTIC\n"))
  }
}
