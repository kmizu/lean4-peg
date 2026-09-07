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
}
