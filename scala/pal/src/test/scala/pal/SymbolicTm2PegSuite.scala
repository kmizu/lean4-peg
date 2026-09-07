package pal

import SymbolicTm2Peg.{Operation, SymbolicTM, Transition, fromDense}
import Tm2Peg.{Move, tmMarkedPalindrome}

/** Sparse focus guards must compile without a product of tape alphabets.
  * （Python 版: `test_symbolic_tm2peg.py`、全ケース移植 + 差分テスト）
  */
class SymbolicTm2PegSuite extends munit.FunSuite {

  test("backspace uses the grammar parser's unicode escape") {
    val machine = new SymbolicTM(0, Vector("q"), "q", Set("q"),
      Vector(Transition("q", "\b", Map.empty, "q", Map.empty)), "\b")
    assert(machine.compile().contains("\"\\u0008\""))
    assert(!machine.compile().contains("\"\\b\""))
  }

  test("supplementary and surrogate input are rejected") {
    for (char <- Vector("😀", "\ud800", "\udfff")) {
      val error = intercept[IllegalArgumentException] {
        new SymbolicTM(0, Vector("q"), "q", Set("q"), Vector.empty, char)
      }
      assert(error.getMessage.contains("BMP"), error.getMessage)
    }
  }

  test("sparse machine matches dense reference") {
    val dense = tmMarkedPalindrome()
    val sparse = fromDense(dense, extraTapes = 18)
    for (n <- 0 until 8; word <- Twoway.product("ab#", n)) {
      assertEquals(sparse.run(word), dense.run(word), word)
    }
  }

  test("compilation size does not expand focus vectors") {
    val sparse = fromDense(tmMarkedPalindrome(), extraTapes = 18)
    val source = sparse.compile()
    assert(source.length < 150000, source.length)
    assert(source.contains("D_0 ="))
    assert(!source.contains("macro"))
  }

  test("overlapping guards are rejected") {
    val error = intercept[IllegalArgumentException] {
      new SymbolicTM(1, Vector("q"), "q", Set("q"), Vector(
        Transition("q", "a", Map.empty, "q", Map.empty),
        Transition("q", "a", Map(0 -> "_"), "q", Map.empty)), "ab")
    }
    assert(error.getMessage.contains("overlapping"), error.getMessage)
  }

  test("unspecified write preserves symbol during move") {
    val machine = new SymbolicTM(1, Vector("p", "q", "r", "s", "yes"), "p", Set("yes"), Vector(
      Transition("p", "a", Map.empty, "q", Map(0 -> Operation(Some("x"), Move.S))),
      Transition("q", "a", Map.empty, "r", Map(0 -> Operation(None, Move.R))),
      Transition("r", "a", Map.empty, "s", Map(0 -> Operation(None, Move.L))),
      Transition("s", "a", Map(0 -> "x"), "yes", Map.empty)), "a")
    assert(machine.run("aaaa"))
    assert(!machine.run("aaa"))
    assert(machine.compile().contains("Lsym_0"))
  }

  // ---- beyond the Python tests: byte-identity with the Python compiler

  test("from_dense(tm_marked_palindrome, 18).compile() is byte-identical to Python") {
    val source = fromDense(tmMarkedPalindrome(), extraTapes = 18).compile()
    PyDiff.assertSameAsPython(source, "-c",
      "from tm2peg import tm_marked_palindrome; import symbolic_tm2peg as s; import sys; " +
        "sys.stdout.write(s.from_dense(tm_marked_palindrome(), extra_tapes=18).compile())")
  }

  test("the small preserving-move machine compiles byte-identically to Python") {
    val machine = new SymbolicTM(1, Vector("p", "q", "r", "s", "yes"), "p", Set("yes"), Vector(
      Transition("p", "a", Map.empty, "q", Map(0 -> Operation(Some("x"), Move.S))),
      Transition("q", "a", Map.empty, "r", Map(0 -> Operation(None, Move.R))),
      Transition("r", "a", Map.empty, "s", Map(0 -> Operation(None, Move.L))),
      Transition("s", "a", Map(0 -> "x"), "yes", Map.empty)), "a")
    PyDiff.assertSameAsPython(machine.compile(), "-c",
      """import symbolic_tm2peg as s, sys
        |m = s.SymbolicTM(1, ["p", "q", "r", "s", "yes"], "p", {"yes"}, [
        |  s.Transition("p", "a", {}, "q", {0: ("x", "S")}),
        |  s.Transition("q", "a", {}, "r", {0: (None, "R")}),
        |  s.Transition("r", "a", {}, "s", {0: (None, "L")}),
        |  s.Transition("s", "a", {0: "x"}, "yes", {})], "a")
        |sys.stdout.write(m.compile())
        |""".stripMargin)
  }

  test("tape alphabet is sorted by code point") {
    assertEquals(fromDense(tmMarkedPalindrome(), 2).tapeAlphabet, Vector("A", "B", "_", "a", "b"))
  }

  test("validation errors carry the Python messages") {
    def failing(body: => SymbolicTM): String = intercept[IllegalArgumentException](body).getMessage
    assertEquals(failing(new SymbolicTM(-1, Vector("q"), "q", Set("q"), Vector.empty)), "invalid tapes or duplicate states")
    assertEquals(failing(new SymbolicTM(0, Vector("q", "q"), "q", Set("q"), Vector.empty)), "invalid tapes or duplicate states")
    assertEquals(failing(new SymbolicTM(0, Vector("q"), "z", Set("q"), Vector.empty)), "unknown initial/accepting state")
    assertEquals(failing(new SymbolicTM(0, Vector("q"), "q", Set("z"), Vector.empty)), "unknown initial/accepting state")
    assertEquals(failing(new SymbolicTM(0, Vector("q"), "q", Set("q"), Vector.empty, "")), "nonempty BMP scalar character alphabet required")
    assertEquals(failing(new SymbolicTM(0, Vector("q"), "q", Set("q"),
      Vector(Transition("q", "a", Map.empty, "z", Map.empty)))), "unknown transition state")
    assertEquals(failing(new SymbolicTM(0, Vector("q"), "q", Set("q"),
      Vector(Transition("q", "c", Map.empty, "q", Map.empty)))), "unknown input character")
    assertEquals(failing(new SymbolicTM(1, Vector("q"), "q", Set("q"),
      Vector(Transition("q", "a", Map(1 -> "_"), "q", Map.empty)))), "unknown tape")
  }
}
