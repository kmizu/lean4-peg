package pal

import Twoway.{Counter, bruteBorders, product}
import TwowayBorder.longestBorderTwoway

/** twoway_border.py has no Python test; its `__main__` demo is pinned byte-for-byte. */
class TwowayBorderSuite extends munit.FunSuite {

  test("longest_border_twoway on short strings") {
    assertEquals(longestBorderTwoway(""), 0)
    assertEquals(longestBorderTwoway("a"), 0)
    assertEquals(longestBorderTwoway("aa"), 1)
    assertEquals(longestBorderTwoway("abab"), 2)
    assertEquals(longestBorderTwoway("aaba"), 0) // documented mismatch: brute says 1
    assertEquals(bruteBorders("aaba"), Vector(1))
  }

  test("comparison counter is used") {
    val counter = new Counter
    longestBorderTwoway("abababab", Some(counter))
    assert(counter.value > 0)
  }

  test("agrees with Python on every binary string up to length 8") {
    val script =
      """from itertools import product
        |from twoway_border import longest_border_twoway
        |for n in range(0, 9):
        |    for t in product('ab', repeat=n):
        |        print(longest_border_twoway(''.join(t)))
        |""".stripMargin
    val got = (0 to 8).flatMap(n => product("ab", n)).map(w => longestBorderTwoway(w).toString).mkString("\n") + "\n"
    PyDiff.assertSameAsPython(got, "-c", script)
  }

  test("__main__ demo is byte-identical to python3 twoway_border.py") {
    PyDiff.assertSameAsPython(TwowayBorder.demo(), "twoway_border.py")
  }
}
