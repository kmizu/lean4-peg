package pal

import Stage3bDesignCheck.*
import Twoway.product

/** stage3b_design_check.py has no Python test; drivers and demo are pinned against python3. */
class Stage3bDesignCheckSuite extends munit.FunSuite {

  test("run_online(('abba'*5)) matches Python outputs and costs") {
    assertEquals(runOnline("abba" * 5), (
      Vector(1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1),
      Vector(2, 6, 33, 2, 73, 2, 2, 2, 197, 2, 2, 2, 268, 2, 2, 2, 325, 2, 2, 13)))
  }

  test("online output is the truth (and the design assertions hold) up to length 9") {
    for (n <- 1 to 9; x <- product("ab", n)) {
      assertEquals(runOnline(x)._1, brute(x), x)
    }
  }

  test("the design assertions hold on long periodic inputs") {
    for (x <- Vector("ab" * 100, "a" * 200, "aab" * 60, "abba" * 50, "aabab" * 40)) {
      assertEquals(runOnline(x)._1, brute(x), x.take(8))
    }
  }

  test("run_realtime agrees with python3 at budget 64 on all strings up to length 8") {
    val got = (for (n <- 1 to 8; x <- product("ab", n)) yield runRealtime(x, 64).mkString).mkString("\n") + "\n"
    PyDiff.assertSameAsPython(got, "-c",
      """from itertools import product
        |from stage3b_design_check import run_realtime
        |for n in range(1, 9):
        |    for t in product('ab', repeat=n):
        |        print(''.join(map(str, run_realtime(''.join(t), 64))))
        |""".stripMargin)
  }

  test("__main__ demo is byte-identical to python3 stage3b_design_check.py") {
    PyDiff.assertSameAsPython(demo(), "stage3b_design_check.py")
  }
}
