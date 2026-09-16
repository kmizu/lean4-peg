package pal

import Stage2TmGalil.*
import Twoway.product

/** stage2_tm_galil.py has no Python test; drivers and demo are pinned against python3. */
class Stage2TmGalilSuite extends munit.FunSuite {

  test("run_online('abbabba') matches Python outputs and costs") {
    assertEquals(runOnline("abbabba"), (Vector(1, 0, 0, 1, 0, 0, 1), Vector(2, 5, 5, 2, 15, 2, 1)))
  }

  test("run_realtime('abbabba', 8) matches Python") {
    assertEquals(runRealtime("abbabba", 8), Vector(1, 0, 0, 1, 0, 0, 1))
  }

  test("online output is the truth for all binary strings up to length 9") {
    for (n <- 1 to 9; x <- product("ab", n)) {
      assertEquals(runOnline(x)._1, brute(x), x)
    }
  }

  test("the Tape keeps symbols and marks per cell") {
    val tape = new Tape[Char]
    assertEquals(tape.sym(3), None)
    tape.set(3, 'a')
    assertEquals(tape.sym(3), Some('a'))
    tape.marks(3) += "m"
    assertEquals(tape.marks(3).toSet, Set("m"))
    assertEquals(tape.cells.size, 4)
  }

  test("the online constraint is enforced") {
    val m = new Machine("ab")
    m.feed()
    assertEquals(m.readInput(1), 'a')
    intercept[AssertionError](m.readInput(2))
  }

  test("run_realtime agrees with python3 over budgets 4..12 on all strings up to length 8") {
    val budgets = Vector(4, 6, 8, 12)
    val got = (for (budget <- budgets; n <- 1 to 8; x <- product("ab", n))
      yield runRealtime(x, budget).mkString).mkString("\n") + "\n"
    PyDiff.assertSameAsPython(got, "-c",
      """from itertools import product
        |from stage2_tm_galil import run_realtime
        |for budget in (4, 6, 8, 12):
        |    for n in range(1, 9):
        |        for t in product('ab', repeat=n):
        |            print(''.join(map(str, run_realtime(''.join(t), budget))))
        |""".stripMargin)
  }

  test("__main__ demo is byte-identical to python3 stage2_tm_galil.py") {
    PyDiff.assertSameAsPython(demo(), "stage2_tm_galil.py")
  }
}
