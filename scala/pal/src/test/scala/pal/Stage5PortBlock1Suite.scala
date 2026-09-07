package pal

import Scavm.{Label, Stats}
import Stage5PortBlock1.{Mode, allStrings, brute, run}

/** `stage5_port_block1.py` の観測可能な振る舞いを固定する。 */
class Stage5PortBlock1Suite extends munit.FunSuite {

  private def pyList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")

  test("main prints exactly what python3 stage5_port_block1.py prints") {
    PyDiff.assertSameAsPython(TestUtil.captureStdout(Stage5PortBlock1.main(Array.empty)), "stage5_port_block1.py")
  }

  test("online (unbounded budget) agrees with brute force on every string over {a,b,c} up to length 7") {
    for (n <- 1 to 7; x <- allStrings("abc", n)) {
      assertEquals(run(x)._1, brute(x), x)
    }
  }

  test("worst-case statistics over {a,b}^<=10 as reported by python") {
    var worst: Option[Stats] = None
    for (n <- 1 to 10; x <- allStrings("ab", n)) {
      val st = run(x)._2
      if (worst.forall(w => st.radius > w.radius)) {
        worst = Some(st)
      }
    }
    assertEquals(worst, Some(Stats(steps = 10, radius = 47, fields = 139, labels = 10)))
  }

  test("bounded budgets: outputs and statistics match python for a sample of (x, budget)") {
    val samples = Vector("a", "ab", "aba", "abba", "abaab", "abcba", "aabaa", "abaaba", "babbab", "aabbaabb", "abababab", "abbaabba", "aaaaaaaaaa")
    val budgets = Vector(None, Some(1), Some(2), Some(3), Some(5), Some(8))
    val script =
      """from stage5_port_block1 import run
        |for x in ['a', 'ab', 'aba', 'abba', 'abaab', 'abcba', 'aabaa', 'abaaba', 'babbab', 'aabbaabb', 'abababab', 'abbaabba', 'aaaaaaaaaa']:
        |    for bud in [None, 1, 2, 3, 5, 8]:
        |        outs, st = run(x, bud)
        |        print(x, bud, outs, st)
        |""".stripMargin
    val sb = new StringBuilder
    for (x <- samples; budget <- budgets) {
      val (outs, st) = run(x, budget)
      sb.append(s"$x ${budget.fold("None")(_.toString)} ${pyList(outs)} ${st.pythonRepr}\n")
    }
    PyDiff.assertSameAsPython(sb.toString, "-c", script)
  }

  test("a budget of 1 unit per step lags: outputs are a delayed/partial view but never wrong when caught up") {
    val (outs, _) = run("abba", Some(1))
    assertEquals(outs.length, 4)
    val (unbounded, _) = run("abba")
    assertEquals(unbounded, Vector(1, 0, 0, 1))
    assert(outs.zip(unbounded).forall { case (o, u) => o == 0 || o == u })
  }

  test("brute and allStrings") {
    assertEquals(brute("abba"), Vector(1, 0, 0, 1))
    assertEquals(brute(""), Vector.empty[Int])
    assertEquals(allStrings("ab", 2), Vector("aa", "ab", "ba", "bb"))
    assertEquals(allStrings("ab", 0), Vector(""))
    assertEquals(allStrings("ab", 10).length, 1024)
  }

  test("Mode round-trips through its label; unknown labels are rejected") {
    for (m <- Mode.values) {
      assertEquals(Mode.fromLabel(Label.Str(m.label)), m)
    }
    assertEquals(Mode.values.map(_.label).toVector, Vector("match", "kmp", "chain"))
    intercept[IllegalArgumentException](Mode.fromLabel(Label.Str("idle")))
  }

  test("the empty input produces no output and an empty VM") {
    assertEquals(run(""), (Vector.empty[Int], Stats(0, 0, 0, 0)))
  }
}
