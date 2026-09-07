package pal

/** fpp.py has no Python test module; its `__main__` output is the differential oracle. */
class FppSuite extends munit.FunSuite {

  test("__main__ output (reference check and random cursor analysis) matches Python") {
    PyDiff.assertSameAsPython(Fpp.mainText(), "fpp.py")
  }

  test("palindromic prefixes agree with brute force and with the FPP border definition") {
    for (n <- 0 to 10) {
      for (u <- Fpp.binaryWords(n)) {
        assertEquals(Fpp.palindromicPrefixes(u), Fpp.brute(u), u)
        assertEquals(Fpp.bordersReference(u).sorted, borders(u), u)
      }
    }
  }

  /** Proper borders of `u`, increasing. */
  def borders(u: String): Vector[Int] =
    (1 until u.length).filter(k => u.take(k) == u.takeRight(k)).toVector

  test("maximal suffixes and periodicity match Python on all binary words up to length 8") {
    val lines = for {
      n <- 0 to 8
      u <- Fpp.binaryWords(n)
    } yield {
      val (i1, p1) = Fpp.maximalSuffix(u, true)
      val (i2, p2) = Fpp.maximalSuffix(u, false)
      s"$u ($i1, $p1) ($i2, $p2) ${Fpp.periodIfPeriodic(u).map(_.toString).getOrElse("None")}"
    }
    PyDiff.assertSameAsPython(lines.mkString("", "\n", "\n"), "-c",
      "from itertools import product\nfrom fpp import maximal_suffix, period_if_periodic\n" +
        "for n in range(9):\n  for t in product('ab', repeat=n):\n    u = ''.join(t)\n" +
        "    print(u, maximal_suffix(u), maximal_suffix(u, False), period_if_periodic(u))")
  }

  test("borders_via_periods is the documented dead end: it fails on any nonempty input") {
    assertEquals(Fpp.bordersViaPeriods(""), Vector())
    intercept[NotImplementedError] {
      Fpp.bordersViaPeriods("abab")
    }
  }

  test("PythonRandom reproduces random.seed(5) draws") {
    val random = new Fpp.PythonRandom(5)
    val draws = (0 until 20).map(_ => random.randint(4, 200)) ++ (0 until 20).map(_ => random.randrange(3))
    PyDiff.assertSameAsPython(draws.mkString("", "\n", "\n"), "-c",
      "import random\nrandom.seed(5)\n" +
        "for _ in range(20): print(random.randint(4, 200))\nfor _ in range(20): print(random.randrange(3))")
  }
}
