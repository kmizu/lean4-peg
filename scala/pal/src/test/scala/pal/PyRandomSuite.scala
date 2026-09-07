package pal

/** `PyRandom` が CPython の `random` と同じ系列を出すことを python3 と突き合わせる。 */
class PyRandomSuite extends munit.FunSuite {

  private val seeds = Vector(0L, 1L, 2L, 11L, (1L << 40) + 5L, 4294967295L, 4294967296L)

  private val script =
    """import random
      |for seed in [0, 1, 2, 11, 2**40 + 5, 2**32 - 1, 2**32]:
      |    random.seed(seed)
      |    print(seed, [random.random() for _ in range(5)])
      |    print(seed, [random.randint(0, 3) for _ in range(8)])
      |    print(seed, [random.choice('pp o') for _ in range(8)])
      |    print(seed, [random.getrandbits(k) for k in (1, 7, 32, 33, 64)])
      |    print(seed, [random.randint(2, 14) for _ in range(6)], random.choice([0, 0, 1, 2]))
      |""".stripMargin

  private def pyList[A](xs: Seq[A]): String = xs.mkString("[", ", ", "]")

  /** Python の `repr(float)`: 1e-4 以上は指数表記にならない（Java は 1e-3 未満で E 表記）。 */
  private def pyFloat(d: Double): String = new java.math.BigDecimal(d.toString).toPlainString

  private def scalaOutput: String = {
    val sb = new StringBuilder
    for (seed <- seeds) {
      val r = new PyRandom(seed)
      sb.append(s"$seed ${pyList((0 until 5).map(_ => pyFloat(r.random())))}\n")
      sb.append(s"$seed ${pyList((0 until 8).map(_ => r.randint(0, 3)))}\n")
      sb.append(s"$seed ${pyList((0 until 8).map(_ => "'" + r.choice("pp o") + "'"))}\n")
      // getrandbits(64) は Long の全ビットを使うので、Python の非負整数として印字する
      sb.append(s"$seed ${pyList(Vector(1, 7, 32, 33, 64).map(k => java.lang.Long.toUnsignedString(r.getrandbits(k))))}\n")
      sb.append(s"$seed ${pyList((0 until 6).map(_ => r.randint(2, 14)))} ${r.choice(Vector(0, 0, 1, 2))}\n")
    }
    sb.toString
  }

  test("random(), randint, choice, getrandbits match CPython for several seeds") {
    // Double の repr: Python は最短往復表現、Scala の toString も同じ規則なので一致する
    PyDiff.assertSameAsPython(scalaOutput, "-c", script)
  }

  test("seed can be reset") {
    val r = new PyRandom(1L)
    val first = r.random()
    r.random()
    r.seed(1L)
    assertEquals(r.random(), first)
    assertEquals(first, 0.13436424411240122)
  }

  test("argument checks") {
    intercept[IllegalArgumentException](new PyRandom(-1L))
    val r = new PyRandom(1L)
    intercept[IllegalArgumentException](r.randint(3, 2))
    intercept[IllegalArgumentException](r.getrandbits(0))
    intercept[IllegalArgumentException](r.getrandbits(65))
  }
}
