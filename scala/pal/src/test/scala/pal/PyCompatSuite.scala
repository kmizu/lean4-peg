package pal

/** Pins the Python-compatibility helpers against values printed by CPython 3.14. */
class PyCompatSuite extends munit.FunSuite {

  test("PyRandom reproduces random.seed(7)") {
    val r = new PyRandom(7)
    assertEquals(Vector(r.random(), r.random(), r.random()),
      Vector(0.32383276483316237, 0.15084917392450192, 0.6509344730398537))
    assertEquals(r.randint(1, 12), 2)
    assertEquals(r.choice(Vector("ab", "ab", "abc")), "abc")
    assertEquals(r.randrange(100), 12)
  }

  test("PyRandom reproduces random.seed(11) getrandbits") {
    val r = new PyRandom(11)
    assertEquals(r.getrandbits(32), 1942955373L)
    assertEquals(r.getrandbits(5), 27L)
    assertEquals(r.random(), 0.559772386080496)
  }

  test("PyRandom agrees with python3 on a longer mixed sequence") {
    val r = new PyRandom(2026)
    val got = (0 until 40).map { i =>
      i % 4 match {
        case 0 => PyFormat.floatRepr(r.random())
        case 1 => r.randint(-5, 300).toString
        case 2 => r.choice("abc").toString
        case _ => r.randrange(7).toString
      }
    }.mkString("\n") + "\n"
    val script =
      """import random
        |random.seed(2026)
        |for i in range(40):
        |    k = i % 4
        |    if k == 0: print(repr(random.random()))
        |    elif k == 1: print(random.randint(-5, 300))
        |    elif k == 2: print(random.choice("abc"))
        |    else: print(random.randrange(7))
        |""".stripMargin
    val expected = PyDiff.python("-c", script)
    assertEquals(got, expected)
  }

  test("PyFormat.fixed rounds half to even on the exact binary value") {
    assertEquals(PyFormat.fixed(0.125, 2), "0.12")
    assertEquals(PyFormat.fixed(2.675, 2), "2.67")
    assertEquals(PyFormat.fixed(0.5, 0), "0")
    assertEquals(PyFormat.fixed(1.5, 0), "2")
    assertEquals(PyFormat.fixed(2.5, 0), "2")
    assertEquals(PyFormat.fixed(7.25, 1), "7.2")
    assertEquals(PyFormat.fixed(176.65, 1), "176.7")
  }

  test("PyFormat.floatRepr matches repr(float)") {
    assertEquals(PyFormat.floatRepr(1e-5), "1e-05")
    assertEquals(PyFormat.floatRepr(0.0001), "0.0001")
    assertEquals(PyFormat.floatRepr(123456789012345678.0), "1.2345678901234568e+17")
    assertEquals(PyFormat.floatRepr(1e16), "1e+16")
    assertEquals(PyFormat.floatRepr(0.1 + 0.2), "0.30000000000000004")
    assertEquals(PyFormat.floatRepr(3.0), "3.0")
    assertEquals(PyFormat.floatRepr(0.001234567), "0.001234567")
    assertEquals(PyFormat.floatRepr(-2.5), "-2.5")
  }

  test("PyFormat reprs") {
    assertEquals(PyFormat.strRepr("a\tb"), "'a\\tb'")
    assertEquals(PyFormat.strRepr("it's"), "\"it's\"")
    assertEquals(PyFormat.bytesRepr("B_0"), "b'B_0'")
    assertEquals(PyFormat.listRepr(Vector("'a'", "'b'")), "['a', 'b']")
    assertEquals(PyFormat.intListRepr(Vector()), "[]")
    assertEquals(PyFormat.jsonString("a\"b\\c\n\u0001"), "\"a\\\"b\\\\c\\n\\u0001\"")
  }
}
