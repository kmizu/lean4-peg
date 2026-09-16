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

  private def fromBits(hex: String): Double = java.lang.Double.longBitsToDouble(java.lang.Long.parseUnsignedLong(hex, 16))

  test("PyFormat.floatRepr on subnormals and boundaries (values printed by python3)") {
    val cases = Vector(
      "0000000000000001" -> "5e-324", // Double.MIN_VALUE: Double.toString says 4.9E-324
      "0000000000000002" -> "1e-323",
      "0000000000000003" -> "1.5e-323",
      "0010000000000000" -> "2.2250738585072014e-308",
      "7fefffffffffffff" -> "1.7976931348623157e+308",
      "3e70000000000000" -> "5.960464477539063e-08",
      "4340000000000000" -> "9007199254740992.0",
      "4480f0cf064dd592" -> "1e+22",
      "44b52d02c7e14af6" -> "1e+23",
      "3fb999999999999a" -> "0.1",
      "3f0a36e2eb1c432d" -> "5e-05",
      "40fe240c9fbe76c9" -> "123456.789",
      "4011666666666666" -> "4.35",
      "3e7ad7f29abcaf48" -> "1e-07",
      "430c6bf526340000" -> "1000000000000000.0",
      "4341c37937e08001" -> "1.0000000000000002e+16",
      "43118b54f22aeb03" -> "1234567890123456.8")
    for ((bits, expected) <- cases) {
      assertEquals(PyFormat.floatRepr(fromBits(bits)), expected, bits)
    }
    assertEquals(PyFormat.floatRepr(9.9e-324), "1e-323") // 9.9e-324 parses to the second subnormal
    assertEquals(PyFormat.floatRepr(-5e-324), "-5e-324")
  }

  test("PyFormat.floatRepr agrees with repr() on 300 random bit patterns") {
    val script =
      """import random, struct
        |random.seed(5)
        |for i in range(300):
        |    kind = i % 3
        |    if kind == 0: bits = random.getrandbits(64)
        |    elif kind == 1: bits = random.getrandbits(52)
        |    else: bits = (random.getrandbits(11) << 52) | random.getrandbits(52)
        |    x = struct.unpack(">d", bits.to_bytes(8, "big"))[0]
        |    if x != x or x in (float("inf"), float("-inf")): continue
        |    print(f"{bits:016x} {x!r}")
        |""".stripMargin
    val expected = PyDiff.python("-c", script)
    val got = expected.linesIterator.map { line =>
      val bits = line.substring(0, 16)
      s"$bits ${PyFormat.floatRepr(fromBits(bits))}"
    }.mkString("", "\n", "\n")
    assertEquals(got, expected)
  }

  test("PyFormat.fixed keeps the sign of negative values and of -0.0") {
    assertEquals(PyFormat.fixed(-0.0, 2), "-0.00")
    assertEquals(PyFormat.fixed(-0.001, 2), "-0.00")
    assertEquals(PyFormat.fixed(-1.005, 2), "-1.00")
    assertEquals(PyFormat.fixed(2.5, 0), "2")
    assertEquals(PyFormat.fixed(-0.4, 0), "-0")
    assertEquals(PyFormat.fixed(0.0, 3), "0.000")
  }

  test("PyFormat.jsonString: ensure_ascii escapes everything outside ' '..'~'") {
    assertEquals(PyFormat.jsonString("aé", ensureAscii = true), "\"a\\u00e9\"")
    assertEquals(PyFormat.jsonString("aé"), "\"aé\"")
    assertEquals(PyFormat.jsonString("日本", ensureAscii = true), "\"\\u65e5\\u672c\"")
    assertEquals(PyFormat.jsonString("😀", ensureAscii = true), "\"\\ud83d\\ude00\"")
    assertEquals(PyFormat.jsonString("\u007f", ensureAscii = true), "\"\\u007f\"")
    assertEquals(PyFormat.jsonString("\u007f"), "\"\u007f\"")
    assertEquals(PyFormat.jsonString("a\u001fb"), "\"a\\u001fb\"")
    assertEquals(PyFormat.jsonString("ü\"\\", ensureAscii = true), "\"\\u00fc\\\"\\\\\"")
  }
}
