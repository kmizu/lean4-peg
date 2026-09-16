package pal

import OnlineManacher.*
import Twoway.product

/** online_manacher.py has no Python test; its `__main__` demo is pinned byte-for-byte. */
class OnlineManacherSuite extends munit.FunSuite {

  test("online('abbabba') matches Python") {
    assertEquals(online("abbabba"), Trace(Vector(0, 1, 1, 0, 2, 1, 0), Vector(1, 1, 0, 3, 0, 0), Vector(0, 1, 2, 3, 4, 5)))
  }

  test("starts agree with brute force and codes are recorded once, increasing") {
    for (n <- 1 to 10; x <- product("ab", n)) {
      val Trace(starts, _, order) = online(x)
      assertEquals(starts, (0 until n).map(k => bruteLpsStart(x, k)).toVector, x)
      assertEquals(order, order.sorted, x)
      assertEquals(order.distinct, order, x)
    }
  }

  test("__main__ demo is byte-identical to python3 online_manacher.py") {
    PyDiff.assertSameAsPython(demo(), "online_manacher.py")
  }
}
