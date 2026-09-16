package pal

import Stage1KmpOnline.*
import Twoway.{Counter, product}

/** stage1_kmp_online.py is a module-level script; its stdout is pinned byte-for-byte. */
class Stage1KmpOnlineSuite extends munit.FunSuite {

  test("online tracks the longest palindromic suffix start") {
    for (n <- 1 to 10; x <- product("ab", n)) {
      assertEquals(online(x, new Counter), (0 until n).map(k => bruteLpsStart(x, k)).toVector, x)
    }
  }

  test("kmp_borders builds the failure table of the reversed window") {
    // window x[0..3] = "abab" (a palindrome read backwards is "baba"): fail = [0,0,0,1,2]
    assertEquals(kmpBorders("abab", 0, 3, new Counter).toVector, Vector(0, 0, 0, 1, 2))
  }

  test("module script output is byte-identical to python3 stage1_kmp_online.py") {
    PyDiff.assertSameAsPython(demo(), "stage1_kmp_online.py")
  }
}
