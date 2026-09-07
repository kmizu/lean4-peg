package pal

import LpsHalving.*
import Twoway.{Counter, product}

/** lps_halving.py has no Python test; its `__main__` demo is pinned byte-for-byte. */
class LpsHalvingSuite extends munit.FunSuite {

  test("lps and long_case_scan on small strings") {
    assertEquals(lps("abab"), 3)
    assertEquals(lps("aabaa"), 5)
    assertEquals(lps(""), 0)
    assertEquals(lps("a"), 1)
    assertEquals(longCaseScan("abab"), Some(3))
    assertEquals(longCaseScan("ab"), None)
  }

  test("lps agrees with brute force on all binary strings up to length 12") {
    for (n <- 0 to 12; y <- product("ab", n)) {
      assertEquals(lps(y), bruteLps(y), y)
    }
  }

  test("longest border of non-periodic palindromes matches brute force") {
    for (n <- 2 to 16; half <- product("ab", (n + 1) / 2)) {
      val w = half + (if (n % 2 != 0) half.dropRight(1) else half).reverse
      if (smallestPeriod(w) * 2 > n) {
        assertEquals(longestBorderOfPalindrome(w), bruteLongestBorder(w), w)
      }
    }
  }

  test("comparison counting") {
    val counter = new Counter
    lps("aaaaab", Some(counter))
    assert(counter.value > 0)
  }

  test("__main__ demo is byte-identical to python3 lps_halving.py") {
    PyDiff.assertSameAsPython(demo(), "lps_halving.py")
  }
}
