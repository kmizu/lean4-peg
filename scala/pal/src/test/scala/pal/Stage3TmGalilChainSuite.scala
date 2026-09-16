package pal

import Stage3TmGalilChain.*
import Twoway.product

/** stage3_tm_galil_chain.py has no Python test; drivers and demo are pinned against python3. */
class Stage3TmGalilChainSuite extends munit.FunSuite {

  test("run_online(('aabab'*4)) matches Python outputs and costs") {
    assertEquals(runOnline("aabab" * 4), (
      Vector(1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0),
      Vector(2, 12, 15, 21, 61, 2, 2, 186, 2, 2, 2, 2, 276, 2, 2, 2, 2, 472, 2, 1)))
  }

  test("run_realtime(('aabab'*4), 64) matches Python") {
    assertEquals(runRealtime("aabab" * 4, 64), Vector(1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0))
  }

  test("online output is the truth for all binary strings up to length 9") {
    for (n <- 1 to 9; x <- product("ab", n)) {
      assertEquals(runOnline(x)._1, brute(x), x)
    }
  }

  test("dp_search finds the smallest double-palindrome step, yielding once per unit") {
    // 'aaaaaaaa' in places: C = 15, r = 0 -> h_G = 1 ([C-4, C] = 'a_a_a' is a double palindrome)
    val m = new Machine("aaaaaaaa")
    (1 to 8).foreach(_ => m.feed())
    val search = new DpSearch(m, 15, 0)
    var units = 0
    while (search.next()) { units += 1 }
    assertEquals(search.result, Some(1))
    assert(units > 0)
    assertEquals(search.next(), false)
  }

  test("kmp_suffix_palindromes lists suffix palindrome lengths, decreasing, in places") {
    val m = new Machine("abba")
    (1 to 4).foreach(_ => m.feed())
    val kmp = new KmpSuffixPalindromes(m, 1, 7) // places 1..7 = a_b_b_a
    assertEquals(kmp.runWith(() => ()), Vector(7, 1))
  }

  test("chain_last") {
    assertEquals(chainLast(5, 17, 3), 14)
    assertEquals(chainLast(5, 6, 3), 5)
  }

  test("run_online costs agree with python3 on all strings up to length 8") {
    val got = (for (n <- 1 to 8; x <- product("ab", n)) yield {
      val (out, cost) = runOnline(x)
      out.mkString + " " + cost.mkString(",")
    }).mkString("\n") + "\n"
    PyDiff.assertSameAsPython(got, "-c",
      """from itertools import product
        |from stage3_tm_galil_chain import run_online
        |for n in range(1, 9):
        |    for t in product('ab', repeat=n):
        |        out, cost = run_online(''.join(t))
        |        print(''.join(map(str, out)), ','.join(map(str, cost)))
        |""".stripMargin)
  }

  test("__main__ demo is byte-identical to python3 stage3_tm_galil_chain.py") {
    PyDiff.assertSameAsPython(demo(), "stage3_tm_galil_chain.py")
  }
}
