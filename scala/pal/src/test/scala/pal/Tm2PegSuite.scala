package pal

import Tm2Peg.{tmAnBn, tmEvenA, tmMarkedPalindrome}

/** tm2peg.py has no Python test; the goldens in `generated/` and the simulator pin it. */
class Tm2PegSuite extends munit.FunSuite {

  test("tm_an_bn compiles byte-identically to generated/anbn_from_tm.peg") {
    assertEquals(tmAnBn().compile(), PyDiff.readGolden("generated/anbn_from_tm.peg"))
  }

  test("tm_marked_palindrome compiles byte-identically to generated/marked_palindrome_from_tm.peg") {
    assertEquals(tmMarkedPalindrome().compile(), PyDiff.readGolden("generated/marked_palindrome_from_tm.peg"))
  }

  test("tm_even_a compiles as in Python") {
    PyDiff.assertSameAsPython(tmEvenA().compile(), "-c",
      "from tm2peg import tm_even_a; import sys; sys.stdout.write(tm_even_a().compile())")
  }

  test("tm_an_bn.run accepts exactly a^n b^n") {
    val machine = tmAnBn()
    val accepted = Vector("", "ab", "aabb", "aab", "ba", "aaabbb", "abab").filter(machine.run)
    assertEquals(accepted, Vector("", "ab", "aabb", "aaabbb"))
    for (n <- 0 to 10; w <- Twoway.product("ab", n)) {
      val k = w.length / 2
      val expected = w.length % 2 == 0 && w == ("a" * k) + ("b" * k)
      assertEquals(machine.run(w), expected, w)
    }
  }

  test("tm_marked_palindrome.run accepts exactly u#reverse(u)") {
    val machine = tmMarkedPalindrome()
    for (n <- 0 to 8; w <- Twoway.product("ab#", n)) {
      val expected = w.count(_ == '#') == 1 && {
        val Array(u, v) = w.split("#", -1)
        u == v.reverse
      }
      assertEquals(machine.run(w), expected, w)
    }
  }

  test("tm_even_a.run counts a's modulo 2") {
    assert(tmEvenA().run("abab"))
    assert(tmEvenA().run("aba"))
    assert(!tmEvenA().run("a"))
    assert(!tmEvenA().run("baaab"))
  }

  test("delta keeps first insertion position on re-assignment, like a dict") {
    import Tm2Peg.*
    val k1 = Key("0", Vector('_'), 'a')
    val k2 = Key("0", Vector('_'), 'b')
    val tm = new TM(1, Vector("0"), "0", Set("0"),
      Vector(k1 -> Step("0", Vector(TapeOp('_', Move.S))), k2 -> Step("0", Vector(TapeOp('_', Move.S))),
        k1 -> Step("0", Vector(TapeOp('x', Move.S)))))
    assertEquals(tm.delta.map(_._1), Vector(k1, k2))
    assertEquals(tm.delta.head._2.ops.head.write, 'x')
    assertEquals(tm.tapeAlphabet, Vector('_', 'x'))
  }
}
