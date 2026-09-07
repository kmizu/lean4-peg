package pal

import Expr.{TRUE, SELF, NULL, symbol, old, exists, negate, both, either, pointer, select, read, edge, present}
import GenerateScaffoldExamples.markedPalindrome

/** Output-side tests against independent language specifications (port of `test_symbolic_sca2peg.py`). */
class SymbolicSca2PegSuite extends munit.FunSuite {

  test("shared construction and streaming preserve the emitted grammar") {
    val expected = markedPalindrome().compile()
    val actual = Expr.share {
      assert(symbol('a') eq symbol('a'))
      Expr.share {
        assert(symbol('b') eq symbol('b'))
      }
      markedPalindrome().iterRules().mkString("", "\n", "\n")
    }
    assert(!Expr.sharing)
    assertEquals(actual, expected)
  }

  test("marked palindrome grammar is byte-identical to Python and equivalent to the committed golden") {
    val output = markedPalindrome().compile()
    PyDiff.assertSameAsPython(output, "-c",
      "from generate_scaffold_examples import marked_palindrome; print(marked_palindrome().compile(), end='')")
    // The committed generated/scaffold_marked_palindrome.peg predates the current
    // Python emitter (same 35 rules, older E_i numbering/order), so current Python
    // does not reproduce it byte-for-byte either. Check language equivalence instead.
    val golden = PyDiff.readGolden("generated/scaffold_marked_palindrome.peg")
    assertEquals(output.linesIterator.length, golden.linesIterator.length)
    val ours = new Grammar(output)
    val theirs = new Grammar(golden)
    for (word <- Words.upTo("ab#", 6)) {
      assertEquals(ours.accepts(word), theirs.accepts(word), word)
    }
    assertEquals(GenerateScaffoldExamples.summary(output),
      PyDiff.python("-c", "from generate_scaffold_examples import marked_palindrome\n" +
        "o = marked_palindrome().compile(); print(f'{len(o.splitlines())} rules, {len(o.encode())} bytes')").trim)
  }

  test("marked palindrome has real push, pop and null paths") {
    val machine = markedPalindrome()
    val grammar = new Grammar(machine.compile())
    for (word <- Words.upTo("ab#", 6)) {
      val pieces = word.split("#", -1)
      val expected = pieces.length == 2 && pieces(0) == pieces(1).reverse
      assertEquals(machine.run(word), expected, word)
      assertEquals(grammar.accepts(word.reverse), expected, word)
    }
  }

  test("direction is reversed for asymmetric language") {
    val machine = new Scaffold(
      Vector("first_a" -> false, "seen" -> false, "out" -> false),
      Vector("first_a" -> either(old(Nil, "first_a"), both(negate(old(Nil, "seen")), symbol('a'))),
             "seen" -> TRUE,
             "out" -> both(old(Nil, "first_a"), symbol('b'))),
      Nil, "out")
    val grammar = new Grammar(machine.compile())
    assert(machine.run("ab"))
    assert(grammar.accepts("ba"))
    assert(!grammar.accepts("ab"))
  }

  test("selected null cannot fall back to live pointer") {
    val machine = new Scaffold(Vector("out" -> false), Vector("out" -> exists(Seq("p"))),
      Vector("p" -> select(symbol('a'), NULL, SELF)), "out")
    val grammar = new Grammar(machine.compile())
    assert(!grammar.accepts("ba"))
    assert(grammar.accepts("ab"))
  }

  test("self edges and phase inverse preserve even parity") {
    val machine = new Scaffold(Vector("out" -> true), Vector("out" -> negate(old(Nil, "out"))),
      Vector("self" -> SELF), "out", "a")
    val source = machine.compile()
    val transformed = new Grammar(PhasePeg.inverseRepeat(source, 2))
    for (n <- 0 until 8) {
      assertEquals(new Grammar(source).accepts("a" * n), n % 2 == 0)
      assert(transformed.accepts("a" * n))
    }
  }

  test("types and missing fields are rejected") {
    for (expr <- Seq(pointer(Nil), old(Seq("missing"), "out"), old(Nil, "missing"))) {
      intercept[IllegalArgumentException] {
        new Scaffold(Vector("out" -> false), Vector("out" -> expr), Nil, "out")
      }
    }
    intercept[IllegalArgumentException] {
      new Scaffold(Vector("out" -> false), Vector("out" -> TRUE), Vector("p" -> TRUE), "out")
    }
  }

  test("computed pointer queries share conditional navigation") {
    // Remember the previous a and b separately. Query the predecessor of
    // whichever remembered node is selected by the current input symbol.
    val chosen = select(symbol('a'), pointer(Seq("a")), pointer(Seq("b")))
    val target = edge(chosen, "previous")
    val machine = new Scaffold(
      Vector("is_a" -> false, "out" -> false),
      Vector("is_a" -> symbol('a'), "out" -> both(present(target), read(target, "is_a"))),
      Vector("a" -> select(symbol('a'), SELF, pointer(Seq("a"))),
             "b" -> select(symbol('b'), SELF, pointer(Seq("b"))),
             "previous" -> pointer(Nil)),
      "out")
    val grammar = new Grammar(machine.compile())
    for (word <- Words.upTo("ab", 7)) {
      val index = if (word.isEmpty) { -1 } else { word.dropRight(1).lastIndexOf(word.last.toInt) }
      val expected = index > 0 && word.charAt(index - 1) == 'a'
      assertEquals(machine.run(word), expected, word)
      assertEquals(grammar.accepts(word.reverse), expected, word)
    }
  }

  test("new node queries are rejected even inside pointer choices") {
    for (target <- Seq(SELF, select(TRUE, NULL, SELF))) {
      val error = intercept[IllegalArgumentException] {
        new Scaffold(Vector("out" -> false), Vector("out" -> read(target, "out")), Nil, "out")
      }
      assert(error.getMessage.contains("old nodes"), error.getMessage)
    }
  }

  test("clearExpressionCache drops the interning index but keeps sharing active") {
    Expr.share {
      val first = symbol('a')
      assert(symbol('a') eq first)
      Expr.clearExpressionCache()
      assert(Expr.sharing)
      val second = symbol('a')
      assertEquals(second, first)
      assert(!(second eq first))
      assert(symbol('a') eq second)
    }
    Expr.clearExpressionCache() // no index outside a share scope: a no-op
    assert(!Expr.sharing)
    assert(!(symbol('a') eq symbol('a')))
  }

  test("Expr.make rebuilds every tag from its tuple shape and rejects malformed shapes") {
    val samples = Seq(TRUE, symbol('a'), SELF, NULL, old(Seq("top"), "a"), exists(Seq("top")), negate(TRUE),
      both(TRUE, symbol('a')), either(), pointer(Seq("top", "next")), select(TRUE, SELF, NULL),
      read(pointer(Nil), "a"), edge(pointer(Nil), "top"), present(SELF))
    for (expr <- samples) {
      assertEquals(Expr.make(expr.tag, expr.args), expr)
    }
    intercept[IllegalArgumentException] { Expr.make("bogus", Nil) }
    intercept[IllegalArgumentException] { Expr.make("not", Seq(TRUE, TRUE)) }
  }
}
