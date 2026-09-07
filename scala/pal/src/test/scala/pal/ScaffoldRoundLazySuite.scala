package pal

import Expr.{FALSE, SELF, symbol, old, pointer, select, read, edge, both}
import ScaffoldRound.packRound
import ScaffoldRoundLazy.packRoundLazy

/** Language comparison with full packing, including an asymmetric source (port of `test_scaffold_round_lazy.py`). */
class ScaffoldRoundLazySuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  test("queries retain all needed old slots and drop dead fields") {
    val chosen = select(symbol('a'), pointer(Seq("a")), pointer(Seq("b")))
    val source = new Scaffold(Vector("a" -> false, "out" -> false, "dead" -> true),
      Vector("a" -> symbol('a'), "out" -> read(edge(chosen, "previous"), "a"),
             "dead" -> old(Seq("unused"), "dead")),
      Vector("a" -> select(symbol('a'), SELF, pointer(Seq("a"))),
             "b" -> select(symbol('b'), SELF, pointer(Seq("b"))),
             "previous" -> pointer(Nil), "unused" -> SELF), "out")
    for (width <- Seq(1, 2, 3, 4)) {
      val full = packRound(Vector.fill(width)(source))
      val lazyRound = packRoundLazy(Vector.fill(width)(source))
      assert(!lazyRound.labels.keys.exists(_.endsWith(".dead")))
      assert(!lazyRound.pointers.keys.exists(_.endsWith(".unused")))
      assert(lazyRound.labels.size < full.labels.size)
      val grammar = new Grammar(lazyRound.compile())
      for (word <- Words.upTo("ab", 5)) {
        assertEquals(lazyRound.run(word), full.run(word), (width, word))
        assertEquals(grammar.accepts(word.reverse), full.run(word), (width, word))
      }
    }
  }

  test("distinct input events preserve asymmetric language") {
    val source = new Scaffold(Vector("out" -> true, "saved" -> false),
      Vector("out" -> both(symbol('.'), old(Nil, "saved")), "saved" -> symbol('a')),
      Nil, "out", "ab.")
    val mapping = Seq(Map('a' -> symbol('a'), 'b' -> symbol('b'), '.' -> FALSE),
                      Map('a' -> FALSE, 'b' -> FALSE, '.' -> Expr.TRUE))
    val lazyRound = packRoundLazy(Vector(source, source), Some(mapping), Some("ab"))
    val grammar = new Grammar(lazyRound.compile())
    for (word <- Seq("", "a", "b", "ab", "ba", "aba", "bba")) {
      assertEquals(lazyRound.run(word), word.isEmpty || word.last == 'a')
      assertEquals(grammar.accepts(word), word.isEmpty || word.head == 'a')
    }
  }

  private val pythonScript =
    """from scaffold_round_lazy import pack_round_lazy
      |from symbolic_sca2peg import (Scaffold, TRUE, FALSE, SELF, symbol, old, pointer, select, read, edge, both)
      |chosen = select(symbol("a"), pointer(("a",)), pointer(("b",)))
      |source = Scaffold({"a": False, "out": False, "dead": True},
      |  {"a": symbol("a"), "out": read(edge(chosen, "previous"), "a"),
      |   "dead": old(("unused",), "dead")},
      |  {"a": select(symbol("a"), SELF, pointer(("a",))),
      |   "b": select(symbol("b"), SELF, pointer(("b",))),
      |   "previous": pointer(()), "unused": SELF}, "out")
      |for width in (1, 2, 3, 4, 9):
      |  print(pack_round_lazy([source] * width).compile(), end="")
      |other = Scaffold({"out": True, "saved": False},
      |  {"out": both(symbol("."), old((), "saved")), "saved": symbol("a")}, {}, "out", "ab.")
      |mapping = [{"a": symbol("a"), "b": symbol("b"), ".": FALSE}, {"a": FALSE, "b": FALSE, ".": TRUE}]
      |print(pack_round_lazy([other] * 2, mapping, "ab").compile(), end="")
      |""".stripMargin

  test("demand-packed rule lists match the Python packer") {
    val chosen = select(symbol('a'), pointer(Seq("a")), pointer(Seq("b")))
    val source = new Scaffold(Vector("a" -> false, "out" -> false, "dead" -> true),
      Vector("a" -> symbol('a'), "out" -> read(edge(chosen, "previous"), "a"),
             "dead" -> old(Seq("unused"), "dead")),
      Vector("a" -> select(symbol('a'), SELF, pointer(Seq("a"))),
             "b" -> select(symbol('b'), SELF, pointer(Seq("b"))),
             "previous" -> pointer(Nil), "unused" -> SELF), "out")
    val out = new StringBuilder
    for (width <- Seq(1, 2, 3, 4, 9)) { out.append(packRoundLazy(Vector.fill(width)(source)).compile()) }
    val other = new Scaffold(Vector("out" -> true, "saved" -> false),
      Vector("out" -> both(symbol('.'), old(Nil, "saved")), "saved" -> symbol('a')),
      Nil, "out", "ab.")
    val mapping = Seq(Map('a' -> symbol('a'), 'b' -> symbol('b'), '.' -> FALSE),
                      Map('a' -> FALSE, 'b' -> FALSE, '.' -> Expr.TRUE))
    out.append(packRoundLazy(Vector(other, other), Some(mapping), Some("ab")).compile())
    PyDiff.assertSameAsPython(out.toString, "-c", pythonScript)
  }
}
