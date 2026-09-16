package pal

import scala.collection.mutable

import Expr.{TRUE, FALSE, SELF, NULL, symbol, old, pointer, select, read, edge, present, both, either, negate}
import ScaffoldRound.packRound

/** Check complete reachable configurations and the ordinary PEG output (port of `test_scaffold_round.py`). */
class ScaffoldRoundSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  /** Walk the source and packed node graphs together, checking every slot's labels. */
  private def compareGraph(original: Option[Node], packed: Option[Node], slot: Int, width: Int): Unit = {
    val pending = mutable.Stack((original, packed, slot))
    val seen = mutable.HashSet.empty[(Option[Node], Option[Node], Int)]
    while (pending.nonEmpty) {
      val (current, physical, currentSlot) = pending.pop()
      if (seen.add((current, physical, currentSlot))) {
        assertEquals(current.isEmpty, physical.isEmpty)
        for (node <- current; physicalNode <- physical) {
          for ((label, expected) <- node.labels) {
            assertEquals(physicalNode.labels(RoundBuilder.label(currentSlot, label)), expected, (currentSlot, label))
          }
          for ((field, target) <- node.pointers) {
            val physicalTarget = physicalNode.pointers(RoundBuilder.field(currentSlot, field))
            val targetSlot = (0 until ScaffoldCircuit.bitWidth(width))
              .filter(bit => physicalNode.labels(RoundBuilder.tagBit(currentSlot, field, bit)))
              .map(bit => 1 << bit).sum
            pending.push((target, physicalTarget, targetSlot))
          }
        }
      }
    }
  }

  private def crossRoundSource(): Scaffold = {
    val chosen = select(symbol('a'), pointer(Seq("a")), pointer(Seq("b")))
    val target = edge(chosen, "previous")
    new Scaffold(Vector("is_a" -> false, "out" -> false),
      Vector("is_a" -> symbol('a'), "out" -> both(present(target), read(target, "is_a"))),
      Vector("a" -> select(symbol('a'), SELF, pointer(Seq("a"))),
             "b" -> select(symbol('b'), SELF, pointer(Seq("b"))),
             "previous" -> pointer(Nil), "loop" -> SELF,
             "optional" -> select(symbol('a'), NULL, pointer(Seq("optional")))), "out")
  }

  test("self, null, conditional and cross-round references") {
    val source = crossRoundSource()
    for (width <- Seq(1, 2, 3, 4)) {
      val packed = packRound(Vector.fill(width)(source))
      val grammar = new Grammar(packed.compile())
      for (word <- Words.upTo("ab", 5)) {
        var original = source.initialNode()
        var physical = packed.initialNode()
        for (char <- word) {
          for (_ <- 0 until width) { original = source.step(original, char).get }
          physical = packed.step(physical, char).get
          compareGraph(Some(original), Some(physical), width - 1, width)
        }
        assertEquals(grammar.accepts(word.reverse), original.labels("out"), word)
      }
    }
  }

  test("distinct stages and asymmetric language") {
    val initial = Vector("first_a" -> false, "seen" -> false, "out" -> false)
    val first = new Scaffold(initial,
      Vector("first_a" -> either(old(Nil, "first_a"), both(negate(old(Nil, "seen")), symbol('a'))),
             "seen" -> TRUE, "out" -> old(Nil, "out")),
      Vector("previous" -> pointer(Nil)), "out")
    val second = new Scaffold(initial,
      Vector("first_a" -> old(Nil, "first_a"), "seen" -> old(Nil, "seen"),
             "out" -> both(old(Nil, "first_a"), symbol('b'))),
      Vector("previous" -> pointer(Nil)), "out")
    val packed = packRound(Seq(first, second))
    val grammar = new Grammar(packed.compile())
    assert(packed.run("ab"))
    assert(!packed.run("ba"))
    assert(grammar.accepts("ba"))
    assert(!grammar.accepts("ab"))
  }

  test("invalid round schema is rejected") {
    intercept[IllegalArgumentException] { packRound(Nil) }
    val a = new Scaffold(Vector("out" -> false), Vector("out" -> TRUE), Nil, "out")
    val b = new Scaffold(Vector("out" -> false), Vector("out" -> TRUE), Vector("p" -> NULL), "out")
    intercept[IllegalArgumentException] { packRound(Seq(a, b)) }
  }

  test("constant event guards skip disabled source queries") {
    val source = new Scaffold(Vector("out" -> false),
      Vector("out" -> both(symbol('a'), old(Nil, "out"))),
      Vector("p" -> select(symbol('a'), edge(pointer(Nil), "p"), SELF)), "out")
    // Python patched `builder.read` / `builder.follow` to raise; here they are overridden.
    val builder = new RoundBuilder(Seq(source), Some(Seq(Map('a' -> FALSE, 'b' -> TRUE)))) {
      override def read(target: Address, key: String): Expr = throw new AssertionError("disabled read")
      override def follow(target: Address, key: String): Address = throw new AssertionError("disabled edge")
    }
    val packed = builder.build()
    assert(!packed.run("ab"))
  }

  private val pythonSource =
    """from scaffold_round import pack_round
      |from symbolic_sca2peg import (Scaffold, SELF, NULL, symbol, pointer, select, read, edge, present, both)
      |chosen = select(symbol("a"), pointer(("a",)), pointer(("b",)))
      |target = edge(chosen, "previous")
      |source = Scaffold({"is_a": False, "out": False},
      |  {"is_a": symbol("a"), "out": both(present(target), read(target, "is_a"))},
      |  {"a": select(symbol("a"), SELF, pointer(("a",))),
      |   "b": select(symbol("b"), SELF, pointer(("b",))),
      |   "previous": pointer(()), "loop": SELF,
      |   "optional": select(symbol("a"), NULL, pointer(("optional",)))}, "out")
      |for width in (1, 2, 3, 4, 9, 10):
      |  print(pack_round([source] * width).compile(), end="")
      |""".stripMargin

  test("packed rule lists match the Python packer, including wide rounds") {
    val source = crossRoundSource()
    val out = new StringBuilder
    for (width <- Seq(1, 2, 3, 4, 9, 10)) { out.append(packRound(Vector.fill(width)(source)).compile()) }
    PyDiff.assertSameAsPython(out.toString, "-c", pythonSource)
  }

  test("address slot merging follows CPython's key-union order") {
    val random = new scala.util.Random(2026)
    val cases = Vector.fill(300) {
      def keys(): Vector[Int] = random.shuffle((0 until 40).toVector).take(random.nextInt(9))
      (keys(), keys())
    }
    val script = "for a, b in [" + cases.map { case (a, b) => s"(${a.mkString("[", ", ", "]")}, ${b.mkString("[", ", ", "]")})" }.mkString(", ") +
      "]:\n  print(list({k: 1 for k in a}.keys() | {k: 1 for k in b}.keys()))\n"
    val actual = cases.map { case (a, b) => CPythonSetOrder.unionKeys(a, b).mkString("[", ", ", "]") + "\n" }.mkString
    PyDiff.assertSameAsPython(actual, "-c", script)
  }
}
