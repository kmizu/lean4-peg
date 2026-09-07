package pal

import Expr.{TRUE, FALSE, SELF, NULL, old, pointer, read, edge, negate, both, either, symbol}
import ScaffoldOptimize.optimize

/** Constant propagation must preserve sentinel, null, and recursive behavior (port of `test_scaffold_optimize.py`). */
class ScaffoldOptimizeSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  private def nullsAndConstants(): Scaffold = {
    new Scaffold(
      Vector("out" -> false, "off" -> false, "propagate" -> false, "on" -> true),
      Vector("off" -> FALSE, "propagate" -> old(Nil, "off"), "on" -> TRUE,
             "out" -> either(both(negate(old(Nil, "propagate")), symbol('a')),
                             read(edge(pointer(Nil), "null"), "on"))),
      Vector("null" -> NULL, "dead" -> pointer(Seq("null"))), "out")
  }

  private def sentinelPointer(): Scaffold = {
    new Scaffold(
      Vector("out" -> true, "first" -> true, "on" -> true),
      Vector("first" -> FALSE, "on" -> TRUE,
             "out" -> either(old(Nil, "first"), both(symbol('a'), read(pointer(Seq("p")), "on")))),
      Vector("p" -> SELF), "out")
  }

  private def compare(source: Scaffold, reduced: Scaffold): Unit = {
    val grammar = new Grammar(reduced.compile())
    for (word <- Words.upTo("ab", 5)) {
      assertEquals(reduced.run(word), source.run(word), word)
      assertEquals(grammar.accepts(word.reverse), source.run(word), word)
    }
  }

  test("nulls and constant labels propagate before field projection") {
    val source = nullsAndConstants()
    val (reduced, stats) = optimize(source)
    assert(stats.rounds > 1)
    assertEquals(reduced.labels.keySet, Set("out"))
    assert(reduced.pointers.isEmpty)
    compare(source, reduced)
  }

  test("initial value and sentinel pointer are not erased") {
    val source = sentinelPointer()
    val (reduced, _) = optimize(source, roots = Seq("first"))
    assert(reduced.labels.contains("first"))
    assert(reduced.pointers.contains("p"))
    compare(source, reduced)
  }

  private val pythonScript =
    """from scaffold_optimize import optimize
      |from symbolic_sca2peg import (Scaffold, TRUE, FALSE, SELF, NULL, old, pointer,
      |                              read, edge, negate, both, either, symbol)
      |first = Scaffold({"out": False, "off": False, "propagate": False, "on": True},
      |  {"off": FALSE, "propagate": old((), "off"), "on": TRUE,
      |   "out": either(both(negate(old((), "propagate")), symbol("a")),
      |                 read(edge(pointer(()), "null"), "on"))},
      |  {"null": NULL, "dead": pointer(("null",))}, "out")
      |second = Scaffold({"out": True, "first": True, "on": True},
      |  {"first": FALSE, "on": TRUE,
      |   "out": either(old((), "first"), both(symbol("a"), read(pointer(("p",)), "on")))},
      |  {"p": SELF}, "out")
      |for source, roots in ((first, ()), (second, ("first",))):
      |  reduced, stats = optimize(source, roots=roots)
      |  print(reduced.compile(), end="")
      |  print(stats["rounds"], stats["constant_labels"], stats["null_pointers"],
      |        stats["labels_removed"], stats["pointers_removed"])
      |""".stripMargin

  test("reduced rule lists and statistics match the Python optimizer") {
    val out = new StringBuilder
    for ((source, roots) <- Seq((nullsAndConstants(), Nil), (sentinelPointer(), Seq("first")))) {
      val (reduced, stats) = optimize(source, roots)
      out.append(reduced.compile())
      out.append(s"${stats.rounds} ${stats.constantLabels} ${stats.nullPointers} ${stats.labelsRemoved} ${stats.pointersRemoved}\n")
    }
    PyDiff.assertSameAsPython(out.toString, "-c", pythonScript)
  }
}
