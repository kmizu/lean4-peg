package pal

import Expr.{old, symbol, negate, either, both}
import ScaffoldEventBuffer.packService
import ScaffoldRoundTree.packServiceTree

/** Compare exact event traces; identity leaves must add no source service (port of `test_scaffold_round_tree.py`). */
class ScaffoldRoundTreeSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  /** Work toggles parity; a/b set the answer, then each work complements it. */
  private def paritySource(): Scaffold = {
    new Scaffold(Vector("out" -> true), Vector("out" -> either(
      both(symbol('a'), negate(symbol('.'))),
      both(symbol('.'), negate(old(Nil, "out"))))), Nil, "out", "ab.")
  }

  test("non power of two round keeps exact work count") {
    val source = paritySource()
    for (service <- Seq(1, 2, 3, 4, 7, 8)) {
      val flat = packService(source, service)
      val tree = packServiceTree(source, service)
      val grammar = new Grammar(tree.compile())
      for (word <- Words.upTo("ab", 4)) {
        assertEquals(tree.run(word), flat.run(word), (service, word))
        assertEquals(grammar.accepts(word.reverse), flat.run(word), (service, word))
      }
    }
  }

  private val pythonScript =
    """from scaffold_round_tree import pack_service_tree
      |from scaffold_event_buffer import pack_service
      |from symbolic_sca2peg import Scaffold, old, symbol, negate, either, both
      |source = Scaffold({"out": True}, {"out": either(
      |  both(symbol("a"), negate(symbol("."))),
      |  both(symbol("."), negate(old((), "out"))))}, {}, "out", "ab.")
      |for service in (1, 3, 7):
      |  print(pack_service_tree(source, service).compile(), end="")
      |for service in (3, 8):
      |  print(pack_service(source, service).compile(), end="")
      |""".stripMargin

  test("tree and flat service rounds match the Python packers rule for rule") {
    val source = paritySource()
    val out = new StringBuilder
    for (service <- Seq(1, 3, 7)) { out.append(packServiceTree(source, service).compile()) }
    for (service <- Seq(3, 8)) { out.append(packService(source, service).compile()) }
    PyDiff.assertSameAsPython(out.toString, "-c", pythonScript)
  }
}
