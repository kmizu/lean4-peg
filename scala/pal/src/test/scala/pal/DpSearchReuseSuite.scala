package pal

import FppFinite.*
import DpFinite.LOWER
import DpSearchFinite.{WINDOW, centerSymbol, buildSearchProgram}
import DpSearchFiniteSuite.expected
import DpSearchReuse.makeCancellable

/** Cancellation of the complete search, including internal cleanup/marking. (test_dp_search_reuse.py) */
class DpSearchReuseSuite extends munit.FunSuite {

  def allBlank(tape: Tape): Boolean = tape.values.forall(_ == BLANK)

  test("saved cancellable table") {
    val p = ControllerArtifacts.load(PyDiff.readGolden("generated/dp-search-reusable-controller.json"))
    p.validate()
    val tapes = Tape.fresh(p.ntapes)
    tapes(WINDOW) = new Tape(Seq(0 -> LEFT) ++ (1 to 12).map(i => i -> "a") ++
      Seq(13 -> centerSymbol("a"), 14 -> END))
    tapes(LOWER) = new Tape(Seq(0 -> LEFT, 1 -> END))
    val before = tapes(WINDOW).copy
    val heads = Array.fill(p.ntapes)(0)
    heads(WINDOW) = 13
    val result = p.execute(tapes, heads, 10000)
    assertEquals(Some(result.state), p.found)
    p.execute(tapes, heads, 10000, start = p.cancelEntries(result.state))
    assertEquals(tapes(WINDOW), before)
    for (tape <- p.scratch) {
      assert(allBlank(tapes(tape)))
    }
  }

  test("cancel every instruction including cleanup and result marks") {
    val p = makeCancellable(buildSearchProgram("ab"))
    for (prefix <- Seq("a", "aabaa", "aabbbaaabbbaa")) {
      val tapes = Tape.fresh(p.ntapes)
      val tokens = ((LEFT +: prefix.map(_.toString)) ++ Seq("b", "a", END)).toVector
        .updated(prefix.length, centerSymbol(prefix.last.toString))
      tapes(WINDOW) = Tape.of(tokens)
      tapes(LOWER) = new Tape(Seq(0 -> LEFT, 1 -> END))
      val positions = Array.fill(p.ntapes)(0)
      positions(WINDOW) = prefix.length
      val machine = p.execution(tapes, positions)
      var running = true
      while (running) {
        val saved = tapes.map(_.copy)
        val heads = positions.clone()
        p.execute(saved, heads, 2000 * (prefix.length + 1), start = p.cancelEntries(machine.state))
        assertEquals(saved(WINDOW), Tape.of(tokens), machine.steps)
        assertEquals(saved(LOWER), new Tape(Seq(0 -> LEFT, 1 -> END)))
        val wantHeads = Array.fill(p.ntapes)(0)
        wantHeads(WINDOW) = prefix.length
        assertEquals(heads.toVector, wantHeads.toVector, machine.steps)
        for (tape <- p.scratch) {
          assert(allBlank(saved(tape)), (machine.steps, tape))
        }
        if (machine.done) {
          running = false
        } else {
          machine.step()
        }
      }
    }
  }

  test("completed search can reuse physical scratch") {
    val p = makeCancellable(buildSearchProgram("ab"))
    val tapes = Tape.fresh(p.ntapes)
    val heads = Array.fill(p.ntapes)(0)
    for (prefix <- Seq("a" * 50, "aabbbaaabbbaa", "b", "ab" * 17)) {
      val tokens = ((LEFT +: prefix.map(_.toString)) :+ END).toVector
        .updated(prefix.length, centerSymbol(prefix.last.toString))
      tapes(WINDOW) = Tape.of(tokens)
      tapes(LOWER) = new Tape(Seq(0 -> LEFT, 1 -> END))
      heads(WINDOW) = prefix.length
      val result = p.execute(tapes, heads, 5000 * (prefix.length + 1))
      assertEquals(p.found.contains(result.state), expected(prefix, 0).isDefined)
      p.execute(tapes, heads, 2000 * (prefix.length + 1), start = p.cleanup.get)
      for (tape <- p.scratch) {
        assert(allBlank(tapes(tape)))
      }
    }
  }
}
