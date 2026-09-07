package pal

import FppFinite.*
import FppSubroutine.{SOURCE, MARKS, buildMarkedProgram}
import DpFinite.{buildDpProgram, LOWER, OUTPUT}

/** Cleanup must work at real instruction boundaries, including half-writes. (test_fpp_reuse.py) */
class FppReuseSuite extends munit.FunSuite {

  def initial(p: Program, word: String, lower: Int): (Array[Tape], Array[Int]) = {
    val tapes = Tape.fresh(p.ntapes)
    tapes(SOURCE) = Tape.bounded(word)
    tapes(LOWER) = Tape.bounded("1" * lower)
    (tapes, Array.fill(p.ntapes)(0))
  }

  def allBlank(tape: Tape): Boolean = tape.values.forall(_ == BLANK)

  test("reuses nine tape marked kernel") {
    val p = FppReuse.makeReusable(buildMarkedProgram())
    val tapes = Tape.fresh(p.ntapes)
    val positions = Array.fill(p.ntapes)(0)
    for (word <- Seq("abababa", "aaba", "", "a")) {
      tapes(SOURCE) = Tape.bounded(word)
      val before = tapes(SOURCE).copy
      p.execute(tapes, positions, 1000 * (word.length + 1))
      assertEquals((1 to word.length).map(i => tapes(MARKS)(i)).toVector,
        (1 to word.length).map(i => if (word.take(i) == word.take(i).reverse) { "1" } else { "0" }).toVector)
      p.execute(tapes, positions, 200 * (word.length + 1), start = p.cleanup.get)
      assertEquals(positions.toVector, Vector.fill(p.ntapes)(0))
      assertEquals(tapes(SOURCE), before)
      for (tape <- p.scratch) {
        assert(allBlank(tapes(tape)))
      }
    }
  }

  test("wraps saved controller table") {
    val kernel = ControllerArtifacts.load(PyDiff.readGolden("generated/dp-place-controller.json"))
    val p = FppReuse.makeReusable(kernel)
    val (tapes, positions) = initial(p, "asasasasa", 0)
    val result = p.execute(tapes, positions, 10000)
    assertEquals(Some(result.state), p.found)
  }

  test("reuses same tapes after success and failure") {
    val p = FppReuse.makeReusable(buildDpProgram())
    val (tapes, positions) = initial(p, "a" * 65, 0)
    for ((word, lower) <- Seq(("a" * 65, 0), ("ab", 0), ("a" * 9, 1), ("", 0))) {
      // Only the input driver changes input, never a scratch tape.
      tapes(SOURCE) = Tape.bounded(word)
      tapes(LOWER) = Tape.bounded("1" * lower)
      val result = p.execute(tapes, positions, 1000 * (word.length + 1))
      val want = DpFiniteSuite.expected(word, lower)
      assertEquals(p.found.contains(result.state), want.isDefined)
      for (h <- want) {
        assertEquals(tapes(OUTPUT).values.count(_ == "1"), h)
      }
      val clean = p.execute(tapes, positions, 200 * (word.length + 1), start = p.cleanup.get)
      assertEquals(clean.positions, Vector.fill(p.ntapes)(0))
      for (tape <- p.scratch) {
        assert(allBlank(tapes(tape)))
      }
    }
  }

  test("cancellation at every instruction boundary") {
    val p = FppReuse.makeReusable(buildDpProgram())
    for ((word, lower) <- Seq(("", 0), ("ababa", 0), ("aaaaab", 1))) {
      val (tapes, positions) = initial(p, word, lower)
      val e = p.execution(tapes, positions)
      while (!e.done) {
        val saved = e.tapes.map(_.copy).toArray
        val beforeSource = saved(SOURCE).copy
        val beforeLower = saved(LOWER).copy
        val clean = p.execute(saved, e.positions.clone(), 200 * (word.length + 1),
          start = p.cancelEntries(e.state))
        assertEquals(clean.positions, Vector.fill(p.ntapes)(0), (word, e.state, e.steps))
        assertEquals(saved(SOURCE), beforeSource)
        assertEquals(saved(LOWER), beforeLower)
        for (tape <- p.scratch) {
          assert(allBlank(saved(tape)), (word, e.state, tape, saved(tape)))
        }
        e.step()
      }
    }
  }
}
