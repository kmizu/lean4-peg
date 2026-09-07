package pal

import FppFinite.*
import DpFinite.LOWER
import DpSearchFinite.WINDOW
import MoveCenterFinite.boundary

/** The eight checked-in controller tables must be reproduced byte for byte, and the
  * deterministic default symbol order of `FppReuse.makeReusable` must build controllers
  * that behave exactly like the golden tables (same traces, only state numbers differ).
  */
class ControllerArtifactsSuite extends munit.FunSuite {

  for ((name, generate) <- ControllerArtifacts.all) {
    test(s"generated/$name-controller.json is reproduced byte for byte") {
      val actual = generate()
      val golden = PyDiff.readGolden(s"generated/$name-controller.json")
      if (actual != golden) {
        fail(PyDiff.firstDifference(actual, golden, name))
      }
    }
  }

  test("instruction JSON round-trips") {
    val p = ChainFinite.buildChainProgram("abs")
    for (row <- p.instructions) {
      assertEquals(ControllerArtifacts.instructionFromJson(ControllerArtifacts.instructionJson(row)), row)
    }
  }

  def golden(name: String): Program = ControllerArtifacts.load(PyDiff.readGolden(s"generated/$name-controller.json"))

  /** The observable outcome of a halted run: what the labels say about the final state. */
  def classify(p: Program, state: Int): (Boolean, Boolean, Boolean, Option[String]) =
    (p.found.contains(state), p.missed.contains(state), p.finished.contains(state), p.outcomes.get(state))

  /** Run both controllers from the same configuration until `stop`; require identical step
    * counts, head positions, tape contents and final-state classification.
    */
  def assertSameTrace(a: Program, b: Program, setup: Program => (Array[Tape], Array[Int]),
    cap: Int, stop: (Program, Execution) => Boolean = (_, e) => e.done): (Execution, Execution) = {
    def drive(p: Program): Execution = {
      val (tapes, positions) = setup(p)
      val e = p.execution(tapes, positions)
      while (!stop(p, e)) {
        assert(e.steps < cap, "watchdog")
        e.step()
      }
      e
    }
    val ea = drive(a)
    val eb = drive(b)
    assertEquals(ea.steps, eb.steps)
    assertEquals(ea.positions.toVector, eb.positions.toVector)
    assertEquals(ea.tapes.map(_.toMap), eb.tapes.map(_.toMap))
    assertEquals(classify(a, ea.state), classify(b, eb.state))
    (ea, eb)
  }

  /** Take both interrupted executions through their cancel entries; require the same cleanup trace. */
  def assertSameCancellation(a: Program, ea: Execution, b: Program, eb: Execution, cap: Int): Unit = {
    val ra = a.execute(ea.tapes, ea.positions, cap, start = a.cancelEntries(ea.state))
    val rb = b.execute(eb.tapes, eb.positions, cap, start = b.cancelEntries(eb.state))
    assertEquals(ra.steps, rb.steps)
    assertEquals(ra.positions, rb.positions)
    assertEquals(ra.tapes.map(_.toMap), rb.tapes.map(_.toMap))
  }

  def searchSetup(prefix: String, suffix: String, lower: Int)(p: Program): (Array[Tape], Array[Int]) = {
    val tapes = Tape.fresh(p.ntapes)
    val plain = ((LEFT +: (prefix + suffix).map(_.toString)) :+ END).toVector
    tapes(WINDOW) = Tape.of(plain.updated(prefix.length, DpSearchFinite.centerSymbol(plain(prefix.length))))
    tapes(LOWER) = Tape.bounded("1" * lower)
    val positions = Array.fill(p.ntapes)(0)
    positions(WINDOW) = prefix.length
    (tapes, positions)
  }

  val searchSample: Seq[(String, Int)] = Seq(("asasa", 0), ("as" * 35, 3), ("aabasbbbs" * 12, 0), ("b", 1), ("a" * 33, 2))

  test("default symbol order: dp-search behaves like the golden table") {
    val default = DpSearchFinite.buildSearchProgram("abs")
    val saved = golden("dp-search")
    assertEquals(default.code.size, saved.code.size)
    for ((prefix, lower) <- searchSample) {
      assertSameTrace(default, saved, searchSetup(prefix, "babas", lower), 3000 * (prefix.length + lower + 1))
    }
  }

  test("default symbol order: dp-search-reusable behaves like the golden table, cancellation included") {
    val default = DpSearchReuse.makeCancellable(DpSearchFinite.buildSearchProgram("abs"))
    val saved = golden("dp-search-reusable")
    assertEquals(default.code.size, saved.code.size)
    assertEquals(default.cancelEntries.size, saved.cancelEntries.size)
    for ((prefix, lower) <- searchSample) {
      val cap = 3000 * (prefix.length + lower + 1)
      val (ea, eb) = assertSameTrace(default, saved, searchSetup(prefix, "babas", lower), cap)
      // Cancel from the halted state: the outer cleanup must leave both with the same tapes.
      assertSameCancellation(default, ea, saved, eb, cap)
    }
  }

  val chainSample: Seq[(String, String)] = Seq(("a" * 15, "a" * 14), ("b" + "a" * 14, "a" * 14),
    ("ab" * 10, "babaabab"), ("ab", ""), ("asasasasa", "sasasasa"), ("sasasasas", "asasasas"))

  test("default symbol order: chain-monitor behaves like the golden table") {
    val default = ChainFinite.buildChainProgram("abs")
    val saved = golden("chain-monitor")
    assertEquals(default.code.size, saved.code.size)
    assertEquals(default.ready.size, saved.ready.size)
    for ((prefix, right) <- chainSample) {
      // Setup up to the first ready state, then the place-by-place stream.
      assertSameTrace(default, saved, p => ChainFiniteSuite.initial(p, prefix, 0), 5000 * (prefix.length + 1),
        stop = (p, e) => e.done || p.ready.contains(e.state))
      assertEquals(ChainFiniteSuite.run(default, prefix, right), ChainFiniteSuite.run(saved, prefix, right), (prefix, right))
    }
  }

  test("default symbol order: chain-monitor-reusable behaves like the golden table, cancellation included") {
    val default = DpSearchReuse.makeCancellable(ChainFinite.buildChainProgram("abs"))
    val saved = golden("chain-monitor-reusable")
    assertEquals(default.code.size, saved.code.size)
    assertEquals(default.cancelEntries.size, saved.cancelEntries.size)
    for ((prefix, right) <- chainSample) {
      val cap = 5000 * (prefix.length + 1)
      val (ea, eb) = assertSameTrace(default, saved, p => ChainFiniteSuite.initial(p, prefix, 0), cap,
        stop = (p, e) => e.done || p.ready.contains(e.state))
      // Cancel at the first ready state (or the no-chain halt): same cleanup trace on both.
      assertSameCancellation(default, ea, saved, eb, cap)
      assertEquals(ChainFiniteSuite.run(default, prefix, right), ChainFiniteSuite.run(saved, prefix, right), (prefix, right))
    }
  }

  /** WINDOW holds `word` at 0 with boundary tags, head at the right boundary (as the saved-table test does). */
  def moveCenterSetup(word: String)(p: Program): (Array[Tape], Array[Int]) = {
    val tapes = Tape.fresh(p.ntapes)
    for ((c, i) <- word.zipWithIndex) {
      tapes(WINDOW).write(i, (if (i % 2 == 1) { "C:" } else { "P:" }) + c)
    }
    val right = word.length - 1
    tapes(WINDOW).write(0, boundary(word.head.toString, left = true, right = right == 0))
    if (right != 0) {
      tapes(WINDOW).write(right, boundary(word.last.toString, right = true))
    }
    tapes(WINDOW).write(right + 1, "outside-right")
    val positions = Array.fill(p.ntapes)(0)
    positions(WINDOW) = right
    (tapes, positions)
  }

  test("default symbol order: move-center behaves like the golden table") {
    val default = MoveCenterFinite.buildMoveCenterProgram("abs")
    val saved = golden("move-center")
    assertEquals(default.code.size, saved.code.size)
    for (word <- Seq("a", "asbsa", "ab" * 17, "a" * 32 + "b" + "a" * 31, "ssabss", "basbsab")) {
      assertSameTrace(default, saved, moveCenterSetup(word), 700 * (word.length + 1))
    }
  }

  test("Json.dumps matches json.dumps(indent=2) on a mixed value") {
    val value = Json.obj(
      "a" -> Json.arr(Json.Num(1), Json.Str("x\"y\\z\n"), Json.obj(), Json.arr()),
      "b" -> Json.Obj(Vector("k" -> Json.Null, "é" -> Json.Bool(true))))
    PyDiff.assertSameAsPython(Json.dumps(value) + "\n", "-c",
      "import json; print(json.dumps({'a': [1, 'x\"y\\\\z\\n', {}, []], 'b': {'k': None, '\\u00e9': True}}, indent=2))")
    assertEquals(Json.parse(Json.dumps(value)), value)
  }
}
