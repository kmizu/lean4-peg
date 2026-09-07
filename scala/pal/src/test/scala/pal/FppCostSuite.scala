package pal

import FppFinite.*
import FppFinite.Instruction.*
import FppSubroutine.{buildMarkedProgram, SOURCE}
import DpFinite.{buildDpProgram, LOWER}
import FppCost.{CostObservation, bounds, cutDistance, PREPARATION, DP_SCAN}

/** Check symbolic resource bounds on finite-table executions. (test_fpp_cost.py) */
class FppCostSuite extends munit.FunSuite {

  test("control graph and each resource") {
    val p = buildProgram("abs#")
    val factor = cutDistance(p)
    assertEquals(factor, 4)
    val words = (0 until 8).flatMap(n => Fpp.binaryWords(n)) ++
      Seq("a" * 512, "a" * 512 + "b", "ab" * 256,
        "b" * 128 + "a" + "b" * 64 + "aa" + "b" * 128)
    for (word <- words) {
      val z = Tape.bounded(word)
      val e = p.execution(Array(z, z.copy, new Tape(Seq(0 -> "0", 1 -> "1", 2 -> "0")),
        new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT))),
        Array(0, 1, 0, 0, 0, 0, 0))
      val seen = new CostObservation
      while (!e.done) {
        seen.observe(p.instruction(e.state))
        e.step()
      }
      seen.check(word.length, factor)
    }
  }

  test("analyzer rejects an uncharged cycle") {
    val p = buildProgram("ab#")
    p.set(p.start, Write(0, LEFT, p.start))
    val error = intercept[IllegalArgumentException] {
      cutDistance(p)
    }
    assert(error.getMessage.contains("uncharged cycle"), error.getMessage)
  }

  test("marked setup and dp scan costs") {
    val kernel = buildProgram("abs#")
    val marked = buildMarkedProgram("abs")
    val dp = buildDpProgram("abs")
    val limits = bounds()
    val kernelHalts = kernel.instructions.zipWithIndex.collect { case (Halt, q) => q }.toSet
    for (n <- 0 until 7) {
      for (word <- Fpp.binaryWords(n)) {
        val tapes = Tape.fresh(marked.ntapes)
        tapes(SOURCE) = Tape.bounded(word)
        val e = marked.execution(tapes, Array.fill(marked.ntapes)(0))
        while (e.state != kernel.start) {
          e.step()
        }
        assertEquals(e.steps, PREPARATION(n), word)
        while (!e.done) {
          e.step()
        }
        assert(e.steps <= limits.marked(n), word)
        for (lower <- Seq(0, n, n + 3)) {
          val dpTapes = Tape.fresh(dp.ntapes)
          dpTapes(SOURCE) = Tape.bounded(word)
          dpTapes(LOWER) = Tape.bounded("1" * lower)
          val run = dp.execution(dpTapes, Array.fill(dp.ntapes)(0))
          while (!kernelHalts.contains(run.state)) {
            run.step()
          }
          // This state replaces the FPP halt by one read. Charge that
          // read to the kernel, so the remaining scan excludes it.
          run.step()
          val scanStart = run.steps
          while (!run.done) {
            run.step()
          }
          assert(run.steps - scanStart <= DP_SCAN(n), (word, lower))
          assert(run.steps <= limits.dp(n), (word, lower))
        }
      }
    }
  }
}
