package pal

import scala.collection.mutable
import scala.util.boundary, boundary.break

import FppFinite.*
import DpFinite.LOWER
import DpSearchFinite.{WINDOW, centerSymbol}
import DpSearchFiniteSuite.expected
import ChainFinite.{PORT, buildChainProgram}
import DpSearchReuse.makeCancellable

/** Right-dp confirmation and three-way chain matching from real DP output. (test_chain_finite.py) */
class ChainFiniteSuite extends munit.FunSuite {
  import ChainFiniteSuite.*

  test("saved monitor without builder") {
    val p = ControllerArtifacts.load(PyDiff.readGolden("generated/chain-monitor-controller.json"))
    p.validate()
    for ((prefix, right) <- Seq(("a" * 15, "a" * 14), ("b" + "a" * 14, "a" * 14),
      ("ab" * 10, "babaabab"), ("ab", ""))) {
      val (got, used, _) = run(p, prefix, right)
      assertEquals((got, used), reference(prefix, right, 0))
    }
  }

  test("cancellation during setup and stream monitor") {
    val p = makeCancellable(buildChainProgram("ab"))
    val prefix = "b" + "a" * 14
    val (tapes, heads) = initial(p, prefix, 0)
    val originalWindow = tapes(WINDOW).copy
    val originalLower = tapes(LOWER).copy
    val machine = p.execution(tapes, heads)
    val remaining = (("a" * 14).map(_.toString) :+ END).iterator
    var running = true
    while (running) {
      val saved = tapes.map(_.copy)
      val positions = heads.clone()
      p.execute(saved, positions, 30000, start = p.cancelEntries(machine.state))
      assertEquals(saved(WINDOW), originalWindow, machine.steps)
      assertEquals(saved(LOWER), originalLower)
      assertEquals(positions.toVector, (0 until p.ntapes).map(t => if (t == WINDOW) { prefix.length } else { 0 }).toVector)
      for (tape <- p.scratch) {
        assert(saved(tape).values.forall(_ == BLANK), (machine.steps, tape))
      }
      if (machine.done) {
        running = false
      } else {
        if (p.ready.contains(machine.state)) {
          tapes(PORT).write(0, remaining.next())
        }
        machine.step()
      }
    }
  }

  test("short prefix and right streams") {
    val p = buildChainProgram("ab")
    for (n <- 1 until 8) {
      for (prefix <- Fpp.binaryWords(n)) {
        for (right <- Seq("", "a", "b", "aabababb", prefix.reverse)) {
          val (got, used, _) = run(p, prefix, right)
          assertEquals((got, used), reference(prefix, right, 0), (prefix, right))
        }
      }
    }
  }

  test("all chain outcomes and constant work per place") {
    val p = buildChainProgram("ab")
    val seen = mutable.HashSet.empty[String]
    for (prefix <- Seq("a" * 25, "baa" + "a" * 12, "ab" * 20, "aabbbaaabbbaa" * 4, "aabababbbaa")) {
      for (h <- expected(prefix, 0)) {
        val ideal = (1 until prefix.length).map { j =>
          prefix(prefix.length - math.min(j % (2 * h), 2 * h - j % (2 * h)) - 1)
        }.mkString
        val rights = mutable.ArrayBuffer(ideal, ideal.take(4 * h), ideal.take(4 * h - 1))
        for (j <- 0 until math.min(ideal.length, 4 * h + 4)) {
          rights += ideal.take(j) + (if (ideal(j) == 'a') { "b" } else { "a" }) + ideal.drop(j + 1)
        }
        for (right <- rights) {
          val (got, used, costs) = run(p, prefix, right)
          assertEquals((got, used), reference(prefix, right, 0), (prefix, right))
          assert(costs.maxOption.getOrElse(0) <= 12)
          seen += got
        }
      }
    }
    val all = Set("palindrome", "failed_right_dp", "chain_shift", "restart_search", "nonchain_move",
      "end_chain", "end_pending")
    assert(all.subsetOf(seen), seen)
  }
}

object ChainFiniteSuite {

  /** The defining outcome of feeding `right` after a DP search on `prefix`, and the places consumed. */
  def reference(prefix: String, right: String, lower: Int): (String, Int) = {
    expected(prefix, lower) match {
      case None => ("no_chain", 0)
      case Some(h) =>
        boundary {
          for ((symbol, j) <- right.zipWithIndex.map { case (s, i) => (s, i + 1) }) {
            val left = prefix(prefix.length - j - 1)
            val phase = j % (2 * h)
            val prediction = prefix(prefix.length - math.min(phase, 2 * h - phase) - 1)
            if (left == symbol && symbol == prediction) {
              if (j == prefix.length - 1) {
                break(("palindrome", j))
              }
            } else if (j <= 4 * h) {
              break(("failed_right_dp", j))
            } else if (left == symbol) {
              break(("restart_search", j))
            } else if (prediction == symbol) {
              break(("chain_shift", j))
            } else {
              break(("nonchain_move", j))
            }
          }
          (if (right.length >= 4 * h) { "end_chain" } else { "end_pending" }, right.length)
        }
    }
  }

  def initial(p: Program, prefix: String, lower: Int): (Array[Tape], Array[Int]) = {
    val tapes = Tape.fresh(p.ntapes)
    val tokens = ((LEFT +: prefix.map(_.toString)) :+ END).toVector
      .updated(prefix.length, centerSymbol(prefix.last.toString))
    tapes(WINDOW) = Tape.of(tokens)
    tapes(LOWER) = Tape.bounded("1" * lower)
    val heads = Array.fill(p.ntapes)(0)
    heads(WINDOW) = prefix.length
    (tapes, heads)
  }

  /** Drive the monitor: run to readiness, then feed `right` then END through PORT; returns
    * (outcome, places consumed, instructions per place).
    */
  def run(p: Program, prefix: String, right: String, lower: Int = 0): (String, Int, Vector[Int]) = {
    val (tapes, heads) = initial(p, prefix, lower)
    val machine = p.execution(tapes, heads)
    val cap = 5000 * (prefix.length + lower + 1)
    while (!p.ready.contains(machine.state) && !machine.done) {
      assert(machine.steps < cap)
      machine.step()
    }
    var consumed = 0
    val costs = Vector.newBuilder[Int]
    if (machine.done) {
      return (p.outcomes(machine.state), consumed, costs.result())
    }
    boundary {
      for (symbol <- right.map(_.toString) :+ END) {
        tapes(PORT).write(0, symbol)
        val before = machine.steps
        machine.step()
        while (!p.ready.contains(machine.state) && !machine.done) {
          assert(machine.steps - before < 30)
          machine.step()
        }
        costs += machine.steps - before
        if (symbol != END) {
          consumed += 1
        }
        if (machine.done) {
          break((p.outcomes(machine.state), consumed, costs.result()))
        }
      }
      throw new AssertionError("did not halt at stream end")
    }
  }
}
