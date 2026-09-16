package pal

import ScaffoldWindowCounterSuite.decode
import TestScaffoldCircuitProgram.scalar

class ScaffoldWindowGsLiveSuite extends munit.FunSuite {
  import ScaffoldWindowGsLive.fixture
  import ScaffoldWindowGsSuite.twoEndedProgram

  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(900, "s")

  private def checkMachine(program: Option[Program], quantum: Int, words: Seq[String], peg: Boolean = true): Unit = {
    val (circuit, worker, machine, grammar) = Expr.share {
      val (circuit, worker, machine) = fixture(quantum, program)
      val grammar = if (peg) { Some(new Grammar(ScaffoldOptimize.optimize(machine)._1.compile())) } else { None }
      (circuit, worker, machine, grammar)
    }
    for (word <- words) {
      val observer = new HeadVM(word.toIndexedSeq, worker.program)
      var node = machine.evaluate(word + "!").get
      var trace = word + "!"
      var rounds = 0
      val limit = 1000 * (word.length + 1)
      while (scalar(circuit, node, worker.modeKey) != "done" && rounds < limit) {
        node = machine.step(node, '.').get
        trace += "."
        for (_ <- 0 until quantum if !observer.done) { observer.step() }
        assertEquals(scalar(circuit, node, "circuit.fault"), false, word)
        assertEquals(scalar(circuit, node, worker.pcKey), observer.state, word)
        val distances = worker.distances
        for (pair <- distances.analysis.before(observer.state)) {
          val key = distances.keys(distances.analysis.colors(pair))
          val actual = decode(circuit, node, distances.values.bank.counters(key))
          val expected = observer.positions(pair._1) - observer.positions(pair._2)
          assertEquals(actual, BigInt(expected), (word, pair))
        }
        rounds += 1
      }
      assertEquals(scalar(circuit, node, worker.modeKey), "done", word)
      assertEquals(node.labels(machine.accepting), observer.outputs.nonEmpty, word)
      grammar.foreach(value => assertEquals(value.accepts(trace.reverse), observer.outputs.nonEmpty, word))
    }
  }

  test("plain PEG for small independent program") {
    val words = Vector("", "a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "aba", "abb", "baa", "bab", "bba", "bbb",
      "abbaabba", "abbababb", "a" * 17)
    checkMachine(Some(twoEndedProgram), 5, words)
  }

  test("full batch controller live registers") {
    checkMachine(None, 3, Vector("", "a", "ab", "aa", "aba", "abb", "abab", "abba"), peg = false)
  }
}
