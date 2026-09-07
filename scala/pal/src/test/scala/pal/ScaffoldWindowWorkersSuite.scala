package pal

import scala.collection.mutable
import Ref.PREVIOUS
import ScaffoldCircuit.conjunction as AND
import TestScaffoldCircuitProgram.scalar

class ScaffoldWindowWorkersSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(900, "s")

  private def counterValue(circuit: Circuit, root: Node, counter: WindowCounter): BigInt = {
    ScaffoldWindowCounterSuite.decode(circuit, root, counter)
  }

  private def flagValues(circuit: Circuit, root: Node, view: FlagStack): Vector[Boolean] = {
    var node = root.pointers(view.rootKey)
    var index = scalar(circuit, root, view.indexKey).asInstanceOf[Int]
    val result = mutable.ArrayBuffer.empty[Boolean]
    while (node.nonEmpty) {
      val (bitKey, previousKey) = view.pool.fields(index)
      result += scalar(circuit, node.get, bitKey).asInstanceOf[Boolean]
      index = scalar(circuit, node.get, previousKey).asInstanceOf[Int]
      if (index == -1) {
        index = scalar(circuit, node.get, view.pool.indexKey).asInstanceOf[Int]
        node = node.get.pointers(view.pool.backKey)
      }
    }
    result.toVector
  }

  private def fixedStart(kind: String, quantum: Int, size: Int, lower: Int = 0): (Circuit, WindowWorker, Scaffold) = {
    val circuit = new Circuit("ab")
    var count = circuit.get(PREVIOUS, "fixture.count", (0 to size).toVector, 0)
    val start = count.eqTo(size - 1)
    val mark = count.eqTo(lower - 1)
    count = count.map(n => math.min(n + 1, size))
    val worker = if (kind == "flags") { ScaffoldWindowWorkers.flags(circuit, quantum = quantum) }
                 else { ScaffoldWindowWorkers.matcher(circuit, quantum = quantum) }
    worker.arrive()
    if (kind == "flags") { worker.mark(mark) }
    worker.start(start)
    worker.service()
    val answer = if (kind == "flags") {
      val (bit, _) = worker.flagPool.get.read(worker.flags.get.root, worker.flags.get.index)
      AND(worker.mode.eqTo("done"), bit)
    } else { worker.output }
    worker.commit()
    circuit.put("fixture.count", count)
    (circuit, worker, circuit.machine(answer))
  }

  private def checkLive(circuit: Circuit, worker: WindowWorker, node: Node,
                        state: Int, positions: collection.Map[String, Int]): Unit = {
    assertEquals(scalar(circuit, node, worker.pcKey), state)
    val distances = worker.distances
    for (pair <- distances.analysis.before(state)) {
      val key = distances.keys(distances.analysis.colors(pair))
      assertEquals(counterValue(circuit, node, distances.values.bank.counters(key)),
        BigInt(positions(pair._1) - positions(pair._2)), pair)
    }
  }

  test("frozen oriented flag views during actual arrivals") {
    val quantum = 3
    val size = 4
    val lower = 2
    val (circuit, worker, machine) = Expr.share { fixedStart("flags", quantum, size, lower) }
    for (word <- Vector("aaaa", "abba", "abab", "abaa")) {
      var node = machine.initialNode()
      val observer = new DualFlagVM(word, lower, size, Some(worker.program))
      var stopped = false
      for ((char, index) <- (word + "ab" * 120).zipWithIndex if !stopped) {
        node = machine.step(node, char).get
        assertEquals(scalar(circuit, node, "circuit.fault"), false, (word, index))
        if (index + 1 >= size) {
          for (_ <- 0 until quantum if !observer.done) { observer.step() }
          checkLive(circuit, worker, node, observer.state, observer.positions)
          assertEquals(flagValues(circuit, node, worker.flags.get), observer.flags.reverse)
        }
        stopped = scalar(circuit, node, worker.modeKey) == "done"
      }
      assertEquals(scalar(circuit, node, worker.modeKey), "done", word)
      assertEquals(node.labels(machine.accepting), word.take(lower) == word.take(lower).reverse)
    }
  }

  test("matcher instructions on contiguous actual input") {
    val quantum = 3
    val size = 2
    val (circuit, worker, machine) = Expr.share { fixedStart("match", quantum, size) }
    for ((prefix, text) <- Vector("ab" -> ("a" * 70), "ba" -> ("b" * 70))) {
      var node = machine.initialNode()
      val observer = new StreamingMatcher(prefix.reverse, Some(worker.program))
      for ((char, index) <- (prefix + text).zipWithIndex) {
        node = machine.step(node, char).get
        if (index + 1 > size) { observer.append(char) }
        if (index + 1 >= size) {
          for (_ <- 0 until quantum) { observer.step() }
          checkLive(circuit, worker, node, observer.state, observer.positions)
        }
        assertEquals(scalar(circuit, node, "circuit.fault"), false, (prefix, index))
      }
    }
  }

  test("service quantum must be positive") {
    val error = intercept[IllegalArgumentException] { ScaffoldWindowWorkers.matcher(new Circuit(), quantum = 0) }
    assertEquals(error.getMessage, "a positive finite service quantum is required")
  }
}
