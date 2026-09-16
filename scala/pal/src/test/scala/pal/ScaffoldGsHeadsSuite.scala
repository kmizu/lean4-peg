package pal

import TestScaffoldCircuitProgram.scalar

/** Observation helpers shared only by the GS circuit suites. */
object ScaffoldGsHeadsSuite {
  def stack(circuit: Circuit, node: Node, view: Stack): Vector[Any] = {
    var current = node.pointers(view.rootKey)
    var tag = scalar(circuit, node, view.tagKey).asInstanceOf[CellTag]
    val answer = Vector.newBuilder[Any]
    while (current.nonEmpty) {
      val cell = current.get
      answer += scalar(circuit, cell, view.pool.key(tag, "data"))
      val below = cell.pointers(view.pool.key(tag, "below"))
      tag = scalar(circuit, cell, view.pool.key(tag, "tag")).asInstanceOf[CellTag]
      current = below
    }
    answer.result()
  }
}

class ScaffoldGsHeadsSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  private lazy val built = Expr.share { ScaffoldGsHeads.fixture() }

  test("loaded snapshot and every executed instruction") {
    val (circuit, worker, machine) = built
    for (word <- Vector("", "ab", "aabaaa")) {
      val vm = new HeadVM(word.toIndexedSeq, worker.program)
      var node = machine.evaluate(word + "!" + "." * (word.length + 1)).get
      assertEquals(scalar(circuit, node, worker.modeKey), "run")
      val observed = Vector.newBuilder[Int]
      while (!vm.done) {
        vm.step()
        node = machine.step(node, '.').get
        assertEquals(scalar(circuit, node, worker.pcKey), vm.state)
        assertEquals(scalar(circuit, node, "circuit.fault"), false)
        if (scalar(circuit, node, "gs.border") == true) {
          val pair = worker.bank.get.counters(("Origin", "KP"))
          observed += ScaffoldGsHeadsSuite.stack(circuit, node, pair.negativeStack).size -
            ScaffoldGsHeadsSuite.stack(circuit, node, pair.positiveStack).size
        }
        for (name <- Vector("A", "B", "P")) {
          val location = vm.positions(name)
          val wanted = if (location < word.length) { word(location) } else { '_' }
          assertEquals(scalar(circuit, node, worker.tapes(name).symbolKey), wanted, (word, vm.steps, name, location))
        }
      }
      node = machine.step(node, '.').get
      assertEquals(observed.result(), vm.outputs)
      assertEquals(scalar(circuit, node, worker.modeKey), "done")
      assertEquals(node.labels("accept"), vm.outputs.nonEmpty)
    }
  }

  test("bounded ordinary grammar is byte-identical to Python") {
    val source = built._3.compile()
    assert(source.length < 3000000)
    assert(source.startsWith("S = "))
    assert(!source.contains("<%"))
    PyDiff.assertSameAsPython(source, "-c", "from scaffold_gs_heads import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = fixture()[2]\nprint(m.compile(), end='')")
  }

  test("uncompacted distances also compile byte-identically") {
    val source = Expr.share { ScaffoldGsHeads.fixture(compact = false)._3 }.compile()
    PyDiff.assertSameAsPython(source, "-c", "from scaffold_gs_heads import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions(): m = fixture(compact=False)[2]\nprint(m.compile(), end='')")
  }
}
