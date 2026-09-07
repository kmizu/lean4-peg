package pal

import scala.collection.mutable

import ScaffoldCircuit.{conjunction, disjunction, neg}
import Ref.NEW

/** Queue lowering is checked against a deque, including in-flight rotations (port of `test_scaffold_circuit_queue.py`). */
object ScaffoldCircuitQueueSuite {

  def queueFixture(): Scaffold = {
    val c = new Circuit("ab<.")
    c.put("input", c.input(), c.alphabet.toVector, 'a')
    val cells = new StackPool(c, Vector("q.F" -> 0, "q.B" -> 1, "q.B2" -> 1,
                                        "q.Fr" -> 6, "q.Br" -> 12, "q.WF" -> 0, "q.WB" -> 0))
    val counters = new StackPool(c, Vector("q.m.pos" -> 6, "q.m.neg" -> 7,
                                           "q.c.pos" -> 12, "q.c.neg" -> 2))
    val q = new Queue(cells, counters, "q")
    q.push(NEW, disjunction(c.input().eqTo('a'), c.input().eqTo('b')))
    q.work()
    val take = conjunction(c.input().eqTo('<'), neg(q.empty()))
    val value = q.pop(take)
    q.work()
    val answer = c.get(value, "input", c.alphabet.toVector, 'a').eqTo('a')
    q.commit()
    c.machine(conjunction(take, answer))
  }

  /** Feed one character to the reference deque; true when `<` popped an `a`. */
  def referenceStep(queue: mutable.Queue[Char], char: Char): Boolean = {
    val answer = char == '<' && queue.nonEmpty && queue.dequeue() == 'a'
    if (char == 'a' || char == 'b') { queue.enqueue(char) }
    answer
  }
}

class ScaffoldCircuitQueueSuite extends munit.FunSuite {
  import ScaffoldCircuitQueueSuite.{queueFixture, referenceStep}

  test("queue lowering is byte-identical to Python (1081833 bytes)") {
    val output = queueFixture().compile()
    assertEquals(output.getBytes("UTF-8").length, 1081833)
    PyDiff.assertSameAsPython(output, "-c",
      "from test_scaffold_circuit_queue import queue_fixture; print(queue_fixture().compile(), end='')")
  }

  test("deque equivalence across rotations and empty pops") {
    val machine = queueFixture()
    val grammar = new Grammar(machine.compile())
    for (word <- Seq("a<", "b<", "ab<<", "aabb<<<<", "<<", "a..b..<<")) {
      val queue = mutable.Queue.empty[Char]
      var answer = false
      for (char <- word) { answer = referenceStep(queue, char) }
      assertEquals(machine.run(word), answer, word)
      assertEquals(grammar.accepts(word.reverse), answer, word)
    }
    // Python: random.seed(871); random.choices("ab<.", k=250). Mersenne Twister is not
    // reproduced here, so the same pseudo-random tail is drawn from Python.
    val tail = PyDiff.python("-c", "import random; random.seed(871); print(''.join(random.choices('ab<.', k=250)), end='')")
    assertEquals(tail.length, 250)
    val word = "a" * 30 + "b" * 20 + "<" * 55 + tail
    val queue = mutable.Queue.empty[Char]
    var root = machine.initialNode()
    for (char <- word) {
      val expected = referenceStep(queue, char)
      root = machine.step(root, char).get
      assertEquals(root.labels(machine.accepting), expected)
    }
  }
}
