package pal

import Expr.TRUE
import ScaffoldCircuit.{conjunction, disjunction, neg}
import Ref.NEW

/** Stack, Tape and Queue paths not covered by the ported Python tests; expectations come from Python. */
class ScaffoldCircuitStructsSuite extends munit.FunSuite {

  test("Stack.copyFrom rejects stacks from different pools") {
    val circuit = new Circuit()
    val first = new StackPool(circuit, Vector("x" -> 1))
    val second = new StackPool(circuit, Vector("y" -> 1))
    val error = intercept[IllegalArgumentException] { new Stack(first, "s").copyFrom(new Stack(second, "t")) }
    assertEquals(error.getMessage, "aliased stacks must share a declared finite cell pool")
    assertEquals(PyDiff.python("-c", PyCircuit.PREAMBLE +
      "p1 = StackPool(Circuit(), {'x': 1}); p2 = StackPool(p1.circuit, {'y': 1})\n" +
      "try: Stack(p1, 's').copy_from(Stack(p2, 't'))\n" +
      "except ValueError as e: print(e)").trim, error.getMessage)
  }

  test("shared-pool tape with aliased move slots is byte-identical to Python") {
    val c = new Circuit("ab")
    val pool = new StackPool(c, Vector("cells" -> 2), Vector('_', 'a', 'b'))
    val tape = new Tape(c, "t", pool.payload, pool = Some(pool))
    val a = c.input().eqTo('a')
    val b = c.input().eqTo('b')
    tape.write(Value(Vector('a' -> a, 'b' -> b)), TRUE)
    tape.move(1, a, slot = Some(0))
    tape.move(-1, b, slot = Some(0))
    tape.commit()
    val machine = c.machine(conjunction(neg(tape.left.empty()), tape.focus.eqTo('a')))
    val expected = PyCircuit.expected(
      """c = Circuit("ab"); pool = StackPool(c, {"cells": 2}, ("_", "a", "b"))
        |t = Tape(c, "t", pool.payload, pool=pool)
        |a, b = c.input().eq("a"), c.input().eq("b")
        |t.write(Value({"a": a, "b": b}), TRUE); t.move(1, a, slot=0); t.move(-1, b, slot=0); t.finalize()
        |report(c.machine(conjunction(neg(t.left.empty()), t.focus.eq("a"))), words("ab", 5))
        |""".stripMargin)
    assertEquals(PyCircuit.acceptanceBits(machine, Words.upTo("ab", 5).toVector), expected.bits)
    assertEquals(machine.compile(), expected.peg)
  }

  test("Tape.withSides gives the two sides different cell counts") {
    val c = new Circuit("ab")
    val tape = Tape.withSides(c, "t", "_ab", (1, 3))
    assertEquals(tape.left.pool.tags.length, 1)
    assertEquals(tape.right.pool.tags.length, 3)
    assertEquals(new Tape(c, "u", "_ab", slots = 2).right.pool.tags.length, 2)
  }

  test("shared-slot queue requires explicit work units and is byte-identical to Python") {
    val c = new Circuit("ab<.")
    c.put("input", c.input(), c.alphabet.toVector, 'a')
    val cells = new StackPool(c, Vector("cells" -> 4))
    val counters = new StackPool(c, Vector("cells" -> 4))
    val q = new Queue(cells, counters, "q", sharedSlots = true)
    val error = intercept[IllegalArgumentException] { q.work() }
    assertEquals(error.getMessage, "shared queue cells require one work_unit per physical transition")
    q.push(NEW, disjunction(c.input().eqTo('a'), c.input().eqTo('b')))
    q.workUnit()
    val take = conjunction(c.input().eqTo('<'), neg(q.empty()))
    val value = q.pop(take)
    q.workUnit()
    val answer = c.get(value, "input", c.alphabet.toVector, 'a').eqTo('a')
    q.commit()
    val machine = c.machine(conjunction(take, answer))
    val samples = Vector("a<", "b<", "ab<<", "aabb<<<<", "<<", "a..b..<<", "ab.<.<", "aaa<<<")
    val expected = PyCircuit.expected(
      """c = Circuit("ab<."); c.put("input", c.input(), tuple(c.alphabet), "a")
        |cells = StackPool(c, {"cells": 4}); counters = StackPool(c, {"cells": 4})
        |q = Queue(cells, counters, "q", shared_slots=True)
        |q.push(NEW, disjunction(c.input().eq("a"), c.input().eq("b"))); q.work_unit()
        |take = conjunction(c.input().eq("<"), neg(q.empty())); value = q.pop(take); q.work_unit()
        |answer = c.get(value, "input", tuple(c.alphabet), "a").eq("a"); q.finalize()
        |report(c.machine(conjunction(take, answer)), ["a<", "b<", "ab<<", "aabb<<<<", "<<", "a..b..<<", "ab.<.<", "aaa<<<"])
        |""".stripMargin)
    assertEquals(PyCircuit.acceptanceBits(machine, samples), expected.bits)
    assertEquals(machine.compile(), expected.peg)
  }
}
