package pal

import Expr.TRUE
import ScaffoldCircuit.{conjunction, neg}
import Ref.PREVIOUS

/** Finite circuit lowering exercises local cells, aliases, and tape history (port of `test_scaffold_circuit.py`). */
object ScaffoldCircuitSuite {

  def balancedTape(quantum: Int = 1): Scaffold = {
    val circuit = new Circuit()
    val tape = new Tape(circuit, "t", "_a", slots = quantum)
    val inputValue = circuit.input()
    var before = circuit.get(PREVIOUS, "before", Vector(false, true), true).eqTo(true)
    var live = circuit.get(PREVIOUS, "live", Vector(false, true), true).eqTo(true)
    val a = inputValue.eqTo('a')
    val b = inputValue.eqTo('b')
    live = conjunction(live, neg(conjunction(a, neg(before))))
    for (_ <- 0 until quantum) {
      tape.write(Value.constant('a'), a)
      tape.move(1, a)
      live = conjunction(live, neg(conjunction(b, tape.left.empty())))
      tape.move(-1, b)
    }
    before = conjunction(before, neg(b))
    circuit.put("before", Value.select(before, Value.constant(true), Value.constant(false)))
    circuit.put("live", Value.select(live, Value.constant(true), Value.constant(false)))
    tape.commit()
    circuit.machine(conjunction(live, b, tape.left.empty()))
  }
}

class ScaffoldCircuitSuite extends munit.FunSuite {
  import ScaffoldCircuitSuite.balancedTape

  test("multiple local tape pushes and pops compile") {
    for (quantum <- Seq(1, 2)) {
      val machine = balancedTape(quantum)
      val grammar = new Grammar(machine.compile())
      for (word <- Words.upTo("ab", 6)) {
        val n = word.length
        val expected = n > 0 && n % 2 == 0 && word == "a" * (n / 2) + "b" * (n / 2)
        assertEquals(machine.run(word), expected, (quantum, word))
        assertEquals(grammar.accepts(word.reverse), expected, (quantum, word))
      }
    }
  }

  test("balanced tape lowering is byte-identical to Python (1641 / 5700 bytes)") {
    for ((quantum, bytes) <- Seq(1 -> 1641, 2 -> 5700)) {
      val output = balancedTape(quantum).compile()
      assertEquals(output.getBytes("UTF-8").length, bytes, s"quantum $quantum")
      PyDiff.assertSameAsPython(output, "-c",
        s"from test_scaffold_circuit import balanced_tape; print(balanced_tape($quantum).compile(), end='')")
    }
  }

  test("Value.map merges the guards of colliding keys, byte-identical to Python") {
    val c = new Circuit()
    val count = c.get(PREVIOUS, "count", Vector(0, 1, 2, 3), 0)
    val next = Value.select(c.input().eqTo('a'), count.map(n => (n + 1) % 4), count)
    c.put("count", next)
    val parity = next.map(n => n % 2)
    assertEquals(parity.domain, Vector(0, 1))
    c.put("parity", parity, Vector(0, 1), 0)
    val machine = c.machine(parity.eqTo(1))
    val expected = PyCircuit.expected(
      """c = Circuit(); count = c.get(PREVIOUS, "count", (0, 1, 2, 3), 0)
        |nxt = Value.select(c.input().eq("a"), count.map(lambda n: (n + 1) % 4), count)
        |c.put("count", nxt); parity = nxt.map(lambda n: n % 2); c.put("parity", parity, (0, 1), 0)
        |report(c.machine(parity.eq(1)), words("ab", 4))
        |""".stripMargin)
    assertEquals(PyCircuit.acceptanceBits(machine, Words.upTo("ab", 4).toVector), expected.bits)
    assertEquals(machine.compile(), expected.peg)
    for (word <- Words.upTo("ab", 4)) { assertEquals(machine.run(word), word.count(_ == 'a') % 2 == 1, word) }
  }

  test("Value.cycle(-1) counts down, byte-identical to Python") {
    val c = new Circuit()
    val count = c.get(PREVIOUS, "count", Vector(0, 1, 2, 3), 0)
    val down = Value.select(c.input().eqTo('a'), count.cycle(-1), count)
    c.put("count", down)
    val machine = c.machine(down.eqTo(3))
    val expected = PyCircuit.expected(
      """c = Circuit(); count = c.get(PREVIOUS, "count", (0, 1, 2, 3), 0)
        |down = Value.select(c.input().eq("a"), count.cycle(-1), count); c.put("count", down)
        |report(c.machine(down.eq(3)), words("ab", 4))
        |""".stripMargin)
    assertEquals(PyCircuit.acceptanceBits(machine, Words.upTo("ab", 4).toVector), expected.bits)
    assertEquals(machine.compile(), expected.peg)
    for (word <- Words.upTo("ab", 4)) { assertEquals(machine.run(word), word.count(_ == 'a') % 4 == 1, word) }
  }

  test("Value.equal on same and different domains, byte-identical to Python") {
    val c = new Circuit("ab")
    val x = c.get(PREVIOUS, "x", Vector(0, 1, 2, 3), 0)
    val y = c.get(PREVIOUS, "y", Vector(0, 1, 2), 0)
    val nx = Value.select(c.input().eqTo('a'), x.cycle(1), x)
    val ny = Value.select(c.input().eqTo('b'), y.map(n => (n + 1) % 3), y)
    c.put("x", nx)
    c.put("y", ny)
    val machine = c.machine(conjunction(nx.equal(ny), nx.equal(x)))
    val expected = PyCircuit.expected(
      """c = Circuit("ab"); x = c.get(PREVIOUS, "x", (0, 1, 2, 3), 0); y = c.get(PREVIOUS, "y", (0, 1, 2), 0)
        |nx = Value.select(c.input().eq("a"), x.cycle(1), x); ny = Value.select(c.input().eq("b"), y.map(lambda n: (n + 1) % 3), y)
        |c.put("x", nx); c.put("y", ny)
        |report(c.machine(conjunction(nx.equal(ny), nx.equal(x))), words("ab", 5))
        |""".stripMargin)
    assertEquals(PyCircuit.acceptanceBits(machine, Words.upTo("ab", 5).toVector), expected.bits)
    assertEquals(machine.compile(), expected.peg)
    for (word <- Words.upTo("ab", 5)) {
      val agree = word.count(_ == 'a') % 4 == word.count(_ == 'b') % 3
      assertEquals(machine.run(word), word.nonEmpty && word.last == 'b' && agree, word)
    }
  }

  test("finite binary value mapping and selection") {
    val circuit = new Circuit()
    val count = circuit.get(PREVIOUS, "count", Vector(0, 1, 2, 3), 0)
    val value = Value.select(circuit.input().eqTo('a'), count.map(n => (n + 1) % 4), count)
    circuit.put("count", value)
    val machine = circuit.machine(value.eqTo(3))
    val grammar = new Grammar(machine.compile())
    for (word <- Words.upTo("ab", 6)) {
      val expected = word.count(_ == 'a') % 4 == 3
      assertEquals(machine.run(word), expected, word)
      assertEquals(grammar.accepts(word.reverse), expected, word)
    }
  }

  test("Value.cycle rotates a power-of-two domain and rejects other sizes") {
    val circuit = new Circuit()
    val count = circuit.get(PREVIOUS, "count", Vector(0, 1, 2, 3), 0)
    val up = Value.select(circuit.input().eqTo('a'), count.cycle(1), count)
    circuit.put("count", up)
    val machine = circuit.machine(up.eqTo(3))
    for (word <- Words.upTo("ab", 5)) {
      assertEquals(machine.run(word), word.count(_ == 'a') % 4 == 3, word)
    }
    intercept[IllegalArgumentException] { Value.constant(1).recode(Vector(1, 2, 3)).cycle(1) }
    intercept[IllegalArgumentException] { Value.constant(1).recode(Vector(1, 2)).cycle(2) }
    intercept[IllegalArgumentException] { Value.constant(1).recode(Vector(2)) }
  }

  test("neg, conjunction, disjunction and choose simplify constants and complements") {
    import Expr.{FALSE, symbol}
    val a = symbol('a')
    val b = symbol('b')
    assertEquals(neg(neg(a)), a)
    assertEquals(neg(TRUE), FALSE)
    assertEquals(conjunction(a, TRUE, a), a)
    assertEquals(conjunction(a, neg(a)), FALSE)
    assertEquals(conjunction(), TRUE)
    assertEquals(ScaffoldCircuit.disjunction(a, FALSE, b), Expr.Or(Vector(a, b)))
    assertEquals(ScaffoldCircuit.disjunction(a, neg(a)), TRUE)
    assertEquals(ScaffoldCircuit.choose(a, TRUE, FALSE), a)
    assertEquals(ScaffoldCircuit.choose(a, FALSE, TRUE), neg(a))
    assertEquals(ScaffoldCircuit.choose(a, b, b), b)
    assertEquals(ScaffoldCircuit.choosePointer(a, Expr.SELF, Expr.NULL), Expr.select(a, Expr.SELF, Expr.NULL))
  }
}
