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
