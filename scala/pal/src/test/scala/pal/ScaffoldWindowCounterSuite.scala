package pal

import TestScaffoldCircuitProgram.scalar
import ScaffoldWindowCounter.fixture

object ScaffoldWindowCounterSuite {
  def applyCommand(values: (BigInt, BigInt), char: Char): (BigInt, BigInt) = {
    val (x, y) = values
    char match {
      case 'a' => (x + 7, y)
      case 'b' => (x - 5, y)
      case 'c' => (x, x)
      case 'd' => (y, y)
      case 'e' => (x, y - 3)
      case 'f' => (BigInt(0), y)
      case 'g' => (-x, y)
      case 'h' => (x, -x)
      case _ => values
    }
  }
  private def stackSize(circuit: Circuit, node: Node, view: Stack): Int = {
    var current = node.pointers(view.rootKey)
    var tag = scalar(circuit, node, view.tagKey).asInstanceOf[CellTag]
    var size = 0
    while (current.nonEmpty) {
      val cell = current.get
      size += 1
      current = cell.pointers(view.pool.key(tag, "below"))
      tag = scalar(circuit, cell, view.pool.key(tag, "tag")).asInstanceOf[CellTag]
    }
    size
  }
  def decode(circuit: Circuit, root: Node, counter: WindowCounter): BigInt = {
    val quotient = stackSize(circuit, root, counter.quotient.pos) - stackSize(circuit, root, counter.quotient.negativeStack)
    var digits = (0 until counter.bank.width).filter(bit => scalar(circuit, root, s"${counter.name}.low.$bit") == true)
      .map(bit => BigInt(1) << bit).sum
    if (digits >= counter.bank.base / 2) { digits -= counter.bank.base }
    quotient * counter.bank.base + digits
  }
}

class ScaffoldWindowCounterSuite extends munit.FunSuite {
  import ScaffoldWindowCounterSuite.*
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  test("crossings copies negations and queries before normalization") {
    val (circuit, bank, machine) = Expr.share { fixture() }
    var root = machine.initialNode()
    var values = (BigInt(0), BigInt(0))
    val rng = new PyRandom(910)
    val commands = "a" * 70 + "gch" + "b" * 200 + "g" + "e" * 80 + "dghf" + Vector.fill(1000)(rng.choice("abcdefgh")).mkString
    for ((char, index) <- commands.zipWithIndex) {
      values = applyCommand(values, char)
      root = machine.step(root, char).get
      for ((name, value) <- bank.names.zip(Vector(values._1, values._2))) {
        assertEquals(decode(circuit, root, bank.counters(name)), value, (index, char, values))
        for ((relation, expected) <- Vector("zero" -> (value == 0), "negative" -> (value < 0), "positive" -> (value > 0))) {
          assertEquals(scalar(circuit, root, name + "." + relation), expected, (index, name, relation))
        }
      }
    }
  }
  test("ordinary PEG on original commands") {
    val (_, _, machine) = Expr.share { fixture() }
    val source = machine.compile()
    assert(source.length < 30000)
    val grammar = new Grammar(source)
    val rng = new PyRandom(911)
    val cases = Vector("", "a", "f", "aaaaabbbbbbb", "a" * 32 + "gchd", "b" * 33 + "gf", "abcghd") ++
      Vector.fill(70)(Vector.fill(rng.randrange(1, 45))(rng.choice("abcdefgh")).mkString)
    for (word <- cases) {
      val values = word.foldLeft((BigInt(0), BigInt(0)))(applyCommand)
      assertEquals(grammar.accepts(word.reverse), values._1 == 0, (word, values))
    }
  }
  test("large batch needs one cell slot per register") {
    val (circuit, bank, machine) = Expr.share {
      val circuit = new Circuit()
      val bank = new WindowCounters(circuit, Vector("x"), 65535)
      val counter = bank.counters("x")
      counter.add(32767, circuit.input().eqTo('a'))
      counter.add(-32768, circuit.input().eqTo('b'))
      val answer = counter.zero()
      bank.commit()
      (circuit, bank, circuit.machine(answer, initialAccepting = true))
    }
    var root = machine.initialNode()
    var value = BigInt(0)
    for (char <- "aaabbbbaabba") {
      value += (if (char == 'a') { 32767 } else { -32768 })
      root = machine.step(root, char).get
      assertEquals(decode(circuit, root, bank.counters("x")), value)
    }
    assertEquals(bank.pool.tags.size, 1)
    assert(machine.compile().length < 20000)
  }
  test("window is checked at construction") {
    val bank = new WindowCounters(new Circuit(), Vector("x", "y"), 7)
    val x = bank.counters("x")
    val y = bank.counters("y")
    x.add(7)
    intercept[IllegalArgumentException] { x.inc() }
    y.copyFrom(x)
    intercept[IllegalArgumentException] { y.dec() }
    x.reset()
    x.inc()
    bank.commit()
    intercept[IllegalArgumentException] { x.inc() }
    intercept[IllegalArgumentException] { x.commit() }
  }
  test("fixture PEG is byte identical to Python") {
    val (_, _, machine) = Expr.share { fixture() }
    PyDiff.assertSameAsPython(machine.compile(), "-c",
      "from scaffold_window_counter import fixture\nfrom symbolic_sca2peg import share_expressions\nwith share_expressions():\n _, _, m = fixture()\nprint(m.compile(), end='')")
  }
  test("finite words reject unequal widths and support arbitrary integer widths") {
    val a = Bits.constant(0, 2)
    val b = Bits.constant(0, 3)
    intercept[IllegalArgumentException] { a.plus(b) }
    intercept[IllegalArgumentException] { a.equal(b) }
    intercept[IllegalArgumentException] { a.unsignedLess(b) }
    intercept[IllegalArgumentException] { Bits.select(Expr.TRUE, a, b) }
    val wide = BigInt(1) << 70
    assertEquals(Bits.constant(wide, 73).add(-wide).zero(), Expr.TRUE)
    assertEquals(Bits.constant(-wide, 73).negated(), Bits.constant(wide, 73))
    val bank = new WindowCounters(new Circuit(), Vector("wide"), wide)
    bank.counters("wide").add(wide)
    assertEquals(bank.counters("wide").radius, wide)
  }
}
