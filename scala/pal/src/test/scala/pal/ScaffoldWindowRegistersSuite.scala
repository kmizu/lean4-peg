package pal

import TestScaffoldCircuitProgram.scalar
import ScaffoldWindowCounterSuite.decode

object ScaffoldWindowRegistersSuite {
  def fixture(): (Circuit, WindowRegisters, Scaffold) = {
    val c = new Circuit("abcdefg")
    val bank = new WindowRegisters(c, Vector("x", "y", "z"), 24)
    val char = c.input()
    for (_ <- 0 until 3) {
      val saved = bank.registers
      for ((target, source) <- Vector("x" -> "y", "y" -> "z", "z" -> "x")) {
        bank.assign(target, saved(source), char.eqTo('c'))
      }
      bank.add("x", 5, char.eqTo('a'))
      bank.add("y", -3, char.eqTo('b'))
      bank.assign("y", bank.registers("x"), char.eqTo('d'), Expr.TRUE)
      bank.reset("z", char.eqTo('e'))
      bank.assign("x", bank.registers("x"), char.eqTo('f'), Expr.TRUE)
      bank.add("z", 2, char.eqTo('g'))
    }
    for ((name, register) <- bank.registers) {
      val (zero, less) = bank.compareZero(register)
      for ((label, bit) <- Vector("zero" -> zero, "less" -> less)) {
        c.put(name + "." + label, Value.select(bit, Value.constant(true), Value.constant(false)), Vector(false, true), label == "zero")
      }
    }
    val accepting = bank.compareZero(bank.registers("x"))._2
    bank.commit()
    (c, bank, c.machine(accepting))
  }

  // The Python test builds its fixture inline. Retain that exact construction
  // here as the independent differential oracle without editing the original.
  val pythonFixture: String =
    """from scaffold_circuit import Circuit, Value, TRUE
      |from scaffold_window_registers import WindowRegisters
      |from symbolic_sca2peg import share_expressions
      |from scaffold_optimize import optimize
      |with share_expressions():
      | c = Circuit('abcdefg')
      | bank = WindowRegisters(c, ('x', 'y', 'z'), 24)
      | char = c.input()
      | for _ in range(3):
      |  saved = dict(bank.registers)
      |  for target, source in (('x','y'), ('y','z'), ('z','x')):
      |   bank.assign(target, saved[source], char.eq('c'))
      |  bank.add('x', 5, char.eq('a'))
      |  bank.add('y', -3, char.eq('b'))
      |  bank.assign('y', bank.registers['x'], char.eq('d'), TRUE)
      |  bank.reset('z', char.eq('e'))
      |  bank.assign('x', bank.registers['x'], char.eq('f'), TRUE)
      |  bank.add('z', 2, char.eq('g'))
      | for name, register in bank.registers.items():
      |  for label, bit in zip(('zero','less'), bank.compare_zero(register)):
      |   c.put(name+'.'+label, Value.select(bit, Value.constant(True), Value.constant(False)), (False,True), label=='zero')
      | accepting = bank.compare_zero(bank.registers['x'])[1]
      | bank.finalize()
      | machine = c.machine(accepting)
      | projected, _ = optimize(machine)
      |""".stripMargin
}

class ScaffoldWindowRegistersSuite extends munit.FunSuite {
  import ScaffoldWindowRegistersSuite.*
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  test("signed origins and simultaneous transfers") {
    val (c, bank, machine, projected) = Expr.share {
      val (c, bank, machine) = fixture()
      (c, bank, machine, ScaffoldOptimize.optimize(machine)._1)
    }
    val grammar = new Grammar(projected.compile())
    val rng = new PyRandom(702)
    val commands = "a" * 20 + "b" * 20 + "cfdca" + Vector.fill(250)(rng.choice("abcdefg")).mkString
    var node = machine.initialNode()
    var expected = Map("x" -> BigInt(0), "y" -> BigInt(0), "z" -> BigInt(0))
    var trace = ""
    for (char <- commands) {
      node = machine.step(node, char).get
      trace += char
      for (_ <- 0 until 3) {
        char match {
          case 'a' => expected = expected.updated("x", expected("x") + 5)
          case 'b' => expected = expected.updated("y", expected("y") - 3)
          case 'c' => expected = Map("x" -> expected("y"), "y" -> expected("z"), "z" -> expected("x"))
          case 'd' => expected = expected.updated("y", -expected("x"))
          case 'e' => expected = expected.updated("z", BigInt(0))
          case 'f' => expected = expected.updated("x", -expected("x"))
          case 'g' => expected = expected.updated("z", expected("z") + 2)
          case _ => ()
        }
      }
      for (name <- Vector("x", "y", "z")) {
        assertEquals(decode(c, node, bank.bank.counters(name)), expected(name), (trace, name))
        assertEquals(scalar(c, node, name + ".zero"), expected(name) == 0)
        assertEquals(scalar(c, node, name + ".less"), expected(name) < 0)
      }
      if (trace.length < 60) { assertEquals(grammar.accepts(trace.reverse), expected("x") < 0, trace) }
    }
  }
  test("raw and optimized register PEGs are byte identical to Python") {
    val actual = Expr.share {
      val (_, _, machine) = fixture()
      machine.compile() + ScaffoldOptimize.optimize(machine)._1.compile()
    }
    PyDiff.assertSameAsPython(actual, "-c", pythonFixture + "print(machine.compile(), end='')\nprint(projected.compile(), end='')\n")
  }
  test("selected additions and absent origins keep exact zero semantics") {
    val bank = new WindowRegisters(new Circuit(), Vector("x", "y"), 5)
    val absent = bank.select(Value.constant(None))
    assertEquals(bank.compareZero(absent), (Expr.TRUE, Expr.FALSE))
    bank.assign("x", absent)
    bank.addSelected("x", Value.constant(-3).recode(Vector(-3, 0, 2)))
    assertEquals(bank.registers("x").radius, BigInt(3))
    assertEquals(bank.compareZero(bank.registers("x")), (Expr.FALSE, Expr.TRUE))
    val saved = bank.registers
    bank.reset("x")
    bank.assign("y", bank.select(Value.constant("x"), saved), reverse = Expr.TRUE)
    assertEquals(bank.compareZero(bank.registers("y")), (Expr.FALSE, Expr.FALSE))
    intercept[IllegalArgumentException] { bank.add("y", 3) }
    intercept[IllegalArgumentException] { bank.addSelected("y", Value.constant(3)) }
  }
}
