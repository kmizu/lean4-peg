package pal

import scala.collection.immutable.VectorMap

class ScaffoldRomSuite extends munit.FunSuite {
  private def constantBits(value: Int, width: Int): Vector[Expr] = {
    Vector.tabulate(width)(bit => if ((value & (1 << bit)) != 0) Expr.TRUE else Expr.FALSE)
  }

  test("every GS instruction decodes exactly, including colored readers") {
    val program = GsHeads.unitMoves(GsHeads.compileController())
    val readers = GsHeadLiveness.analyzeReaders(program)
    val names = Vector.tabulate(readers.registers)(i => s"r$i")
    val table = ScaffoldRom.controllerTable(program, GsHeads.HEADS, Some(readers), names)
    table.rows.zipWithIndex.foreach { case (wanted, state) =>
      table.read(constantBits(state, table.width)).foreach { case (key, value) =>
        assert(value.bits.forall(bit => bit == Expr.TRUE || bit == Expr.FALSE))
        val index = value.bits.zipWithIndex.collect { case (Expr.TRUE, bit) => 1 << bit }.sum
        assertEquals(value.domain(index), wanted(key), s"state=$state key=$key")
      }
    }
  }

  test("sequential table steps compile byte-for-byte and recognize the finite automaton") {
    val rows = Vector.tabulate(7) { state =>
      VectorMap[String, Any]("a" -> ((2 * state + 1) % 7), "b" -> ((3 * state + 2) % 7),
        "accept" -> Set(0, 3)(state))
    }
    val table = new ROM(rows, VectorMap("a" -> (0 until 7).toVector, "b" -> (0 until 7).toVector,
      "accept" -> Vector(false, true)))
    val machine = Expr.share {
      val circuit = new Circuit()
      var pc: Value[Any] = circuit.get(Ref.PREVIOUS, "pc", (0 until 7).toVector, 0)
      for (_ <- 0 until 3) {
        val fields = table.read(pc.bits)
        pc = Value.select(circuit.input().eqTo('a'), fields("a"), fields("b"))
      }
      val answer = table.read(pc.bits)("accept").eqTo(true)
      circuit.put("pc", pc)
      circuit.machine(answer, initialAccepting = true)
    }
    PyDiff.assertSameAsPython(machine.compile(), "-c", """
      |from scaffold_rom import ROM
      |from scaffold_circuit import Circuit, Value, PREVIOUS
      |from symbolic_sca2peg import share_expressions
      |rows = [dict(a=(2*s+1)%7, b=(3*s+2)%7, accept=s in (0,3)) for s in range(7)]
      |table = ROM(rows, dict(a=range(7), b=range(7), accept=(False, True)))
      |with share_expressions():
      | c = Circuit()
      | pc = c.get(PREVIOUS, 'pc', tuple(range(7)), 0)
      | for _ in range(3):
      |  fields = table.read(pc.bits)
      |  pc = Value.select(c.input().eq('a'), fields['a'], fields['b'])
      | answer = table.read(pc.bits)['accept'].eq(True)
      | c.put('pc', pc)
      | machine = c.machine(answer, initial_accepting=True)
      |print(machine.compile(), end='')
      |""".stripMargin)
    val grammar = new Grammar(machine.compile())
    PyItertools.wordsBelow("ab", 7).foreach { word =>
      var pc = 0
      word.foreach(char => (0 until 3).foreach(_ => pc = rows(pc)(char.toString).asInstanceOf[Int]))
      assertEquals(grammar.accepts(word.reverse), Set(0, 3)(pc), word)
    }
  }

  test("batched reader deltas and augmentation decode, unused addresses pad with row zero") {
    val program = Program(Vector(
      Row(Event.Move(Vector(Event.Movement("A", 2), Event.Movement("B", -1))), Vector(1)),
      Row(Event.Symbols("A", "B"), Vector(2, 2)), Row(Event.Halt, Vector.empty)), 0, 4)
    val readers = GsHeadLiveness.analyzeReaders(program)
    val table = ScaffoldRom.controllerTable(program, Vector("A", "B"), Some(readers),
      Vector.tabulate(readers.registers)(i => s"r$i"), batched = true,
      augment = Some((rows, domains) => {
        rows.foreach(_("extra") = true)
        domains("extra") = Vector(false, true)
      }))
    assertEquals(table.rows.head("data_delta.r" + readers.colors("A")), 2)
    assertEquals(table.rows.head("data_delta.r" + readers.colors("B")), -1)
    val padded = table.read(constantBits(3, table.width))
    table.read(constantBits(0, table.width)).foreach { case (key, value) =>
      assertEquals(padded(key).bits, value.bits)
      assertEquals(padded(key).domain, value.domain)
    }
    assertEquals(table.read(constantBits(1, table.width))("extra").eqTo(true), Expr.TRUE)
  }

  test("invalid finite tables and address widths fail") {
    intercept[IllegalArgumentException](new ROM(Vector.empty, VectorMap.empty))
    intercept[IllegalArgumentException](new ROM(Vector(VectorMap("x" -> 0)), VectorMap("y" -> Vector(0))))
    intercept[IllegalArgumentException](new ROM(Vector(VectorMap("x" -> 0)), VectorMap("x" -> Vector(0, 0))))
    val table = new ROM(Vector(VectorMap("x" -> 0)), VectorMap("x" -> Vector(0)))
    intercept[IllegalArgumentException](table.read(Vector(Expr.TRUE)))
    assertEquals(table.read(Vector.empty)("x").domain, Vector[Any](0))
  }
}
