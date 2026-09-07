package pal

import scala.collection.mutable

import Scavm.{Stats, VM}
import ScavmStructs.{Builder, emit}
import ScaffoldProgram.{ProgramView, TapeView}
import FppFinite.{BLANK, END, LEFT}
import FppSubroutine.{buildMarkedProgram, MARKS, SOURCE}

/** Port of `test_scaffold_program.py`: finite tape instructions must have the same
  * effect on the scaffold. Each driver is also run in Python and its trace and VM
  * statistics compared line by line.
  */
class ScaffoldProgramSuite extends munit.FunSuite {

  /** Python `("write", symbol)` / `("move", direction)` operations of the FPP fixture. */
  private sealed trait Op
  private final case class WriteOp(symbol: String) extends Op
  private final case class MoveOp(direction: Int) extends Op

  /** The first Python test as a driver; returns the final statistics. */
  private def twoPrograms(): Stats = {
    val kernel = buildMarkedProgram("ab")
    val vm = new VM
    for (step <- 0 until 3) {
      vm.begin()
      val b = new Builder
      val first = new ProgramView(vm, vm.top, b, kernel, name = "f")
      val second = new ProgramView(vm, vm.top, b, kernel, name = "d")
      if (step == 0) {
        first.tapes(SOURCE).write("a")
        first.tapes(SOURCE).move(1)
        first.tapes(SOURCE).write("b")
        second.tapes(SOURCE).write(LEFT)
        second.start()
      } else if (step == 1) {
        first.reset()
        assertEquals(second.tapes(SOURCE).read(), LEFT)
        assert(!second.done)
      } else {
        assertEquals(first.tapes(SOURCE).read(), BLANK)
        intercept[IllegalArgumentException](first.tapes(SOURCE).move(-1))
        assert(first.done)
        assertEquals(second.tapes(SOURCE).read(), LEFT)
        assert(!second.done)
      }
      first.finish()
      second.finish()
      emit(vm, b)
    }
    vm.stats
  }

  /** The second Python test as a driver (`random.seed(422)`); returns the trace. */
  private def privateTape(): String = {
    val random = new PyRandom(422L)
    val vm = new VM
    val data = mutable.HashMap.empty[Int, String]
    var head = 0
    val out = new StringBuilder
    for (step <- 0 until 1500) {
      vm.begin()
      val b = new Builder
      val tape = new TapeView(vm, vm.top, b, "t")
      val before = tape.read()
      assertEquals(before, data.getOrElse(head, BLANK))
      val action = random.choice(Vector("write", "left", "right"))
      if (action == "write") {
        val symbol = random.choice("ab01_")
        tape.write(symbol)
        data(head) = symbol
      } else if (action == "right") {
        tape.move(1)
        head += 1
      } else if (head > 0) {
        tape.move(-1)
        head -= 1
      } else {
        intercept[IllegalArgumentException](tape.move(-1))
      }
      assertEquals(tape.read(), data.getOrElse(head, BLANK))
      out.append(s"$step $before $action ${tape.read()} ${vm.hops}\n")
      tape.finish()
      emit(vm, b)
    }
    out.append(vm.stats.pythonRepr).append("\n")
    out.toString
  }

  /** The third Python test for one word: load `^word$` on SOURCE, run the marked FPP
    * table on the scaffold, decode MARKS. Returns `(steps, marks, stats)`.
    */
  private def fppOnScaffold(word: String): (Int, Vector[Int], Stats) = {
    val kernel = buildMarkedProgram("ab")
    val vm = new VM
    // Fixture loading is explicit and creates scaffold nodes. The tested
    // finite program starts only after SOURCE has returned to its origin.
    val operations = (LEFT + word + END).flatMap(symbol => Vector(WriteOp(symbol.toString), MoveOp(1))) ++
      Vector.fill(word.length + 2)(MoveOp(-1))
    for (op <- operations) {
      vm.begin()
      val b = new Builder
      val state = new ProgramView(vm, vm.top, b, kernel)
      op match {
        case WriteOp(symbol) => state.tapes(SOURCE).write(symbol)
        case MoveOp(direction) => state.tapes(SOURCE).move(direction)
      }
      state.finish()
      emit(vm, b)
    }
    var started = false
    var steps = 0
    var finished = false
    val watchdog = 500 * (word.length + 1)
    while (!finished && steps < watchdog) {
      vm.begin()
      val b = new Builder
      val state = new ProgramView(vm, vm.top, b, kernel)
      if (!started) {
        state.start()
        started = true
      }
      state.step()
      finished = state.done
      state.finish()
      emit(vm, b)
      steps += 1
    }
    if (!finished) {
      fail("FPP exceeded its fixture watchdog")
    }
    val actual = (0 until word.length).map { _ =>
      vm.begin()
      val b = new Builder
      val state = new ProgramView(vm, vm.top, b, kernel)
      state.tapes(MARKS).move(1)
      val mark = state.tapes(MARKS).read().toInt
      state.finish()
      emit(vm, b)
      mark
    }.toVector
    (steps, actual, vm.stats)
  }

  private val fppWords = Vector("", "a", "abba", "ababa", "aababb", "a" * 31)

  test("two programs are isolated and can drop private scratch") {
    twoPrograms()
  }

  test("private tape matches local array operations") {
    privateTape()
  }

  test("FPP table runs on scaffold private tapes") {
    for (word <- fppWords) {
      val (_, actual, stats) = fppOnScaffold(word)
      val expected = (1 to word.length).map { i =>
        val prefix = word.take(i)
        if (prefix == prefix.reverse) { 1 } else { 0 }
      }.toVector
      assertEquals(actual, expected, word)
      assert(stats.radius < 80, stats)
    }
  }

  test("all three drivers match python: statistics, tape trace, marks") {
    val out = new StringBuilder
    out.append(twoPrograms().pythonRepr).append("\n")
    out.append(privateTape())
    for (word <- fppWords) {
      val (steps, actual, stats) = fppOnScaffold(word)
      out.append(s"'$word' $steps ${actual.mkString("[", ", ", "]")} ${stats.pythonRepr}\n")
    }
    PyDiff.assertSameAsPython(out.toString, "-c",
      """import random
        |from scavm import VM
        |from scavm_structs import Builder, emit
        |from scaffold_program import TapeView, ProgramView
        |from fpp_finite import BLANK, LEFT, END
        |from fpp_subroutine import build_marked_program, SOURCE, MARKS
        |kernel = build_marked_program("ab")
        |vm = VM()
        |for step in range(3):
        |  vm.begin(); b = Builder()
        |  first = ProgramView(vm, vm.top, b, kernel, name="f"); second = ProgramView(vm, vm.top, b, kernel, name="d")
        |  if step == 0:
        |    first.tapes[SOURCE].write("a"); first.tapes[SOURCE].move(1); first.tapes[SOURCE].write("b")
        |    second.tapes[SOURCE].write(LEFT); second.start()
        |  elif step == 1:
        |    first.reset()
        |  first.finalize(); second.finalize(); emit(vm, b)
        |print(vm.stats())
        |random.seed(422)
        |vm, data, head = VM(), {}, 0
        |for step in range(1500):
        |  vm.begin(); b = Builder(); tape = TapeView(vm, vm.top, b, "t"); before = tape.read()
        |  action = random.choice(("write", "left", "right"))
        |  if action == "write":
        |    symbol = random.choice("ab01_"); tape.write(symbol); data[head] = symbol
        |  elif action == "right":
        |    tape.move(1); head += 1
        |  elif head > 0:
        |    tape.move(-1); head -= 1
        |  else:
        |    try: tape.move(-1)
        |    except ValueError: pass
        |  print(step, before, action, tape.read(), vm.hops)
        |  tape.finalize(); emit(vm, b)
        |print(vm.stats())
        |for word in ("", "a", "abba", "ababa", "aababb", "a" * 31):
        |  vm = VM(); operations = []
        |  for symbol in LEFT + word + END: operations.extend((("write", symbol), ("move", 1)))
        |  operations.extend(("move", -1) for _ in range(len(word) + 2))
        |  for op, value in operations:
        |    vm.begin(); b = Builder(); state = ProgramView(vm, vm.top, b, kernel)
        |    getattr(state.tapes[SOURCE], op)(value); state.finalize(); emit(vm, b)
        |  started, steps = False, 0
        |  for _ in range(500 * (len(word) + 1)):
        |    vm.begin(); b = Builder(); state = ProgramView(vm, vm.top, b, kernel)
        |    if not started: state.start(); started = True
        |    state.step(); done = state.done; state.finalize(); emit(vm, b); steps += 1
        |    if done: break
        |  actual = []
        |  for _ in range(len(word)):
        |    vm.begin(); b = Builder(); state = ProgramView(vm, vm.top, b, kernel)
        |    state.tapes[MARKS].move(1); actual.append(int(state.tapes[MARKS].read())); state.finalize(); emit(vm, b)
        |  print(repr(word), steps, actual, vm.stats())
        |""".stripMargin)
  }
}
