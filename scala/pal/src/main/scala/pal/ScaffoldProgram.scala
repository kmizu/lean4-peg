package pal

import Scavm.{Node, Self, VM}
import ScavmStructs.{Builder, StackView}
import FppFinite.{BLANK, Instruction, Program}

/** Run a finite local-tape program on bounded-neighbourhood scaffold cells.
  *
  * Each invocation of step executes one actual finite instruction. It does not
  * make an offline program real time. Tape addresses never enter machine labels;
  * only finite tape symbols and a program counter from the supplied finite table
  * do. The independent VM enforces backward/self pointer reachability.
  *
  * Python 原典: `scaffold_program.py`（`SCA_ONLINE_CONTROL.md` "Private tape
  * execution"）。Python の `finalize` は `finish`。
  */
object ScaffoldProgram {

  /** A private persistent tape: a focus symbol plus two persistent stacks. Cell
    * contents live in the label `<name>.v<slot>` of the node that created the cell;
    * the stacks hold `(node, slot)` references to those cells.
    */
  final class TapeView(val vm: VM, previous: Option[Node], val builder: Builder, val name: String) {

    var focus: String = previous.fold(BLANK)(p => vm.label(p)(name + ".symbol").asStr)

    val left: StackView = new StackView(vm, previous, builder, name + ".l")
    val right: StackView = new StackView(vm, previous, builder, name + ".r")

    def read(): String = focus

    def write(symbol: String): Unit = {
      focus = symbol
    }

    /** Drop this private persistent tape in bounded work, including its origin. */
    def reset(): Unit = {
      focus = BLANK
      left.top = None
      right.top = None
    }

    /** Unit move: park the focus in a fresh cell of the node being built, then take
      * the focus from the stack on the other side (blank beyond the visited prefix).
      */
    def move(direction: Int): Unit = {
      if (direction != -1 && direction != 1) {
        throw new IllegalArgumentException("unit tape move required")
      }
      if (direction == -1 && left.empty) {
        throw new IllegalArgumentException("left-end crossing")
      }
      val (pushed, popped) = if (direction == 1) { (left, right) } else { (right, left) }
      val slot = builder.slot(name + ".v")
      builder.label(s"$name.v$slot") = focus
      pushed.push(Some(Self), slot)
      if (popped.empty) {
        focus = BLANK
      } else {
        val (cell, vslot) = popped.pop2()
        focus = cellSymbol(cell, vslot)
      }
    }

    /** The symbol parked in cell `(node, vslot)`; the node is [[Self]] for a cell of this step. */
    private def cellSymbol(cell: Option[Scavm.NodeRef], vslot: Int): String = {
      val key = s"$name.v$vslot"
      cell match {
        case Some(Self) => builder.label(key).asStr
        case Some(node: Node) => vm.label(node)(key).asStr
        case None => throw new IllegalStateException(s"tape $name: cell without a creator")
      }
    }

    def finish(): Unit = {
      left.finish()
      right.finish()
      builder.label(name + ".symbol") = focus
    }
  }

  /** A finite program executing on private tapes: the tapes, the program counter
    * and the halted flag, all under the optional prefix `name`.
    *
    * @param name separates simultaneous programs' tape and control fields (`""` = none)
    */
  final class ProgramView(val vm: VM, previous: Option[Node], val builder: Builder, val program: Program, name: String = "") {

    val prefix: String = if (name.nonEmpty) { name + "." } else { "" }

    val tapes: Vector[TapeView] =
      (0 until program.ntapes).map(i => new TapeView(vm, previous, builder, s"${prefix}t$i")).toVector

    var pc: Int = previous.fold(program.start)(p => vm.label(p)(prefix + "pc").asStr.toInt)

    var done: Boolean = previous.fold(true)(p => vm.label(p)(prefix + "halted").asBool)

    /** Drop every private tape and return to the start state, halted.
      *
      * The finite table fixes the number of tapes. No scan or mutation of
      * retained nodes is needed in the persistent scaffold representation.
      */
    def reset(): Unit = {
      for (tape <- tapes) {
        tape.reset()
      }
      pc = program.start
      done = true
    }

    /** Begin running at the program's start state. */
    def start(): Unit = start(program.start)

    /** Begin running at the finite state `entry`. */
    def start(entry: Int): Unit = {
      pc = entry
      done = false
    }

    /** Execute exactly one instruction of the table. */
    def step(): Unit = {
      if (done) {
        throw new IllegalArgumentException("program is not running")
      }
      program.instruction(pc) match {
        case Instruction.Halt =>
          done = true
        case Instruction.Read(tape, choices) =>
          pc = choices(tapes(tape).read())
        case Instruction.Write(tape, symbol, next) =>
          tapes(tape).write(symbol)
          pc = next
        case Instruction.Move(tape, direction, next) =>
          tapes(tape).move(direction)
          pc = next
        case Instruction.Emit(_) =>
          throw new IllegalArgumentException("observer-only instruction is not a scaffold operation")
      }
    }

    def finish(): Unit = {
      for (tape <- tapes) {
        tape.finish()
      }
      builder.label(prefix + "pc") = pc.toString
      builder.label(prefix + "halted") = done
    }

    /** Whether the current instruction ends a read block (`read` or `halt`). */
    private def atReadOrHalt: Boolean = {
      program.instruction(pc) match {
        case Instruction.Read(_, _) | Instruction.Halt => true
        case _ => false
      }
    }

    /** Execute one read plus its finite following write/move block.
      *
      * Callers must use a table accepted by read_blocks.analyze. The loop bound
      * is the fixed table size, never a tape value or an input-dependent length.
      */
    def stepReadBlock(): Unit = {
      step()
      // Python: `for _ in range(len(code)): if done or at read/halt: return; step()`,
      // then raise — so the boundary is tested at most `len(code)` times.
      val settled = program.code.indices.exists { _ =>
        val atBoundary = done || atReadOrHalt
        if (!atBoundary) {
          step()
        }
        atBoundary
      }
      if (!settled) {
        throw new IllegalArgumentException("non-reading instruction cycle")
      }
    }
  }
}
