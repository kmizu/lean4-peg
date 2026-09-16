package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Finite straight-line blocks between tape reads, with stack-slot ranks.
  * （Python 版: `docs/palindromes-in-peg/read_blocks.py`）
  *
  * A block executes its entry instruction and then all following writes/moves,
  * ending immediately before the next read or halt. Removing incoming edges to
  * read/halt states must leave a DAG; this is checked, not assumed. Slot ranks
  * are longest-path counts for each tape's left/right stack. Instructions with
  * the same rank cannot allocate that stack twice on one path.
  *
  * Python 版は `fpp_finite.Program`（命令タプルの列）と `Execution` をダックタイピングで
  * 受け取る。ここでは必要な形だけを `Instruction` / `Program` / `Execution` として
  * 明示する。`fpp_finite` 側の移植はこれらに適合させる。
  */
object ReadBlocks {

  /** The finite-controller instruction set of `fpp_finite.Program.code`. */
  sealed trait Instruction
  object Instruction {
    /** `("read", tape, {symbol: next_state})` — choices keep insertion order. */
    final case class Read(tape: Int, choices: VectorMap[String, Int]) extends Instruction
    /** `("write", tape, symbol, next_state)` */
    final case class Write(tape: Int, symbol: String, next: Int) extends Instruction
    /** `("move", tape, direction, next_state)` with direction in {-1, +1}. */
    final case class Move(tape: Int, direction: Int, next: Int) extends Instruction
    /** `("emit", next_state)` — not allowed inside read blocks. */
    final case class Emit(next: Int) extends Instruction
    /** `("halt",)` */
    case object Halt extends Instruction
  }

  /** What `analyze` needs from a program. */
  trait Program {
    def code: IndexedSeq[Instruction]
    def ntapes: Int
  }

  /** What `step` needs from a resumable execution (see `fpp_finite.Execution`). */
  trait Execution {
    def program: Program
    def state: Int
    def done: Boolean
    def step(): Unit
  }

  /** The Python result dict.
    *
    * @param order           topological order of the instructions (cut edges removed)
    * @param cuts            indices of the read/halt instructions
    * @param slots           for each move instruction, its stack-slot rank (insertion order)
    * @param bounds          per stack (2 per tape: right stack at 2t, left stack at 2t+1)
    *                        the largest rank reached
    * @param maxInstructions the longest block, in instructions
    */
  final case class Analysis(
      order: Vector[Int],
      cuts: Set[Int],
      slots: VectorMap[Int, Int],
      bounds: Vector[Int],
      maxInstructions: Int
  )

  private def invalid(message: String): Nothing = throw new IllegalArgumentException(message)

  /** Successor states of each instruction, with edges into cuts removed. */
  private def successors(code: IndexedSeq[Instruction], cuts: Set[Int]): Vector[Vector[Int]] = {
    code.toVector.map { row =>
      val targets: Vector[Int] = row match {
        case Instruction.Read(_, choices) => choices.values.toVector.distinct
        case Instruction.Write(_, _, next) => Vector(next)
        case Instruction.Move(_, _, next)  => Vector(next)
        case Instruction.Halt              => Vector.empty
        case Instruction.Emit(_) => invalid("read blocks require read/write/move/halt instructions")
      }
      targets.filterNot(cuts.contains)
    }
  }

  /** Kahn's algorithm; fails unless the cut graph is a DAG. */
  private def topologicalOrder(succ: Vector[Vector[Int]]): Vector[Int] = {
    val incoming = Array.fill(succ.size)(0)
    succ.foreach(_.foreach(target => incoming(target) += 1))
    val queue = mutable.Queue.from(incoming.indices.filter(i => incoming(i) == 0))
    val order = mutable.ArrayBuffer.empty[Int]
    while (queue.nonEmpty) {
      val node = queue.dequeue()
      order += node
      succ(node).foreach { target =>
        incoming(target) -= 1
        if (incoming(target) == 0) { queue.enqueue(target) }
      }
    }
    if (order.size != succ.size) {
      invalid("non-reading instruction cycle has no finite block bound")
    }
    order.toVector
  }

  def analyze(program: Program): Analysis = {
    val code = program.code
    val cuts = code.indices.filter { i =>
      code(i) match {
        case Instruction.Read(_, _) | Instruction.Halt => true
        case _ => false
      }
    }.toSet
    val succ = successors(code, cuts)
    val order = topologicalOrder(succ)
    val stacks = 2 * program.ntapes
    val ranks = Array.fill(code.size)(Array.fill(stacks)(0))
    val slots = mutable.LinkedHashMap.empty[Int, Int]
    val bounds = Array.fill(stacks)(0)
    val lengths = Array.fill(code.size)(0)
    var longest = 0
    order.foreach { node =>
      lengths(node) += 1
      longest = math.max(longest, lengths(node))
      code(node) match {
        case Instruction.Move(tape, direction, _) =>
          val side = 2 * tape + (if (direction == -1) 1 else 0)
          ranks(node)(side) += 1
          slots(node) = ranks(node)(side) - 1
        case _ => ()
      }
      for (side <- 0 until stacks) { bounds(side) = math.max(bounds(side), ranks(node)(side)) }
      succ(node).foreach { target =>
        lengths(target) = math.max(lengths(target), lengths(node))
        ranks(target) = ranks(target).zip(ranks(node)).map { case (a, b) => math.max(a, b) }
      }
    }
    Analysis(order, cuts, VectorMap.from(slots), bounds.toVector, longest)
  }

  /** Independent concrete block semantics on the finite tape interpreter. */
  def step(execution: Execution): Unit = {
    execution.step()
    while (!execution.done && !isCut(execution.program.code(execution.state))) {
      execution.step()
    }
  }

  private def isCut(instruction: Instruction): Boolean = instruction match {
    case Instruction.Read(_, _) | Instruction.Halt => true
    case _ => false
  }
}
