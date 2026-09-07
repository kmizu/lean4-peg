package pal

import scala.collection.mutable
import Expr.{TRUE, FALSE}
import Ref.PREVIOUS
import ScaffoldCircuit.*
import FppFinite.{BLANK, Instruction}

/** Lower real finite FPP/DP instruction tables to symbolic scaffold equations.
  * Tape symbols are Strings (as in FppFinite); input heads expose Chars.
  */
object ScaffoldCircuitProgram {
  /** Adapter between the finite kernel and the independent read-block analysis. */
  def readBlockProgram(kernel: FppFinite.Program): ReadBlocks.Program = new ReadBlocks.Program {
    val ntapes: Int = kernel.ntapes
    val code: Vector[ReadBlocks.Instruction] = kernel.instructions.map {
      case Instruction.Halt => ReadBlocks.Instruction.Halt
      case Instruction.Read(tape, choices) => ReadBlocks.Instruction.Read(tape, choices)
      case Instruction.Write(tape, symbol, next) => ReadBlocks.Instruction.Write(tape, symbol, next)
      case Instruction.Move(tape, direction, next) => ReadBlocks.Instruction.Move(tape, direction, next)
      case Instruction.Emit(next) => ReadBlocks.Instruction.Emit(next)
    }
  }

  final class Program(val circuit: Circuit, val kernel: FppFinite.Program, val name: String,
                      val quantum: Int = 1, extraSymbols: Map[Int, Seq[String]] = Map.empty,
                      coarse: Boolean = false, sharedCells: Boolean = false, extraMoves: Int = 0) {
    val blocks: Option[ReadBlocks.Analysis] = if (coarse) { Some(ReadBlocks.analyze(readBlockProgram(kernel))) } else { None }
    private val code = kernel.instructions
    private val alphabets = Array.tabulate(kernel.ntapes)(t => mutable.Set.from(Vector(BLANK) ++ extraSymbols.getOrElse(t, Nil)))
    code.foreach {
      case Instruction.Read(tape, choices) => alphabets(tape) ++= choices.keys
      case Instruction.Write(tape, symbol, _) => alphabets(tape) += symbol
      case _ => ()
    }
    if (sharedCells && coarse) {
      throw new IllegalArgumentException("shared instruction cells require one raw instruction per step")
    }
    val sharedPool: Option[StackPool] = if (sharedCells) {
      val pool = new StackPool(circuit, Vector("cells" -> (quantum + extraMoves)), alphabets.iterator.flatten.toVector.distinct.sorted)
      // Controller moves use distinct slots after the instruction prefix.
      pool.used("cells") = quantum
      Some(pool)
    } else { None }
    var instructionIndex: Int = 0
    val tapes: Vector[Tape] = Vector.tabulate(kernel.ntapes) { t =>
      val alphabet = alphabets(t).toVector.sorted
      blocks match {
        case None => new Tape(circuit, s"$name.t$t", alphabet, quantum, BLANK, sharedPool)
        case Some(b) => Tape.withSides(circuit, s"$name.t$t", alphabet,
          (math.max(1, quantum * b.bounds(2 * t)), math.max(1, quantum * b.bounds(2 * t + 1))), BLANK, sharedPool)
      }
    }
    val pcKey: String = name + ".pc"
    val doneKey: String = name + ".done"
    var pc: Value[Int] = circuit.get(PREVIOUS, pcKey, code.indices.toVector, kernel.start)
    var done: Expr = circuit.get(PREVIOUS, doneKey, Vector(false, true), true).eqTo(true)

    def start(enabled: Expr = TRUE, entry: Option[Int] = None): Unit = {
      pc = Value.select(enabled, Value.constant(entry.getOrElse(kernel.start)), pc)
      done = choose(enabled, FALSE, done)
    }

    def reset(enabled: Expr = TRUE): Unit = {
      tapes.foreach(_.reset(enabled))
      pc = Value.select(enabled, Value.constant(kernel.start), pc)
      done = choose(enabled, TRUE, done)
    }

    def step(enabled: Expr = TRUE): Unit = {
      if (blocks.isEmpty) { instructionStep(enabled) } else { blockStep(enabled) }
    }

    def instructionStep(enabled: Expr = TRUE): Unit = {
      val slot = sharedPool.map { _ =>
        if (instructionIndex >= quantum) { throw new IllegalArgumentException("finite instruction cell layout exhausted") }
        val index = instructionIndex
        instructionIndex += 1
        index
      }
      val active = conjunction(enabled, neg(done))
      val events = code.indices.map(i => conjunction(active, pc.eqTo(i)))
      val nextPc = mutable.LinkedHashMap.empty[Int, Expr]
      val halts = mutable.ArrayBuffer.empty[Expr]
      val writes = Array.fill(tapes.size)(mutable.LinkedHashMap.empty[String, Expr])
      val moves = Array.fill(tapes.size)(Map(-1 -> mutable.ArrayBuffer.empty[Expr], 1 -> mutable.ArrayBuffer.empty[Expr]))
      def forward(target: Int, event: Expr): Unit = { nextPc(target) = disjunction(nextPc.getOrElse(target, FALSE), event) }
      for ((event, row) <- events.zip(code)) {
        row match {
          case Instruction.Halt => halts += event
          case Instruction.Read(tape, choices) =>
            choices.foreach { case (symbol, target) => forward(target, conjunction(event, tapes(tape).focus.eqTo(symbol))) }
          case Instruction.Write(tape, symbol, target) =>
            forward(target, event)
            writes(tape)(symbol) = disjunction(writes(tape).getOrElse(symbol, FALSE), event)
          case Instruction.Move(tape, direction, target) =>
            forward(target, event)
            moves(tape)(direction) += event
          case Instruction.Emit(_) =>
            throw new IllegalArgumentException("only finite read/write/move/halt instructions can be lowered")
        }
      }
      for (t <- tapes.indices) {
        if (writes(t).nonEmpty) { tapes(t).write(Value(writes(t)), disjunction(writes(t).values.toSeq*)) }
        tapes(t).move(-1, disjunction(moves(t)(-1).toSeq*), slot)
        tapes(t).move(1, disjunction(moves(t)(1).toSeq*), slot)
      }
      val halt = disjunction(halts.toSeq*)
      pc = Value.select(conjunction(active, neg(halt)), Value(nextPc), pc)
      done = disjunction(done, halt)
    }

    def blockStep(enabled: Expr = TRUE): Unit = {
      val analysis = blocks.getOrElse(throw new IllegalStateException("read-block analysis required"))
      val active = conjunction(enabled, neg(done))
      val events = code.indices.map(i => conjunction(active, pc.eqTo(i))).toArray
      val nextPc = mutable.LinkedHashMap.empty[Int, Expr]
      val halts = mutable.ArrayBuffer.empty[Expr]
      val bases = tapes.map(tape => Vector(tape.left, tape.right).map(stack => stack.pool.used.getOrElse(stack.name, 0)))
      def forward(target: Int, event: Expr): Unit = {
        if (analysis.cuts(target)) { nextPc(target) = disjunction(nextPc.getOrElse(target, FALSE), event) }
        else { events(target) = disjunction(events(target), event) }
      }
      for (state <- analysis.order) {
        val event = events(state)
        code(state) match {
          case Instruction.Halt => halts += event
          case Instruction.Read(tape, choices) =>
            choices.foreach { case (symbol, target) => forward(target, conjunction(event, tapes(tape).focus.eqTo(symbol))) }
          case Instruction.Write(tape, symbol, target) =>
            tapes(tape).write(Value.constant(symbol), event)
            forward(target, event)
          case Instruction.Move(tape, direction, target) =>
            val side = if (direction == -1) { 1 } else { 0 }
            tapes(tape).move(direction, event, Some(bases(tape)(side) + analysis.slots(state)))
            forward(target, event)
          case Instruction.Emit(_) => throw new IllegalArgumentException("read blocks require read/write/move/halt instructions")
        }
      }
      val halt = disjunction(halts.toSeq*)
      circuit.require(disjunction((halt +: nextPc.values.toVector)*), active)
      pc = Value.select(conjunction(active, neg(halt)), Value(nextPc), pc)
      done = disjunction(done, halt)
    }

    def commit(): Unit = {
      tapes.foreach(_.commit())
      circuit.put(pcKey, pc)
      circuit.put(doneKey, Value.select(done, Value.constant(true), Value.constant(false)))
    }
  }
}
