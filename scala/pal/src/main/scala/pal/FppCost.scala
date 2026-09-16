package pal

import scala.collection.mutable

import FppFinite.*
import FppFinite.Instruction.*

/** Structural cost bounds for the finite FPP tables, in local instructions.
  *
  * The control-graph factor is computed. The resource bounds are the symbolic
  * tape-motion ledger documented in FPP_COST.md, not fitted trace maxima. The
  * observer below makes each ledger obligation separately testable; it supplies
  * no runtime operation to the finite machine.
  *
  * Python 原典: `fpp_cost.py`。
  */
object FppCost {

  def successors(row: Instruction): Seq[Int] = row match {
    case Read(_, choices) => choices.values.toSeq
    case Halt => Nil
    case Emit(next) => Seq(next)
    case Move(_, _, next) => Seq(next)
    case Write(_, _, next) => Seq(next)
  }

  /** Instructions that are charged to a tape-motion resource: moves, queue-front reads, outputs, halt. */
  def isCut(row: Instruction): Boolean = row match {
    case Move(_, _, _) | Emit(_) | Halt => true
    case Read(FRONT, _) => true
    case _ => false
  }

  /** Maximum instructions through the next charged instruction, inclusive.
    *
    * Cutting moves, queue-front reads, outputs and halt makes the remaining
    * graph acyclic. A non-cut cycle is an error, never a guessed finite bound.
    */
  def cutDistance(program: Program): Int = {
    val visiting = mutable.HashSet.empty[Int]
    val distances = mutable.HashMap.empty[Int, Int]

    def distance(q: Int): Int = {
      distances.get(q) match {
        case Some(d) => d
        case None =>
          if (visiting.contains(q)) {
            throw new IllegalArgumentException("uncharged cycle in finite FPP control graph")
          }
          visiting += q
          val row = program.instruction(q)
          val value = if (isCut(row)) { 1 } else { 1 + successors(row).map(distance).max }
          visiting -= q
          distances(q) = value
          value
      }
    }

    program.code.indices.map(distance).max
  }

  /** `slope * size + intercept`, defined on nonnegative sizes only. */
  final case class Affine(slope: Int, intercept: Int = 0) {
    def apply(size: Int): Int = {
      if (size < 0) {
        throw new IllegalArgumentException("nonnegative integral size required")
      }
      slope * size + intercept
    }
  }

  /** Per-tape move bounds, indexed by A, B, C, S, T, BACK, FRONT. */
  val MOVE_BOUNDS: Vector[Affine] = Vector(
    Affine(4, 0), Affine(1, 0), Affine(6, 1), Affine(7, 1), Affine(2, 0), Affine(4, 0), Affine(4, 0))
  val FRONT_READS: Affine = Affine(4)
  val EMITS: Affine = Affine(1)
  val PREPARATION: Affine = Affine(24, 42)
  val DP_SCAN: Affine = Affine(18, 25)

  /** Python の `bounds()` が返す dict。 */
  final case class Bounds(factor: Int, kernel: Affine, marked: Affine, dp: Affine)

  def bounds(alphabet: String = "abs"): Bounds = {
    val factor = cutDistance(buildProgram(alphabet + "#"))
    val moves = Affine(MOVE_BOUNDS.map(_.slope).sum, MOVE_BOUNDS.map(_.intercept).sum)
    val cuts = Affine(moves.slope + FRONT_READS.slope + EMITS.slope,
      moves.intercept + 1) // the final halt
    val kernel = Affine(factor * cuts.slope, factor * cuts.intercept)
    // MARKS follows every A movement. Its emit-to-write replacement costs
    // exactly one instruction, just as the original emit does.
    val markedKernel = Affine(kernel.slope + MOVE_BOUNDS(A).slope, kernel.intercept)
    val marked = Affine(2 * markedKernel.slope + PREPARATION.slope,
      markedKernel.slope + markedKernel.intercept + PREPARATION.intercept)
    // SECOND duplicates MARKS: setup is 3m+4, then A moves plus emits on
    // N=2m+1. The FPP halt is replaced by one read, with the same unit cost.
    val duplicate = Affine(3 + 2 * (MOVE_BOUNDS(A).slope + EMITS.slope),
      4 + MOVE_BOUNDS(A).slope + EMITS.slope)
    val dp = Affine(marked.slope + duplicate.slope + DP_SCAN.slope,
      marked.intercept + duplicate.intercept + DP_SCAN.intercept)
    Bounds(factor, kernel, marked, dp)
  }

  /** Counts the charged instructions of one execution and checks them against the ledger. */
  final class CostObservation {
    val moves: Array[Int] = Array.fill(7)(0)
    var frontReads: Int = 0
    var emits: Int = 0
    var halts: Int = 0
    var steps: Int = 0
    var cuts: Int = 0

    def observe(row: Instruction): Unit = {
      steps += 1
      if (isCut(row)) { cuts += 1 }
      row match {
        case Move(tape, _, _) => moves(tape) += 1
        case Read(FRONT, _) => frontReads += 1
        case Emit(_) => emits += 1
        case Halt => halts += 1
        case _ => ()
      }
    }

    def check(size: Int, factor: Int): Unit = {
      for ((bound, tape) <- MOVE_BOUNDS.zipWithIndex) {
        assert(moves(tape) <= bound(size), (tape, size, moves.toVector, bound))
      }
      assert(frontReads <= FRONT_READS(size), (size, frontReads))
      assert(emits <= EMITS(size) && halts == 1)
      assert(steps <= factor * cuts, (steps, factor, cuts))
    }
  }
}
