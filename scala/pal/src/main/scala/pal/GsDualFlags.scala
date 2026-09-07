package pal

import scala.collection.mutable

/** GS overlaps of u and reverse(u), without the separator mirror word.
  *
  * Pattern and text heads have the same coordinate interval [0, len(u)] but
  * different read views. Copies preserve the view; moves change only position.
  * Proper overlaps are exactly palindrome prefixes shorter than u. This saves
  * the doubled preprocessing length of u # reverse(u).
  *
  * Port of `gs_dual_flags.py`; see "Two oriented views" in `GS_LOCAL_CLOCK.md`.
  */
object GsDualFlags {
  import GsHeads.{HEADS, compileController, unitMoves}

  val DUAL_HEADS: Vector[String] = HEADS ++ Vector("TextOrigin", "Lower", "Upper", "Cursor")

  /** `dual_flag_controller(k)`: like `flag_controller`, with the text starting
    * at `TextOrigin` (the reverse view).
    */
  final class DualFlagController(k: Int) extends GsFlagHeads.FlagController(k, "dual_flag_controller", "TextOrigin")

  def dualFlagController(k: Int = 8): DualFlagController = new DualFlagController(k)

  def compileDualFlags(k: Int = 8, unit: Boolean = true): Program = {
    val program = compileController(k, controller = k => dualFlagController(k))
    if (unit) unitMoves(program) else program
  }
}

/** Observer for the two-view flag worker: heads carry an orientation besides a
  * coordinate; reverse-oriented heads read `u` from its end.
  */
class DualFlagVM(word: String, lower: Int, upper: Int, program: Option[Program] = None)
  extends HeadVM[Char](word.toIndexedSeq, program.getOrElse(GsDualFlags.compileDualFlags())) {
  import Event.*
  import GsDualFlags.DUAL_HEADS
  import GsFlagHeads.FLAG_BLIND

  if (!(0 <= lower && lower <= upper && upper <= word.length)) {
    throw new IllegalArgumentException("the proper-prefix interval must satisfy 0 <= lower <= upper <= len(u)")
  }
  positions("TextOrigin") = 0
  positions("Lower") = lower
  positions("Upper") = upper
  positions("Cursor") = 0

  /** Orientation of each head: `true` reads the reversed view. */
  val reverse: mutable.LinkedHashMap[String, Boolean] = mutable.LinkedHashMap.from(DUAL_HEADS.map(_ -> false))
  reverse("OriginalEnd") = true
  reverse("TextOrigin") = true

  protected val flagBuffer: mutable.ArrayBuffer[Boolean] = mutable.ArrayBuffer.empty

  /** The flag bits emitted so far, longest length first. */
  def flags: Vector[Boolean] = flagBuffer.toVector

  private def read(head: String): Char = {
    val position = positions(head)
    if (FLAG_BLIND.contains(head) || !(0 <= position && position < word.length)) {
      throw new AssertionError(("invalid oriented-head read", head, position, word.length).toString)
    }
    if (reverse(head)) word(word.length - 1 - position) else word(position)
  }

  override def step(): Unit = {
    val Row(event, targets) = current
    event match {
      case Symbols(left, right) =>
        val same = read(left) == read(right)
        comparisons += 1
        steps += 1
        state = targets(if (same) 1 else 0)
      case Copy(target, source) =>
        positions(target) = positions(source)
        reverse(target) = reverse(source)
        steps += 1
        state = targets(0)
      case Move(moves) =>
        moves.foreach { case Movement(head, delta) =>
          positions(head) += delta
          motion += math.abs(delta)
          if (!FLAG_BLIND.contains(head) && !(0 <= positions(head) && positions(head) <= word.length)) {
            throw new AssertionError(("oriented head left its view", head, positions(head)).toString)
          }
        }
        steps += 1
        state = targets(0)
      case Flag(value) =>
        flagBuffer += value
        steps += 1
        state = targets(0)
      case _ => super.step()
    }
  }

  /** Run to `halt` and return the flags (Python's `DualFlagVM.run`). */
  def runFlags(watchdog: Option[Long] = None): Vector[Boolean] = {
    run(watchdog)
    flags
  }
}
