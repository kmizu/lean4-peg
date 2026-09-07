package pal

import scala.collection.mutable

import Action.{Call, Emit, Return}
import Coroutine.Local

/** All palindrome-prefix flags, with finite control and local head operations.
  *
  * The input view is `u # reverse(u)`. Upper/Lower are pre-established endpoint
  * heads; no integer lengths enter the generated control. The observer below
  * still preloads the view and endpoints and therefore is not a PAL SCA.
  *
  * Port of `gs_flag_heads.py`.
  */
object GsFlagHeads {
  import Event.*
  import GsHeads.{BLIND, HEADS, HeadGenerator, borderController, compileController, unitMoves}

  val FLAG_HEADS: Vector[String] = HEADS ++ Vector("Lower", "Upper", "Cursor")

  val FLAG_BLIND: Set[String] = BLIND ++ Set("Lower", "Upper", "Cursor")

  /** `flag_controller(k)`: place `Cursor` on the longest proper prefix and run
    * the border controller in flag mode unless the interval is empty.
    */
  final class FlagController(k: Int) extends HeadGenerator[Unit]("flag_controller") {
    override def locals: Vector[(String, Local)] = Vector("k" -> k)

    protected def step(response: Option[Boolean]): Action[Event, Unit] = {
      site match {
        case 0 =>
          site = 1
          Emit(copy("Cursor", "Upper"))
        case 1 =>
          site = 2
          Emit(move(Movement("Cursor", -1)))
        case 2 =>
          site = 3
          Emit(less("Cursor", "Lower"))
        case 3 =>
          if (!response.get) {
            site = 4
            Call(borderController(k, flags = true))
          } else {
            Return(())
          }
        case _ => Return(())
      }
    }
  }

  def flagController(k: Int = 8): FlagController = new FlagController(k)

  def compileFlags(k: Int = 8): Program = {
    unitMoves(compileController(k, controller = k => flagController(k)))
  }
}

/** Observer for the flag worker on the view `u # reverse(u)`; collects the
  * emitted flag bits (`runFlags`).
  */
class FlagVM(word: String, lower: Int, upper: Int, program: Option[Program] = None)
  extends HeadVM[Option[Char]](new PalindromeView(word.toIndexedSeq), program.getOrElse(GsFlagHeads.compileFlags())) {
  import Event.*
  import GsFlagHeads.FLAG_BLIND
  import GsHeads.BLIND

  if (!(0 <= lower && lower <= upper && upper <= word.length + 1)) {
    throw new IllegalArgumentException("invalid flag interval")
  }
  positions("Lower") = lower
  positions("Upper") = upper
  positions("Cursor") = 0

  protected val flagBuffer: mutable.ArrayBuffer[Boolean] = mutable.ArrayBuffer.empty

  /** The flag bits emitted so far, longest length first. */
  def flags: Vector[Boolean] = flagBuffer.toVector

  override def step(): Unit = {
    val Row(event, targets) = current
    event match {
      case Flag(value) =>
        flagBuffer += value
        state = targets(0)
        steps += 1
      case Move(moves) if moves.exists(movement => FLAG_BLIND.contains(movement.head) && !BLIND.contains(movement.head)) =>
        moves.foreach { case Movement(head, delta) =>
          positions(head) += delta
          motion += math.abs(delta)
        }
        state = targets(0)
        steps += 1
      case _ => super.step()
    }
  }

  /** Run to `halt` and return the flags (Python's `FlagVM.run`). */
  def runFlags(watchdog: Option[Long] = None): Vector[Boolean] = {
    run(watchdog)
    flags
  }
}
