package pal

import Scavm.{Node, NodeRef, VM}
import ScavmStructs.Builder
import ScaffoldInput.{InputHead, ReadonlyHead}

/** Readonly Galil places: binary letters at odd places, virtual gaps at even.
  *
  * There is no padded external input. A finite phase bit distinguishes a letter
  * from the gap immediately after it. InputHead still receives each real arrival
  * exactly once. A gap becomes available together with its preceding letter.
  *
  * Python 原典: `scaffold_places.py`（`SCA_ONLINE_CONTROL.md` "Virtual places on
  * unchanged input"）。
  */
object ScaffoldPlaces {

  /** The symbol read at every gap place. */
  val GAP: String = "s"

  /** One phase bit `gap` over an [[InputHead]]: place `2i+1` is letter `i` with
    * `gap = false`, place `2i+2` is the gap after it with `gap = true`; the origin
    * (place 0) is the head's origin with `gap = true`.
    */
  final class PlaceHead(val vm: VM, previous: Option[Node], val builder: Builder, val name: String)
      extends ReadonlyHead[PlaceHead] {

    val head: InputHead = new InputHead(vm, previous, builder, name)

    var gap: Boolean = previous.fold(true)(p => vm.label(p)(name + ".gap").asBool)

    def append(cell: NodeRef): Unit = head.append(cell)

    /** The letter, [[GAP]] at a gap place, `None` at the origin. */
    def read(): Option[String] = head.read().map(symbol => if (gap) { GAP } else { symbol })

    def canRight: Boolean = !gap || head.canRight

    def right(): Unit = {
      if (gap) {
        head.right()
      }
      gap = !gap
    }

    def left(): Unit = {
      if (head.read().isEmpty) {
        throw new IllegalArgumentException("cannot move left of the input origin")
      }
      if (!gap) {
        head.left()
      }
      gap = !gap
    }

    /** Whether this head is at place 1, the first letter. */
    def isFirst: Boolean = !gap && !head.leftStack.empty && head.leftStack.peek.isEmpty

    def copyFrom(other: PlaceHead): Unit = {
      head.copyFrom(other.head)
      gap = other.gap
    }

    def finish(): Unit = {
      head.finish()
      builder.label(name + ".gap") = gap
    }
  }
}
