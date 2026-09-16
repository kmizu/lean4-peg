package pal

import Scavm.{Label, Node, NodeRef, Self, VM}
import ScavmStructs.{Builder, RTQueueView, StackView}

/** Clonable readonly online input heads on the bounded-neighbourhood scaffold.
  *
  * Each head has persistent left/right stacks and a realtime incoming queue.
  * Append each arriving input cell to every head once. A head may move left,
  * move right if input is available, or copy another head's complete state.
  * Broadcast each arrival to all heads before client operations. Copies must
  * use views in the same VM/builder with the same current arrival phase.
  * No addresses, lengths, timestamps or equality of node pointers are tested.
  * The only pointer distinctions are empty None and the current builder SELF.
  *
  * Calls per scaffold step must be bounded by the outer finite controller.
  * Input cells carry their character in label['input']; origin is None.
  * This is a component experiment, not a complete PAL SCA or PEG emitter.
  *
  * Python 原典: `scaffold_input.py`。設計と資源勘定は `SCA_INPUT_HEADS.md` を参照。
  * Python の `finalize` は `ScavmStructs` に倣って `finish` に改名した。
  */
object ScaffoldInput {

  /** The protocol of a readonly online head, as the Python modules duck-type it
    * (`InputHead` and `ScaffoldPlaces.PlaceHead`): the scheduler and chain views
    * take any head of one such type. `copyFrom` only aliases heads of the same type.
    */
  trait ReadonlyHead[H <: ReadonlyHead[H]] {

    /** Receive this step's arriving input cell (exactly once per head and step). */
    def append(cell: NodeRef): Unit

    /** The symbol under the head; `None` at the origin (left of the first input). */
    def read(): Option[String]

    /** Whether a move right is possible now (input already available). */
    def canRight: Boolean

    def right(): Unit

    def left(): Unit

    /** Become an O(1) alias of another head's complete state. */
    def copyFrom(other: H): Unit

    /** Python `finalize`: record this head's roots in the node being built. */
    def finish(): Unit
  }

  /** One readonly head: focus pointer, persistent left/right stacks and a realtime
    * incoming queue, all under the name prefix `name` in the scaffold node.
    *
    * @param previous the previous top node (`None` at the first step)
    */
  final class InputHead(val vm: VM, previous: Option[Node], val builder: Builder, val name: String)
      extends ReadonlyHead[InputHead] {

    /** Finite per-view flag: the arrival of this step has been appended. */
    var arrivalReceived: Boolean = false

    /** The cell under the head: `None` at the origin, [[Self]] for a cell created this step. */
    var focus: Option[NodeRef] = vm.get(previous, name + ".focus")

    val leftStack: StackView = new StackView(vm, previous, builder, name + ".l")
    val rightStack: StackView = new StackView(vm, previous, builder, name + ".r")
    val incoming: RTQueueView = new RTQueueView(vm, previous, builder, name + ".in")

    def append(cell: NodeRef): Unit = {
      if (arrivalReceived) {
        throw new IllegalArgumentException("arrival already received in this step")
      }
      incoming.push(Some(cell))
      incoming.work()
      arrivalReceived = true
    }

    /** `label['input']` of the focused cell; `None` at the origin. */
    def read(): Option[String] = {
      focus.flatMap { cell =>
        val value = cell match {
          case Self => builder.label("input")
          case node: Node => vm.label(node)("input")
        }
        value match {
          case Label.Str(symbol) => Some(symbol)
          case Label.Null => None // a work cell carries no input character
          case other => throw new IllegalArgumentException(s"input label is not a symbol: ${other.pythonRepr}")
        }
      }
    }

    def canRight: Boolean = !rightStack.empty || !incoming.empty

    def right(): Unit = {
      if (!canRight) {
        throw new IllegalArgumentException("input not yet available")
      }
      leftStack.push(focus)
      if (!rightStack.empty) {
        focus = rightStack.pop()
      } else {
        // Extra bounded work allows several client operations in one physical
        // step without depending on a once-per-input rotation cadence.
        incoming.work()
        focus = incoming.pop()
        incoming.work()
      }
    }

    def left(): Unit = {
      if (leftStack.empty) {
        throw new IllegalArgumentException("cannot move left of the input origin")
      }
      rightStack.push(focus)
      focus = leftStack.pop()
    }

    /** Alias the focus, both stacks, all seven queue stacks, the two unary counters
      * and the finite queue phase of `other` (see SCA_INPUT_HEADS.md).
      */
    def copyFrom(other: InputHead): Unit = {
      if (!(vm eq other.vm) || !(builder eq other.builder)) {
        throw new IllegalArgumentException("heads must belong to the same scaffold step")
      }
      if (arrivalReceived != other.arrivalReceived) {
        throw new IllegalArgumentException("heads must have received the same arrival")
      }
      focus = other.focus
      leftStack.copyFrom(other.leftStack)
      rightStack.copyFrom(other.rightStack)
      for (role <- RTQueueView.NAMES) {
        incoming.s(role).copyFrom(other.incoming.s(role))
      }
      for ((target, source) <- Seq((incoming.m, other.incoming.m), (incoming.c, other.incoming.c))) {
        target.pos.copyFrom(source.pos)
        target.neg.copyFrom(source.neg)
      }
      incoming.phase = other.incoming.phase
    }

    def finish(): Unit = {
      incoming.work()
      leftStack.finish()
      rightStack.finish()
      incoming.finish()
      builder.ptr(name + ".focus") = focus
    }
  }
}
