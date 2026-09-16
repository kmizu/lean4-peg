package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Scavm.{Label, LabelMap, Node, NodeRef, Self, Stats, VM, sameTarget}

/** Library structures on the scaffolding VM: stacks, unary counters and a real-time
  * queue (Hood & Melville 1981), all built from the one-node-per-step discipline.
  *
  * Every structure keeps its state in the fields of the current top node under a name
  * prefix.  Within one step, a structure is manipulated through a *view* that reads
  * the previous top (via vm.get, one hop each) and writes the new node's fields into a
  * Builder; `finish` (Python: `finalize`) records the new top of the structure.  Cells
  * created this step live in the new node and are addressed with SELF; several cells of
  * the same stack may be created in one step, distinguished by a slot index.
  *
  * Stack cell (node, k): pointer `<n>.<k>.val`, pointer `<n>.<k>.below`, label
  * `<n>.<k>.bslot`.  Stack top: pointer `<n>.top`, label `<n>.tslot` (None = empty).
  *
  * Counter: two stacks `pos`, `neg` (values unused); value = |pos| - |neg|.
  *
  * RTQueue: front stack F, rear stack B, and during a rotation the reversed copies
  * Fr, Br, the rotation walkers WF, WB over the immutable F and B chains, the new rear
  * B2, and counters m (elements of F not yet popped live) and c (lenF - lenB, with
  * elements in rotation counted as front).  ROT units of rotation work per step.
  *
  * Python 版 `scavm_structs.py` の移植。`finalize` は `java.lang.Object#finalize` と
  * 衝突するので `finish` に改名した。
  */
object ScavmStructs {

  /** The fields of the node being built this step: labels, pointers, and the next free
    * slot index per structure name.
    */
  final class Builder {
    val label: LabelMap = new LabelMap
    val ptr: mutable.LinkedHashMap[String, Option[NodeRef]] = mutable.LinkedHashMap.empty
    private val slots = mutable.LinkedHashMap.empty[String, Int] // name -> next free slot index in the new node

    def slot(name: String): Int = {
      val k = slots.getOrElse(name, 0)
      slots(name) = k + 1
      k
    }
  }

  /** A cell reference (node, creator-name, slot): cells keep the field names of the
    * stack that created them, so aliasing chains (`copyFrom`) is sound.
    */
  final case class StackCell(node: NodeRef, creator: String, slot: Int)

  /** A stack manipulated during one step.  `top` is (node, creator, slot) or None; node
    * may be SELF for cells created this step.
    */
  final class StackView(val vm: VM, val prev: Option[Node], val b: Builder, val name: String) {

    var top: Option[StackCell] = prev match {
      case None => None
      case Some(p) =>
        val node = vm.get(p, name + ".top")
        val lab = vm.label(p)
        node.map(n => StackCell(n, lab(name + ".tname").asStr, lab(name + ".tslot").asInt))
    }

    private def cellKey(cell: StackCell, field: String): String = s"${cell.creator}.${cell.slot}.$field"

    /** Python `_cell` for the pointer fields `val` / `below`. */
    private def cellPtr(cell: StackCell, field: String): Option[NodeRef] = {
      val key = cellKey(cell, field)
      cell.node match {
        case Self => b.ptr(key)
        case node: Node => vm.get(node, key)
      }
    }

    /** Python `_cell` for the label fields `vs` / `bname` / `bslot`. */
    private def cellLabel(cell: StackCell, field: String): Label = {
      val key = cellKey(cell, field)
      cell.node match {
        case Self => b.label(key)
        case node: Node => vm.label(node)(key)
      }
    }

    private def topCell: StackCell = top.getOrElse(throw new NoSuchElementException(s"stack $name is empty"))

    private def cellBelow(cell: StackCell): Option[StackCell] = {
      cellPtr(cell, "below").map { below =>
        StackCell(below, cellLabel(cell, "bname").asStr, cellLabel(cell, "bslot").asInt)
      }
    }

    def empty: Boolean = top.isEmpty

    def peek: Option[NodeRef] = cellPtr(topCell, "val")

    def pop(): Option[NodeRef] = {
      val cell = topCell
      val v = cellPtr(cell, "val")
      top = cellBelow(cell)
      v
    }

    /** pop returning (node, vslot): the value may address a cell (node, slot). */
    def pop2(): (Option[NodeRef], Int) = {
      val vs = cellLabel(topCell, "vs").asInt
      (pop(), vs)
    }

    def peek2: (Option[NodeRef], Int) = {
      val cell = topCell
      (cellPtr(cell, "val"), cellLabel(cell, "vs").asInt)
    }

    /** (node, vslot) of the cell below the top, or None if the top is alone. */
    def belowOfTop: Option[(Option[NodeRef], Int)] = {
      cellBelow(topCell).map(bel => (cellPtr(bel, "val"), cellLabel(bel, "vs").asInt))
    }

    def push(v: Option[NodeRef], vslot: Int = 0): Unit = {
      val k = b.slot(name)
      b.ptr(s"$name.$k.val") = v
      b.label(s"$name.$k.vs") = vslot
      top match {
        case None =>
          b.ptr(s"$name.$k.below") = None
          b.label(s"$name.$k.bname") = ""
          b.label(s"$name.$k.bslot") = 0
        case Some(cell) =>
          b.ptr(s"$name.$k.below") = Some(cell.node)
          b.label(s"$name.$k.bname") = cell.creator
          b.label(s"$name.$k.bslot") = cell.slot
      }
      top = Some(StackCell(Self, name, k))
    }

    /** make this stack an alias of another stack's current chain (O(1)). */
    def copyFrom(other: StackView): Unit = {
      top = other.top
    }

    /** Python `finalize`: record the stack top in the new node. */
    def finish(): Unit = {
      top match {
        case None =>
          b.ptr(name + ".top") = None
          b.label(name + ".tname") = ""
          b.label(name + ".tslot") = 0
        case Some(cell) =>
          b.ptr(name + ".top") = Some(cell.node)
          b.label(name + ".tname") = cell.creator
          b.label(name + ".tslot") = cell.slot
      }
    }
  }

  /** A unary counter: two stacks `pos`, `neg` (values unused); value = |pos| - |neg|. */
  final class CounterView(vm: VM, prev: Option[Node], b: Builder, name: String) {
    val pos: StackView = new StackView(vm, prev, b, name + ".pos")
    val neg: StackView = new StackView(vm, prev, b, name + ".neg")

    def inc(): Unit = {
      if (!neg.empty) { neg.pop() } else { pos.push(None) }
    }

    def dec(): Unit = {
      if (!pos.empty) { pos.pop() } else { neg.push(None) }
    }

    def sign: Int = {
      if (!pos.empty) { 1 } else if (!neg.empty) { -1 } else { 0 }
    }

    def reset(): Unit = {
      pos.top = None
      neg.top = None
    }

    def finish(): Unit = {
      pos.finish()
      neg.finish()
    }
  }

  /** rotation units per step */
  val ROT: Int = 3

  object RTQueueView {
    val NAMES: Vector[String] = Vector("F", "B", "Fr", "Br", "WF", "WB", "B2")

    /** The rotation phase, stored in the label `<name>.phase` as `'idle' | 'rev' | 'copy'`. */
    enum Phase(val label: String) {
      case Idle extends Phase("idle")
      case Rev extends Phase("rev")
      case Copy extends Phase("copy")
    }

    object Phase {
      def fromLabel(label: Label): Phase = {
        val s = label.asStr
        values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown phase '$s'"))
      }
    }
  }

  /** A real-time queue (Hood & Melville) manipulated during one step. */
  final class RTQueueView(val vm: VM, prev: Option[Node], val b: Builder, val name: String) {
    import RTQueueView.Phase

    /** the seven stacks, by role name, in `NAMES` order */
    val s: VectorMap[String, StackView] = VectorMap.from(
      RTQueueView.NAMES.map(n => n -> new StackView(vm, prev, b, s"$name.$n"))
    )
    val m: CounterView = new CounterView(vm, prev, b, name + ".m")
    val c: CounterView = new CounterView(vm, prev, b, name + ".c")
    var phase: Phase = prev match {
      case None => Phase.Idle
      case Some(p) => Phase.fromLabel(vm.label(p)(name + ".phase"))
    }

    private def front: StackView = s("F")

    // --- client operations (at most one push and one pop per step) ---------------

    def push(v: Option[NodeRef], vslot: Int = 0): Unit = {
      if (phase == Phase.Idle) { s("B").push(v, vslot) } else { s("B2").push(v, vslot) }
      c.dec()
    }

    def pop2(): (Option[NodeRef], Int) = {
      assert(!front.empty, "pop on an empty front: real-time invariant violated")
      val v = front.pop2()
      c.dec()
      if (phase != Phase.Idle) {
        m.dec()
        maybeFinish()
      }
      v
    }

    def pop(): Option[NodeRef] = pop2()._1

    def empty: Boolean = front.empty && s("B").empty && phase == Phase.Idle

    /** forget all elements (O(1): the old chains are simply dropped). */
    def clear(): Unit = {
      for (v <- s.values) { v.top = None }
      m.reset()
      c.reset()
      phase = Phase.Idle
    }

    // --- rotation ---------------------------------------------------------------

    private def start(): Unit = {
      s("WF").copyFrom(s("F"))
      s("WB").copyFrom(s("B"))
      s("Fr").top = None
      s("Br").top = None
      s("B2").top = None
      m.reset()
      phase = Phase.Rev
    }

    private def moveTop(from: StackView, to: StackView): Unit = {
      val (v, vs) = from.pop2()
      to.push(v, vs)
    }

    private def unit(): Unit = {
      phase match {
        case Phase.Rev =>
          var progressed = false
          if (!s("WB").empty) {
            moveTop(s("WB"), s("Br"))
            c.inc()
            c.inc()
            progressed = true
          }
          if (!s("WF").empty) {
            moveTop(s("WF"), s("Fr"))
            m.inc()
            progressed = true
          }
          if (!progressed) {
            phase = Phase.Copy
            maybeFinish()
          }
        case Phase.Copy =>
          if (m.sign > 0 && !s("Fr").empty) {
            moveTop(s("Fr"), s("Br"))
            m.dec()
          }
          maybeFinish()
        case Phase.Idle => ()
      }
    }

    private def maybeFinish(): Unit = {
      if (phase == Phase.Copy && m.sign == 0) {
        s("F").copyFrom(s("Br"))
        s("B").copyFrom(s("B2"))
        s("Br").top = None
        s("B2").top = None
        s("Fr").top = None
        phase = Phase.Idle
      }
    }

    /** ROT units of rotation work. */
    def work(): Unit = {
      for (_ <- 0 until ROT) {
        if (phase == Phase.Idle && c.sign < 0) {
          start()
        }
        if (phase != Phase.Idle) {
          unit()
        }
      }
    }

    /** Python `finalize`. */
    def finish(): Unit = {
      for (v <- s.values) { v.finish() }
      m.finish()
      c.finish()
      b.label(name + ".phase") = phase.label
    }
  }

  /** `vm.emit(b.label, **b.ptr)` */
  def emit(vm: VM, b: Builder): Node = vm.emit(b.label.toLabel, b.ptr.toVector)

  // ------------------------------------------------------------------------- tests

  private def assertSame(t: Int, got: Option[NodeRef], exp: Option[NodeRef]): Unit = {
    assert(sameTarget(got, exp), s"($t, $got, $exp)")
  }

  /** Random pushes/pops against a list model; returns the VM statistics. */
  def testStack(n: Int = 200, seed: Long = 1L): Stats = {
    val random = new PyRandom(seed)
    val vm = new VM
    val model = mutable.ArrayBuffer.empty[Option[NodeRef]]
    for (t <- 0 until n) {
      vm.begin()
      val b = new Builder
      val stack = new StackView(vm, vm.top, b, "S")
      // values: pointers to the previous top (an older node) or None
      for (_ <- 0 until random.randint(0, 3)) {
        val op = random.choice("pp o")
        if (op == "p") {
          val v = vm.top
          stack.push(v)
          model += v
        } else if (op == "o" && model.nonEmpty) {
          val got = stack.pop()
          val exp = model.remove(model.size - 1)
          assertSame(t, got, exp)
        }
      }
      assert(stack.empty == model.isEmpty)
      stack.finish()
      emit(vm, b)
    }
    vm.stats
  }

  /** Random pushes/pops of the real-time queue against a deque model; returns the VM
    * statistics.
    */
  def testQueue(n: Int = 3000, seed: Long = 2L): Stats = {
    val random = new PyRandom(seed)
    val vm = new VM
    val model = mutable.ArrayDeque.empty[Option[NodeRef]]
    for (t <- 0 until n) {
      vm.begin()
      val b = new Builder
      val queue = new RTQueueView(vm, vm.top, b, "Q")
      val r = random.random()
      if (r < 0.5 || model.isEmpty) {
        val v = vm.top // push a pointer to an older node
        queue.push(v)
        model.append(v)
      } else {
        val got = queue.pop()
        val exp = model.removeHead()
        assertSame(t, got, exp)
      }
      queue.work()
      assert(queue.empty == model.isEmpty, s"($t, ${queue.phase.label}, ${model.size})")
      queue.finish()
      emit(vm, b)
    }
    vm.stats
  }

  /** adversarial: long push phase then long pop phase, repeated */
  private def testQueueAdversarial(): Stats = {
    val vm = new VM
    val model = mutable.ArrayDeque.empty[Option[NodeRef]]
    val ops = (0 until 6).flatMap { rep =>
      Vector.fill(50 * (rep + 1))("push") ++ Vector.fill(50 * (rep + 1))("pop")
    }
    for ((op, t) <- ops.zipWithIndex) {
      vm.begin()
      val b = new Builder
      val queue = new RTQueueView(vm, vm.top, b, "Q")
      if (op == "push") {
        val v = vm.top
        queue.push(v)
        model.append(v)
      } else {
        val got = queue.pop()
        val exp = model.removeHead()
        assert(sameTarget(got, exp), t.toString)
      }
      queue.work()
      queue.finish()
      emit(vm, b)
    }
    vm.stats
  }

  /** `python3 scavm_structs.py` と同じ出力。 */
  def main(args: Array[String]): Unit = {
    println(s"stack   ${testStack().pythonRepr}")
    println(s"queue   ${testQueue().pythonRepr}")
    println(s"queue adversarial ${testQueueAdversarial().pythonRepr}")
  }
}
