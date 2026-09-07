package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** A scaffolding-automaton virtual machine (stage 4 target for the palindrome PEG).
  *
  * Model (Kim & Park, `Common/Model/Scaffolding.lean`): reading one input symbol per
  * step, the machine creates exactly one node.  A node has a finite label and a bounded
  * number of pointer fields; pointers may only go to *older* nodes.  The transition
  * sees the previous top node's neighbourhood of bounded radius; the new node's
  * pointers must be nodes reached inside that neighbourhood during the step.  The
  * machine accepts by its finite state (here: the top label's `out` component).
  *
  * This VM enforces exactly that:
  *   - `get(node, field)` is the only way to reach a node; it counts one hop and
  *     records the node as touched this step;
  *   - `emit(label, ptrs)` creates the new top; every pointer must be None, the
  *     previous top, or a node touched this step;
  *   - labels must be drawn from a finite set (checked: the label must be a tuple of
  *     small ints / one-character strings / None, and the number of distinct labels
  *     seen must stay bounded — reported, so a run over long inputs exposes leaks);
  *   - per-step hop counts are recorded; `radius` = the maximum.
  *
  * Slots.  One physical node per step is too coarse for structures that must grow
  * several cells per symbol (the KMP tables run at RATE units per symbol), so a
  * logical cell is (node, slot) with slot < SLOTS; a slot is finite data and lives in
  * the label.  Library structures below use that convention.
  *
  * Library: Stack (a chain of cells, one push per structure per step) and a
  * real-time Queue (Hood & Melville 1981 style: two stacks plus an incremental
  * reversal, O(1) worst-case per operation), because "revisit marks left-to-right"
  * needs a queue while "revisit right-to-left" needs a stack.
  *
  * Python 版 `scavm.py` の移植。Python ではラベルは任意のオブジェクトで、`_finite_label`
  * が実行時に形を検査していた。Scala 版では形そのものを [[Scavm.Label]] という閉じた
  * ADT にし、範囲（整数は ±64、文字列は 16 文字以下）だけを `emit` で検査する。
  * ポインタの行き先は [[Scavm.NodeRef]]（実ノード、または「今作っている節点」 [[Scavm.Self]]）で、
  * Python の `None` は `Option` で表す。
  */
object Scavm {

  // ------------------------------------------------------------------ labels

  /** A finite label value: the Python shapes `_finite_label` accepts, as a closed ADT. */
  sealed trait Label {

    /** Python の `label[key]`（dict ラベル）。無いキーは `NoSuchElementException`（KeyError）。 */
    def apply(key: String): Label = {
      this match {
        case Label.Dict(entries) =>
          entries.collectFirst { case (k, v) if k == key => v }
            .getOrElse(throw new NoSuchElementException(s"KeyError: '$key'"))
        case other => throw new IllegalArgumentException(s"label $other is not a dict")
      }
    }

    /** Python の `label[index]`（tuple ラベル）。 */
    def apply(index: Int): Label = {
      this match {
        case Label.Tuple(items) => items(index)
        case other => throw new IllegalArgumentException(s"label $other is not a tuple")
      }
    }

    /** Python の `label.get(key)`（dict ラベル）: 無ければ `None`。 */
    def get(key: String): Option[Label] = {
      this match {
        case Label.Dict(entries) => entries.collectFirst { case (k, v) if k == key => v }
        case other => throw new IllegalArgumentException(s"label $other is not a dict")
      }
    }

    def asStr: String = {
      this match {
        case Label.Str(value) => value
        case other => throw new IllegalArgumentException(s"label $other is not a str")
      }
    }

    def asInt: Int = {
      this match {
        case Label.Num(value) => value
        case Label.Bool(value) => if (value) { 1 } else { 0 } // Python: bool は int の部分型
        case other => throw new IllegalArgumentException(s"label $other is not an int")
      }
    }

    def asBool: Boolean = {
      this match {
        case Label.Bool(value) => value
        case other => throw new IllegalArgumentException(s"label $other is not a bool")
      }
    }

    def isNull: Boolean = this == Label.Null

    /** Python の `repr()` と同じ文字列。デモ出力や `Node.toString` に使う。 */
    def pythonRepr: String = {
      this match {
        case Label.Null => "None"
        case Label.Bool(true) => "True"
        case Label.Bool(false) => "False"
        case Label.Num(value) => value.toString
        case Label.Str(value) => Label.reprStr(value)
        case Label.Tuple(items) =>
          if (items.size == 1) { s"(${items.head.pythonRepr},)" }
          else { items.map(_.pythonRepr).mkString("(", ", ", ")") }
        case Label.Dict(entries) =>
          entries.map { case (k, v) => s"${Label.reprStr(k)}: ${v.pythonRepr}" }.mkString("{", ", ", "}")
      }
    }
  }

  object Label {
    case object Null extends Label
    final case class Bool(value: Boolean) extends Label
    final case class Num(value: Int) extends Label
    final case class Str(value: String) extends Label
    final case class Tuple(items: Vector[Label]) extends Label
    /** 挿入順を保つ dict ラベル（`Builder.label` を `emit` で凍結したもの）。 */
    final case class Dict(entries: Vector[(String, Label)]) extends Label

    def tuple(items: Label*): Tuple = Tuple(items.toVector)

    /** Python `_finite_label`: ints in [-64, 64], strings of at most 16 chars, bools, None,
      * tuples and dicts (with string keys) of finite labels.
      */
    def isFinite(label: Label): Boolean = {
      label match {
        case Null => true
        case Dict(entries) => entries.forall { case (_, v) => isFinite(v) }
        case Tuple(items) => items.forall(isFinite)
        case Bool(_) => true
        case Num(value) => -64 <= value && value <= 64
        case Str(value) => value.length <= 16
      }
    }

    /** Python の `repr(str)`: 通常はシングルクォート、`'` を含み `"` を含まなければダブルクォート。 */
    private[Scavm] def reprStr(value: String): String = {
      val quote = if (value.contains('\'') && !value.contains('"')) { '"' } else { '\'' }
      val body = value.flatMap {
        case '\\' => "\\\\"
        case '\n' => "\\n"
        case '\r' => "\\r"
        case '\t' => "\\t"
        case c if c == quote => s"\\$c"
        case c => c.toString
      }
      s"$quote$body$quote"
    }
  }

  /** Python の `dict` ラベル（`Builder.label`）: 挿入順を保つ可変マップ。
    * `label("k") = "v"` / `= 3` / `= true` と書けるよう `update` を多重定義してある。
    */
  final class LabelMap {
    private val entries = mutable.LinkedHashMap.empty[String, Label]

    def update(key: String, value: Label): Unit = { entries(key) = value }
    def update(key: String, value: String): Unit = { entries(key) = Label.Str(value) }
    def update(key: String, value: Int): Unit = { entries(key) = Label.Num(value) }
    def update(key: String, value: Boolean): Unit = { entries(key) = Label.Bool(value) }

    /** `dict[key]`: 無いキーは `NoSuchElementException`。 */
    def apply(key: String): Label = {
      entries.getOrElse(key, throw new NoSuchElementException(s"KeyError: '$key'"))
    }

    /** `dict.get(key)`。 */
    def get(key: String): Option[Label] = entries.get(key)

    def contains(key: String): Boolean = entries.contains(key)

    def size: Int = entries.size

    def toVector: Vector[(String, Label)] = entries.toVector

    /** 凍結して節点ラベルにする。 */
    def toLabel: Label.Dict = Label.Dict(entries.toVector)
  }

  // ------------------------------------------------------------------ nodes

  /** A pointer target: a real node, or [[Self]] — "the node being created" (Lean:
    * `LocalTarget.self`).  Python の `None` はこの型の `Option` で表す。
    */
  sealed trait NodeRef

  /** pointer target "the node being created" (Lean: LocalTarget.self). Python の `SELF`。 */
  case object Self extends NodeRef

  /** A node of the scaffold: creation time `t`, a finite `label`, and pointer fields
    * (`pointers`, insertion-ordered; every target is an older node or the node itself).
    * Equality is identity, as Python's `is`.
    */
  final class Node private[Scavm] (val t: Int, val label: Label, resolve: Node => VectorMap[String, Option[Node]])
      extends NodeRef {

    val pointers: VectorMap[String, Option[Node]] = resolve(this)

    /** `node.ptr.get(field)`: 無いフィールドも `None`。 */
    def pointer(field: String): Option[Node] = pointers.get(field).flatten

    override def toString: String = s"N$t${label.pythonRepr}"
  }

  /** Python の `a is b`（両方 `None` も真）。 */
  def sameTarget(a: Option[NodeRef], b: Option[NodeRef]): Boolean = {
    (a, b) match {
      case (None, None) => true
      case (Some(x), Some(y)) => x eq y
      case _ => false
    }
  }

  /** `VM.stats()`: dict `{'steps': .., 'radius': .., 'fields': .., 'labels': ..}`。 */
  final case class Stats(steps: Int, radius: Int, fields: Int, labels: Int) {
    def pythonRepr: String = {
      s"{'steps': $steps, 'radius': $radius, 'fields': $fields, 'labels': $labels}"
    }
  }

  // ------------------------------------------------------------------ the VM

  final class VM {
    private var time = -1
    private var current: Option[Node] = None
    private var touched = mutable.HashSet.empty[Node]
    private var hopCount = 0
    private var maxRadius = 0
    private val seenLabels = mutable.LinkedHashSet.empty[Label]
    private var maxFields = 0

    /** Python `vm.t`: index of the current step (-1 before the first `begin`). */
    def t: Int = time

    /** Python `vm.top`: the previous top during a step (before `emit`), the new one after. */
    def top: Option[Node] = current

    def hops: Int = hopCount

    def radius: Int = maxRadius

    private def reachable(node: Node): Boolean = {
      current.exists(_ eq node) || touched.contains(node)
    }

    // ---- reading ---------------------------------------------------------

    /** follow a pointer field of a node reached this step (one hop).
      *
      * Python では `node` に `None` も渡せて `None` が返る。Scala 版は呼び出し側が
      * `Option` を剥がしてから渡す。
      */
    def get(node: Node, field: String): Option[Node] = {
      assert(reachable(node), s"$node not reachable this step")
      hopCount += 1
      val target = node.pointer(field)
      target.foreach { target =>
        assert(target.t <= node.t, "pointer to a newer node")
        touched += target
      }
      target
    }

    def label(node: Node): Label = {
      assert(reachable(node), s"$node not reachable this step")
      node.label
    }

    // ---- one step ----------------------------------------------------------

    def begin(): Unit = {
      time += 1
      touched = mutable.HashSet.empty[Node]
      hopCount = 0
    }

    private def pointerAllowed(target: Option[NodeRef]): Boolean = {
      target match {
        case None => true
        case Some(Self) => true
        case Some(node: Node) => reachable(node)
      }
    }

    /** Create the new top.  Every pointer must be None, [[Self]], the previous top, or a
      * node touched this step; [[Self]] is replaced by the created node.
      */
    def emit(label: Label, ptr: Seq[(String, Option[NodeRef])]): Node = {
      assert(Label.isFinite(label), s"label not finite-shaped: ${label.pythonRepr}")
      for ((k, v) <- ptr) {
        assert(pointerAllowed(v), s"pointer $k -> ${v.getOrElse("None")} was not reached this step")
      }
      val node = new Node(time, label, self => {
        VectorMap.from(ptr.map {
          case (k, Some(Self)) => (k, Some(self))
          case (k, Some(target: Node)) => (k, Some(target))
          case (k, None) => (k, None)
        })
      })
      seenLabels += label
      maxFields = math.max(maxFields, ptr.size)
      maxRadius = math.max(maxRadius, hopCount)
      current = Some(node)
      node
    }

    def stats: Stats = Stats(steps = time + 1, radius = maxRadius, fields = maxFields, labels = seenLabels.size)
  }

  // ---------------------------------------------------------------- library structures
  // A structure lives in the label/pointer fields of the top node under a name prefix.
  // Each is a pure function of (vm, top) -> values to put in the next node, so that the
  // transition of a machine composes several of them into one `emit`.

  /** Cells are (node, slot).  The stack is represented by a pointer `<name>_top`
    * to the physical node of its top cell and a label entry `<name>_slot`; each cell
    * stores its value in the label as `<name>_v<slot>` and its predecessor as the
    * pointer `<name>_below<slot>` plus label `<name>_bslot<slot>`.  At most one push
    * per step is needed by our algorithms; several pushes per step could use slots.
    *
    * （Python 版でも placeholder。実際のスタックは `ScavmStructs.StackView`。）
    */
  final class Stack(val name: String) {
    def empty(vm: VM, top: Option[Node]): Boolean = {
      top match {
        case Some(node) => vm.get(node, name + "_top").isEmpty
        case None => true
      }
    }
  }

  // The generic structures above are placeholders for the port; the concrete machine
  // below shows the discipline on the simplest piece of Galil's algorithm: the match
  // loop with heads L (moving left, one hop) and R (the top).  It recognises exactly
  // the palindromes whose characters pair up from the outside without ever needing a
  // `move` — i.e. it is stage-2 minus the nonchain move — and is here to validate the
  // VM discipline (hops, reachability, finite labels) before the real port.

  private def symLabel(c: Char, out: Int): Label = {
    Label.tuple(Label.Str("sym"), Label.Str(c.toString), Label.Num(out))
  }

  /** Galil's `match` alone: keep the left neighbour `L` of the active suffix
    * palindrome; extend while x[L] == c, otherwise restart from the single symbol.
    * Output 1 iff the active palindrome starts at 0.  (Not a palindrome recogniser —
    * it lacks `move` — but every operation is one the scaffold allows: prev
    * pointers, one label per node, O(1) hops per step.)
    */
  def demoExtensionOnly(x: String): (Vector[Int], Stats) = {
    val vm = new VM
    val outs = Vector.newBuilder[Int]
    for (c <- x) {
      vm.begin()
      vm.top match {
        case None =>
          vm.emit(symLabel(c, 1), Seq("prev" -> None, "L" -> None)) // window [0,0]; L = marker
          outs += 1
        case Some(top) =>
          val left = vm.get(top, "L") // node left of the window
          val out = left match {
            case Some(l) if vm.label(l)(1) == Label.Str(c.toString) =>
              val newLeft = vm.get(l, "prev") // extend both ways
              val out = if (newLeft.isEmpty) { 1 } else { 0 }
              vm.emit(symLabel(c, out), Seq("prev" -> Some(top), "L" -> newLeft))
              out
            case _ =>
              vm.emit(symLabel(c, 0), Seq("prev" -> Some(top), "L" -> Some(top))) // restart: window [t,t]
              0
          }
          outs += out
      }
    }
    (outs.result(), vm.stats)
  }

  private def pyList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")

  /** `python3 scavm.py` と同じ出力。 */
  def main(args: Array[String]): Unit = {
    // the demo only tracks the palindrome centred at the middle of the whole string
    // once L reaches the marker; it is not a palindrome recogniser, just a discipline test
    val (outs1, st1) = demoExtensionOnly("abba")
    println(s"demo abba -> ${pyList(outs1)} ${st1.pythonRepr}")
    val (outs2, st2) = demoExtensionOnly("ab" * 50)
    println(s"demo (ab)^50 -> ${pyList(outs2.takeRight(4))} ${st2.pythonRepr}")
  }
}
