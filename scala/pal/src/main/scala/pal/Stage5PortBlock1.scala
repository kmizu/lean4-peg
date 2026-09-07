package pal

import Scavm.{Label, Node, NodeRef, Self, Stats, VM, sameTarget}
import ScavmStructs.{Builder, RTQueueView, StackView, emit}

/** Stage 5, block 1: Galil's `match` + the nonchain `move` (KMP over the palindromic
  * window) as a scaffolding-automaton program on scavm, with the lag built in.
  *
  * The one genuinely pointer-hostile operation is KMP's "state += 1": the cell for
  * state s+1 was created after the cell for s, so no pointer leads there.  A Turing
  * machine has two heads on the pattern tape (one appending at the end, one at the
  * state); making that real time is exactly a real-time deque problem (Chuang &
  * Goldberg 1993).  We do not need a full deque: the cursor's right part is the stack
  * Rz (cells pushed back by failure jumps) followed by the queue A (cells appended by
  * the scan); every position in Rz precedes every position in A, so "+1" pops Rz if
  * nonempty else A's front, a failure jump pops Lz into Rz until the cell below the
  * top is the jump target (pointer equality), and appending pushes onto A.
  *
  * State (fields of the top node):
  * {{{
  *   c        label   input symbol of this node;   prev  ptr  previous input node
  *   Q.*      real-time queue of input nodes not yet processed by the simulation
  *   mode     label   'match' | 'kmp' | 'chain'
  *   L        ptr     leftmost node of the active palindrome [L, simR]
  *   simR     ptr     rightmost node the simulation has processed
  *   cur      ptr     node whose symbol is being processed (popped from Q)
  *   wj       ptr     KMP: window node of the position being scanned
  *   Lz.* Rz.* A.*    KMP cursor zipper (stacks / queue of cells)
  *   n        cell    cell of the full window once built (chain walk start)
  *   K.k.*    KMP cells created this step: fail (ptr) + fslot (lab), wn (ptr)
  * }}}
  *
  * Window positions count from simR leftwards: position 1 = simR, position q+1 =
  * prev of position q; cell q stores wn = node of position q, so "pattern symbol at
  * q+1" = label(prev(wn(cell q))) and "start of the border of length q" = wn(cell q).
  * The cursor holds s = matched length + 1 = the position to compare; Lz = cells
  * 1..s (top = cell s); state 0 is "Lz has one cell and we are before it", tracked by
  * the flag `zero`.
  *
  * Units: one unit = O(1) hops.  `run(x, budget)` executes at most `budget` units per
  * real step; `budget=None` = unbounded (online correctness).  Output at real step t:
  * 1 iff the simulation is caught up and L is node 0.
  *
  * Python 版 `stage5_port_block1.py` の移植。Python の 1 本の `run` を、1 ステップ分の
  * 状態を持つ [[Stage5PortBlock1.Step]] に分けてある（DEBUG 出力は移植していない）。
  */
object Stage5PortBlock1 {

  /** A KMP cell reference (node, slot). */
  final case class Cell(node: NodeRef, slot: Int) {
    def same(other: Option[Cell]): Boolean = other.exists(c => (node eq c.node) && slot == c.slot)
  }

  /** The simulation mode, stored in the label `mode` as `'match' | 'kmp' | 'chain'`. */
  enum Mode(val label: String) {
    case Match extends Mode("match")
    case Kmp extends Mode("kmp")
    case Chain extends Mode("chain")
  }

  object Mode {
    def fromLabel(label: Label): Mode = {
      val s = label.asStr
      values.find(_.label == s).getOrElse(throw new IllegalArgumentException(s"unknown mode '$s'"))
    }
  }

  /** One real step of the machine: reads the state from the previous top, runs units,
    * and writes the new top's fields.
    */
  private final class Step(vm: VM, cnew: String, budget: Option[Int]) {
    private val prev: Option[Node] = vm.top
    private val b = new Builder
    private val q = new RTQueueView(vm, prev, b, "Q")
    private val a = new RTQueueView(vm, prev, b, "A")
    private val lz = new StackView(vm, prev, b, "Lz")
    private val rz = new StackView(vm, prev, b, "Rz")

    private var mode: Mode = Mode.Match
    private var left: Option[NodeRef] = None // Python `L`
    private var simR: Option[NodeRef] = None
    private var cur: Option[NodeRef] = None
    private var wj: Option[NodeRef] = None
    private var ncell: Option[Cell] = None
    private var zero: Boolean = true
    private var jt: Option[Cell] = None
    private var jumping: Boolean = false

    b.ptr("prev") = prev // the new node's own fields
    b.label("c") = cnew
    q.push(Some(Self)) // the new input node
    q.work()
    loadState()

    // ---- load state -----------------------------------------------------

    private def loadState(): Unit = {
      prev.foreach { p =>
        val lab = vm.label(p)
        mode = Mode.fromLabel(lab("mode"))
        zero = lab("zero").asBool
        left = vm.get(p, "L")
        simR = vm.get(p, "simR")
        cur = vm.get(p, "cur")
        wj = vm.get(p, "wj")
        ncell = vm.get(p, "n").map(n => Cell(n, lab("nslot").asInt))
        jt = vm.get(p, "jt").map(n => Cell(n, lab("jtslot").asInt))
        jumping = lab("jumping").asBool
      }
    }

    // ---- cell helpers -------------------------------------------------------

    private def cellKey(cell: Cell, field: String): String = s"K.${cell.slot}.$field"

    /** Python `cget` for the pointer fields `fail` / `wn`. */
    private def cellPtr(cell: Cell, field: String): Option[NodeRef] = {
      val key = cellKey(cell, field)
      cell.node match {
        case Self => b.ptr(key)
        case node: Node => gt(Some(node), key)
      }
    }

    /** Python `cget` for the label field `fslot`. */
    private def cellLab(cell: Cell, field: String): Label = {
      val key = cellKey(cell, field)
      cell.node match {
        case Self => b.label(key)
        case node: Node => vm.label(node)(key)
      }
    }

    private def cfail(cell: Cell): Option[Cell] = {
      cellPtr(cell, "fail").map(f => Cell(f, cellLab(cell, "fslot").asInt))
    }

    private def newCell(fail: Option[Cell], wn: Option[NodeRef]): Cell = {
      val k = b.slot("K")
      b.ptr(s"K.$k.fail") = fail.map(_.node)
      b.label(s"K.$k.fslot") = fail.fold(0)(_.slot)
      b.ptr(s"K.$k.wn") = wn
      Cell(Self, k)
    }

    private def sym(node: NodeRef): String = {
      node match {
        case Self => cnew
        case n: Node => vm.label(n)("c").asStr
      }
    }

    /** Python `gt`: `None` → `None`（hop なし）、SELF → builder の欄、実節点 → `vm.get`。 */
    private def gt(node: Option[NodeRef], field: String): Option[NodeRef] = {
      node match {
        case None => None
        case Some(Self) => b.ptr.get(field).flatten
        case Some(n: Node) => vm.get(n, field)
      }
    }

    private def spush(s: StackView, cell: Cell): Unit = s.push(Some(cell.node), cell.slot)

    private def spop(s: StackView): Cell = {
      val (n, slot) = s.pop2()
      Cell(n.get, slot)
    }

    private def speek(s: StackView): Cell = {
      val (n, slot) = s.peek2
      Cell(n.get, slot)
    }

    private def sbelow(s: StackView): Option[Cell] = {
      s.belowOfTop.map { case (n, slot) => Cell(n.get, slot) }
    }

    private def qpush(qx: RTQueueView, cell: Cell): Unit = {
      qx.push(Some(cell.node), cell.slot)
      qx.work()
    }

    private def qpop(qx: RTQueueView): Cell = {
      val (n, slot) = qx.pop2()
      qx.work()
      Cell(n.get, slot)
    }

    // ---- units --------------------------------------------------------------

    /** Run units until the budget is spent or the simulation has caught up. */
    private def runUnits(): Unit = {
      var units = 0
      var running = true
      while (running && budget.forall(units < _)) {
        units += 1
        running = mode match {
          case Mode.Match => matchUnit()
          case Mode.Kmp => kmpUnit()
          case Mode.Chain => chainUnit()
        }
      }
    }

    /** Galil's `match`; returns False when the queue is empty (caught up). */
    private def matchUnit(): Boolean = {
      if (q.empty) {
        false
      } else {
        cur = q.pop()
        q.work()
        val c = sym(cur.get)
        simR match {
          case None => // first symbol ever
            left = cur
            simR = cur
          case Some(_) =>
            val lp = gt(left, "prev")
            if (lp.exists(l => sym(l) == c)) { // extend
              left = lp
              simR = cur
            } else {
              startWindow()
            }
        }
        true
      }
    }

    /** mismatch: failure structure of the window read from simR leftwards */
    private def startWindow(): Unit = {
      val cell1 = newCell(None, simR) // position 1, fail(1) = 0
      lz.top = None
      rz.top = None
      a.clear()
      jumping = false
      jt = None
      spush(lz, cell1) // cursor at position 1, matched 0
      zero = true
      if (sameTarget(simR, left)) { // window of length 1
        mode = Mode.Chain
        ncell = Some(cell1)
      } else {
        mode = Mode.Kmp
        wj = gt(simR, "prev") // position 2
      }
    }

    /** one KMP unit over the window; always continues. */
    private def kmpUnit(): Boolean = {
      val cj = sym(wj.get)
      val sCell = speek(lz) // position s to compare
      val created: Option[Cell] = if (sym(cellPtr(sCell, "wn").get) == cj) {
        // match at position s: fail(j) = s (matched length), s += 1
        val newc = newCell(Some(sCell), wj)
        qpush(a, newc)
        if (!rz.empty) {
          spush(lz, spop(rz))
        } else {
          spush(lz, qpop(a))
        }
        zero = false
        Some(newc)
      } else if (zero) {
        // matched length 0 and mismatch: fail(j) = 0, stay
        val newc = newCell(None, wj)
        qpush(a, newc)
        Some(newc)
      } else {
        failureJumpUnit()
        None // retry the compare next unit
      }
      created.foreach { newc =>
        if (sameTarget(wj, left)) {
          mode = Mode.Chain
          ncell = Some(newc)
        } else {
          wj = gt(wj, "prev")
        }
      }
      true
    }

    /** failure jump: matched length s-1 -> fail(s-1); new position = fail(s-1)+1, i.e.
      * pop Lz into Rz until the cell below the top is cell(fail(s-1)) (None -> until
      * one cell is left, then zero).  One step per unit: keep the target in `jt`, pop
      * until reached.
      */
    private def failureJumpUnit(): Unit = {
      if (!jumping) {
        jt = cfail(sbelow(lz).get)
        jumping = true
      }
      sbelow(lz) match {
        case None =>
          zero = true
          jumping = false
        case Some(bel) if bel.same(jt) =>
          jumping = false
        case Some(_) =>
          spush(rz, spop(lz))
      }
    }

    /** one unit of the failure-chain walk; always continues. */
    private def chainUnit(): Boolean = {
      val c = sym(cur.get)
      cfail(ncell.get) match { // longest proper border
        case None =>
          left = if (sym(simR.get) == c) { simR } else { cur } // "cc" or "c"
          simR = cur
          mode = Mode.Match
        case Some(cand) =>
          val start = cellPtr(cand, "wn")
          val before = gt(start, "prev") // Python: gt(None, 'prev') is None
          if (before.exists(bf => sym(bf) == c)) {
            left = before
            simR = cur
            mode = Mode.Match
          } else {
            ncell = Some(cand)
          }
      }
      true
    }

    // ---- finish the step ---------------------------------------------------------

    /** Run the units, write the state and emit the node; returns the output bit. */
    def execute(): Int = {
      runUnits()
      val caughtUp = q.empty && mode == Mode.Match
      val out = if (caughtUp && left.isDefined && gt(left, "prev").isEmpty) { 1 } else { 0 }
      q.work()
      a.work()
      q.finish()
      a.finish()
      lz.finish()
      rz.finish()
      b.label("mode") = mode.label
      b.label("out") = out
      b.label("zero") = zero
      b.ptr("L") = left
      b.ptr("simR") = simR
      b.ptr("cur") = cur
      b.ptr("wj") = wj
      b.ptr("n") = ncell.map(_.node)
      b.label("nslot") = ncell.fold(0)(_.slot)
      b.ptr("jt") = jt.map(_.node)
      b.label("jtslot") = jt.fold(0)(_.slot)
      b.label("jumping") = jumping
      emit(vm, b)
      out
    }
  }

  /** Run the machine on `x` with at most `budget` units per real step (`None` =
    * unbounded); returns the output bits and the VM statistics.
    */
  def run(x: String, budget: Option[Int] = None): (Vector[Int], Stats) = {
    val vm = new VM
    val outs = x.map { cnew =>
      vm.begin()
      new Step(vm, cnew.toString, budget).execute()
    }.toVector
    (outs, vm.stats)
  }

  /** 1 at t iff x[0..t] is a palindrome. */
  def brute(x: String): Vector[Int] = {
    (0 until x.length).map { t =>
      val prefix = x.substring(0, t + 1)
      if (prefix == prefix.reverse) { 1 } else { 0 }
    }.toVector
  }

  private def pyList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")

  /** `python3 stage5_port_block1.py` と同じ出力。 */
  def main(args: Array[String]): Unit = {
    var bad = 0
    var tot = 0
    var worst: Option[Stats] = None
    for (n <- 1 to 10) {
      for (x <- allStrings("ab", n)) {
        tot += 1
        val (outs, st) = run(x)
        if (outs != brute(x)) {
          bad += 1
          if (bad <= 5) {
            println(s"BAD $x ${pyList(outs)} ${pyList(brute(x))}")
          }
        }
        if (worst.forall(w => st.radius > w.radius)) {
          worst = Some(st)
        }
      }
    }
    println(s"online (unbounded budget): strings $tot bad $bad worst stats ${worst.fold("None")(_.pythonRepr)}")
  }

  /** `itertools.product(alphabet, repeat=n)` joined, in lexicographic order. */
  def allStrings(alphabet: String, n: Int): Vector[String] = {
    (1 to n).foldLeft(Vector("")) { (acc, _) =>
      for (s <- acc; c <- alphabet) yield s + c
    }
  }
}
