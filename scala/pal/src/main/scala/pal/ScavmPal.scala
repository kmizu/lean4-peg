package pal

import Scavm.{Label, Node, NodeRef, Self, Stats, VM}
import ScavmStructs.{Builder, RTQueueView, StackView, emit}

/** Components of the palindrome machine on the scaffolding VM (block 2 parts).
  *
  * Places.  Input symbol i sits at place 2i+1 (node i, half 0); the space after it is
  * place 2i+2 (node i, half 1); place 0 is the marker.  A place is `Place(node, half)`;
  * `pleft` is one place to the left; `psym` reads its symbol (SPACE for half 1).
  *
  * KMP over a window.  `KmpWindow` builds the KMP failure structure of the place
  * string read from `hi` leftwards down to `lo` (the palindromic window is its own
  * reverse), one unit per elementary operation, with the cursor zipper Lz / Rz / A of
  * block 1.  Cells: fail, wn (window place: node + half), pred (previous cell = the
  * position below), all as (node, slot) references.  Result: the cell of the full
  * window (`ncell`); the failure chain from it lists the palindromic suffixes of the
  * window in decreasing length, i.e. the palindromes ending at `hi`.
  *
  * Marks and the double-palindrome check.  `Marks` walks the failure chain and the
  * pred chain of the cells in lockstep, creating one mark cell per position with a
  * bit "on the chain" — Galil's marks of the left ends of initial palindromes; the
  * mark cells link to the previous position, so `DpCheck` can walk them with two
  * cursors at speeds 2 and 4 (positions 2k+1 and 4k+1) and report the smallest k
  * above a threshold with both bits set.  Positions are never compared as numbers:
  * the cursors are aligned by lockstep walks from the top.
  *
  * Everything here is unit-stepped: `step()` does O(1) hops and returns True while
  * work remains.  State lives in the Builder under a name prefix.
  *
  * Python 版 `scavm_pal.py` の移植。
  */
object ScavmPal {

  val SPACE: String = "_"

  /** A place: (node, half); half 0 = the symbol, half 1 = the space after it. */
  final case class Place(node: NodeRef, half: Int) {
    /** Python `same`: identity of the node and equality of the half. */
    def same(o: Option[Place]): Boolean = o.exists(p => (node eq p.node) && half == p.half)
  }

  /** A cell reference (node, slot). */
  final case class Cell(node: NodeRef, slot: Int) {
    def same(o: Option[Cell]): Boolean = o.exists(c => (node eq c.node) && slot == c.slot)
  }

  /** per-step context: vm, previous top, builder, this step's symbol. */
  final class Ctx(val vm: VM, val prev: Option[Node], val b: Builder, val cnew: String) {

    // node fields (SELF-aware)

    /** Python `get`: `None` → `None`（hop なし）、SELF → builder の欄、実節点 → `vm.get`。 */
    def get(node: Option[NodeRef], field: String): Option[NodeRef] = {
      node match {
        case None => None
        case Some(Self) => b.ptr.get(field).flatten
        case Some(n: Node) => vm.get(n, field)
      }
    }

    /** Python `lab`: for SELF a missing field reads as `None` (`dict.get`), for an older
      * node it is a KeyError.
      */
    def lab(node: NodeRef, field: String): Label = {
      node match {
        case Self => b.label.get(field).getOrElse(Label.Null)
        case n: Node => vm.label(n)(field)
      }
    }

    def sym(node: NodeRef): String = {
      node match {
        case Self => cnew
        case n: Node => vm.label(n)("c").asStr
      }
    }

    // places

    def pleft(p: Option[Place]): Option[Place] = {
      p.flatMap { place =>
        if (place.half == 1) {
          Some(Place(place.node, 0))
        } else {
          get(Some(place.node), "prev").map(pn => Place(pn, 1))
        }
      }
    }

    /** the symbol at a place; `None` is the marker. */
    def psym(p: Option[Place]): Option[String] = {
      p.map(place => if (place.half == 1) { SPACE } else { sym(place.node) })
    }

    // persisted place fields

    def loadPlace(name: String): Option[Place] = {
      prev.flatMap { p =>
        vm.get(p, name).map(n => Place(n, vm.label(p)(name + ".h").asInt))
      }
    }

    def savePlace(name: String, p: Option[Place]): Unit = {
      b.ptr(name) = p.map(_.node)
      b.label(name + ".h") = p.fold(0)(_.half)
    }

    // persisted cell references

    def loadCell(name: String): Option[Cell] = {
      prev.flatMap { p =>
        vm.get(p, name).map(n => Cell(n, vm.label(p)(name + ".s").asInt))
      }
    }

    def saveCell(name: String, c: Option[Cell]): Unit = {
      b.ptr(name) = c.map(_.node)
      b.label(name + ".s") = c.fold(0)(_.slot)
    }

    def loadLab(name: String, default: Label): Label = {
      prev.fold(default)(p => vm.label(p)(name))
    }

    def loadBool(name: String, default: Boolean): Boolean = loadLab(name, Label.Bool(default)).asBool
  }

  /** A keyword argument of Python `Cells.new(**kw)`: a cell, a place, a raw pointer, or a
    * label value.
    */
  sealed trait CellArg

  object CellArg {
    final case class OfCell(cell: Cell) extends CellArg
    final case class OfPlace(place: Place) extends CellArg
    final case class Pointer(target: Option[NodeRef]) extends CellArg
    final case class Lab(value: Label) extends CellArg

    /** Python では `None` は `isinstance(v, Cell)` に落ちず生ポインタ扱いになる。 */
    def cell(c: Option[Cell]): CellArg = c.fold[CellArg](Pointer(None))(OfCell(_))
    def place(p: Option[Place]): CellArg = p.fold[CellArg](Pointer(None))(OfPlace(_))
    val none: CellArg = Pointer(None)
    def bool(v: Boolean): CellArg = Lab(Label.Bool(v))
  }

  /** a family of cells under a prefix; fields: pointers and labels. */
  final class Cells(val ctx: Ctx, val prefix: String, val ptrFields: Set[String], val labFields: Set[String]) {

    def key(cell: Cell, f: String): String = s"$prefix.${cell.slot}.$f"

    /** Python `get` for a pointer field. */
    def getPtr(cell: Cell, f: String): Option[NodeRef] = ctx.get(Some(cell.node), key(cell, f))

    /** Python `get` for a label field. */
    def getLab(cell: Cell, f: String): Label = ctx.lab(cell.node, key(cell, f))

    def getCell(cell: Cell, f: String): Option[Cell] = {
      getPtr(cell, f).map(n => Cell(n, getLab(cell, f + ".s").asInt))
    }

    def getPlace(cell: Cell, f: String): Option[Place] = {
      getPtr(cell, f).map(n => Place(n, getLab(cell, f + ".h").asInt))
    }

    /** Python `new(**kw)`: create a cell in the node being built.
      *
      * Python の分岐順そのまま: `Cell` → `Place` → `f in ptr_fields`（ポインタ欄）→ それ以外は
      * ラベル欄。`None` はどちらの欄にも置ける（`new(on=None)` はラベル `on = None`）。
      * ラベル欄に実ポインタ、ポインタ欄に `None` 以外のラベル値を置くと Python は `emit` 時の
      * assert で落ちるので、ここでは即座に拒否する。
      */
    def create(fields: (String, CellArg)*): Cell = {
      val k = ctx.b.slot(prefix)
      val c = Cell(Self, k)
      for ((f, v) <- fields) {
        v match {
          case CellArg.OfCell(cell) =>
            ctx.b.ptr(key(c, f)) = Some(cell.node)
            ctx.b.label(key(c, f + ".s")) = cell.slot
          case CellArg.OfPlace(place) =>
            ctx.b.ptr(key(c, f)) = Some(place.node)
            ctx.b.label(key(c, f + ".h")) = place.half
          case CellArg.Pointer(target) if ptrFields.contains(f) =>
            writePointer(c, f, target)
          case CellArg.Lab(Label.Null) if ptrFields.contains(f) =>
            writePointer(c, f, None) // Python: None is None
          case CellArg.Lab(value) if ptrFields.contains(f) =>
            throw new IllegalArgumentException(s"pointer field $f of $prefix cannot hold the label ${value.pythonRepr}")
          case CellArg.Pointer(None) =>
            ctx.b.label(key(c, f)) = Label.Null
          case CellArg.Pointer(Some(target)) =>
            throw new IllegalArgumentException(s"label field $f of $prefix cannot hold the pointer $target")
          case CellArg.Lab(value) =>
            ctx.b.label(key(c, f)) = value
        }
      }
      c
    }

    /** the `f in self.ptr_fields` branch of Python `new`: the pointer plus zeroed `.s` / `.h` labels */
    private def writePointer(c: Cell, f: String, target: Option[NodeRef]): Unit = {
      ctx.b.ptr(key(c, f)) = target
      if (labFields.contains(f + ".s")) {
        ctx.b.label(key(c, f + ".s")) = 0
      }
      if (labFields.contains(f + ".h")) {
        ctx.b.label(key(c, f + ".h")) = 0
      }
    }
  }

  // ------------------------------------------------------------------ KMP over a window

  /** Failure structure of the place string hi, hi-1, ..., lo (read leftwards).
    * Cursor zipper as in block 1.  `start(lo, hi)` then `step()` until it returns
    * False; then `ncell` is the cell of the full window.
    */
  final class KmpWindow(val ctx: Ctx, val name: String) {
    import KmpWindow.{LAB, PTR}

    val cells: Cells = new Cells(ctx, name + ".K", PTR, LAB)
    val lz: StackView = new StackView(ctx.vm, ctx.prev, ctx.b, name + ".Lz")
    val rz: StackView = new StackView(ctx.vm, ctx.prev, ctx.b, name + ".Rz")
    val a: RTQueueView = new RTQueueView(ctx.vm, ctx.prev, ctx.b, name + ".A")
    var active: Boolean = ctx.loadBool(name + ".active", false)
    var zero: Boolean = ctx.loadBool(name + ".zero", true)
    var jumping: Boolean = ctx.loadBool(name + ".jumping", false)
    var lo: Option[Place] = ctx.loadPlace(name + ".lo")
    var wj: Option[Place] = ctx.loadPlace(name + ".wj")
    var last: Option[Cell] = ctx.loadCell(name + ".last") // last created cell (position j-1)
    var jt: Option[Cell] = ctx.loadCell(name + ".jt")
    var ncell: Option[Cell] = ctx.loadCell(name + ".ncell")

    def start(lo: Place, hi: Place): Unit = {
      this.lo = Some(lo)
      lz.top = None
      rz.top = None
      a.clear()
      val c1 = cells.create("fail" -> CellArg.none, "wn" -> CellArg.OfPlace(hi), "pred" -> CellArg.none)
      spush(lz, c1)
      zero = true
      jumping = false
      jt = None
      last = Some(c1)
      ncell = None
      if (hi.same(this.lo)) {
        ncell = Some(c1)
        active = false
      } else {
        wj = ctx.pleft(Some(hi))
        active = true
      }
    }

    // stack/queue helpers for cells

    private def spush(s: StackView, c: Cell): Unit = s.push(Some(c.node), c.slot)

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

    private def qpush(c: Cell): Unit = {
      a.push(Some(c.node), c.slot)
      a.work()
    }

    private def qpop(): Cell = {
      val (n, slot) = a.pop2()
      a.work()
      Cell(n.get, slot)
    }

    /** one unit; returns True while the scan continues. */
    def step(): Boolean = {
      if (!active) {
        false
      } else {
        val cj = ctx.psym(wj)
        val sCell = speek(lz)
        val created: Option[Cell] = if (ctx.psym(cells.getPlace(sCell, "wn")) == cj) {
          Some(matchUnit(sCell))
        } else if (zero) {
          val newc = cells.create("fail" -> CellArg.none, "wn" -> CellArg.place(wj), "pred" -> CellArg.cell(last))
          qpush(newc)
          Some(newc)
        } else {
          failureJumpUnit()
          None
        }
        created match {
          case None => true // retry the compare next unit
          case Some(newc) => advance(newc)
        }
      }
    }

    /** match at position s: fail(j) = s (matched length), s += 1 */
    private def matchUnit(sCell: Cell): Cell = {
      val newc = cells.create("fail" -> CellArg.OfCell(sCell), "wn" -> CellArg.place(wj), "pred" -> CellArg.cell(last))
      qpush(newc)
      if (!rz.empty) {
        spush(lz, spop(rz))
      } else {
        spush(lz, qpop())
      }
      zero = false
      newc
    }

    /** failure jump, one pop per unit: keep the target in `jt`, pop Lz into Rz until reached */
    private def failureJumpUnit(): Unit = {
      if (!jumping) {
        jt = cells.getCell(sbelow(lz).get, "fail")
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

    /** record the new cell and move the window cursor one place left; False when `lo` is reached */
    private def advance(newc: Cell): Boolean = {
      last = Some(newc)
      // Python `self.wj.same(self.lo)`: when the scan ran past the marker (wj is None,
      // i.e. `lo` was never met) this raises AttributeError; `.get` raises likewise.
      if (wj.get.same(lo)) {
        ncell = Some(newc)
        active = false
        false
      } else {
        wj = ctx.pleft(wj)
        true
      }
    }

    def save(): Unit = {
      lz.finish()
      rz.finish()
      a.finish()
      ctx.b.label(name + ".active") = active
      ctx.b.label(name + ".zero") = zero
      ctx.b.label(name + ".jumping") = jumping
      ctx.savePlace(name + ".lo", lo)
      ctx.savePlace(name + ".wj", wj)
      ctx.saveCell(name + ".last", last)
      ctx.saveCell(name + ".jt", jt)
      ctx.saveCell(name + ".ncell", ncell)
    }

    def failOf(cell: Cell): Option[Cell] = cells.getCell(cell, "fail")

    def wnOf(cell: Cell): Option[Place] = cells.getPlace(cell, "wn")

    def predOf(cell: Cell): Option[Cell] = cells.getCell(cell, "pred")
  }

  object KmpWindow {
    val PTR: Set[String] = Set("fail", "wn", "pred")
    val LAB: Set[String] = Set("fail.s", "wn.h", "pred.s")
  }

  // ------------------------------------------------------------------ marks + dp check

  /** Walk the failure chain F and the pred chain P of a KmpWindow from its ncell
    * in lockstep, creating one mark cell per position (descending) with bit `on` =
    * the position is on the failure chain (a palindrome ending at hi starts there).
    * Mark cells: ptr `below` (next lower position's mark), `kc` (the KMP cell), lab `on`.
    */
  final class Marks(val ctx: Ctx, val name: String, val kmp: KmpWindow) {
    import Marks.{LAB, PTR}

    val cells: Cells = new Cells(ctx, name + ".M", PTR, LAB)
    var active: Boolean = ctx.loadBool(name + ".active", false)
    var f: Option[Cell] = ctx.loadCell(name + ".F") // next chain cell to be met
    var p: Option[Cell] = ctx.loadCell(name + ".P") // current position cell
    var last: Option[Cell] = ctx.loadCell(name + ".last") // last mark created
    var top: Option[Cell] = ctx.loadCell(name + ".top") // mark of the highest position

    def start(): Unit = {
      val n = kmp.ncell
      f = n
      p = n
      last = None
      top = None
      active = true
    }

    def step(): Boolean = {
      if (!active) {
        false
      } else {
        val on = f.isDefined && p.get.same(f)
        val m = cells.create("below" -> CellArg.none, "kc" -> CellArg.cell(p), "on" -> CellArg.bool(on))
        // link the previous (higher) mark down to this one: impossible (immutable) —
        // so we link upwards instead: this mark points to the previous mark as `below`?
        // No: descending creation means the *newer* mark is the lower position; keep
        // `below` = None and let `up` = previous mark; cursors walk downwards via
        // the chain of creation, i.e. the later-created marks.  We therefore store
        // `up` (older = higher position) and walk from the *bottom* mark upwards
        // when a descending traversal is needed.  See DpCheck.
        cells.ctx.b.ptr(cells.key(m, "below")) = last.map(_.node)
        cells.ctx.b.label(cells.key(m, "below.s")) = last.fold(0)(_.slot)
        if (top.isEmpty) {
          top = Some(m)
        }
        last = Some(m)
        if (on) {
          f = kmp.failOf(f.get)
        }
        p = kmp.predOf(p.get)
        if (p.isEmpty) {
          active = false
          false
        } else {
          true
        }
      }
    }

    def save(): Unit = {
      ctx.b.label(name + ".active") = active
      ctx.saveCell(name + ".F", f)
      ctx.saveCell(name + ".P", p)
      ctx.saveCell(name + ".last", last)
      ctx.saveCell(name + ".top", top)
    }

    /** the mark of the next higher position */
    def upOf(m: Cell): Option[Cell] = cells.getCell(m, "below")

    def on(m: Cell): Boolean = cells.getLab(m, "on").asBool

    def kcOf(m: Cell): Option[Cell] = cells.getCell(m, "kc")
  }

  object Marks {
    val PTR: Set[String] = Set("below", "kc")
    val LAB: Set[String] = Set("below.s", "kc.s", "on")
  }

  /** Given the marks (bottom = position 1 = `last`, chain upwards via `upOf`),
    * find the smallest k > r such that positions 2k+1 and 4k+1 are both marked.
    * Cursor P2 walks 2 marks per unit, P4 walks 4 marks per unit, both upwards
    * from the bottom (position 1), so at unit k they sit at 2k+1 and 4k+1.  The
    * threshold r is given as the mark at position 2r+1 (`rmark`, None for r = 0):
    * k > r is enforced by skipping until P2 has passed rmark.  Stops when P4 runs
    * out (4k+1 > n).
    */
  final class DpCheck(val ctx: Ctx, val name: String, val marks: Marks) {
    var active: Boolean = ctx.loadBool(name + ".active", false)
    var p2: Option[Cell] = ctx.loadCell(name + ".P2")
    var p4: Option[Cell] = ctx.loadCell(name + ".P4")
    var rmark: Option[Cell] = ctx.loadCell(name + ".rmark")
    var passed: Boolean = ctx.loadBool(name + ".passed", false)
    var found: Option[Cell] = ctx.loadCell(name + ".found") // mark of position 2k+1 when found
    var found4: Option[Cell] = ctx.loadCell(name + ".found4")

    def start(rmark: Option[Cell]): Unit = {
      p2 = marks.last
      p4 = marks.last
      this.rmark = rmark
      passed = rmark.isEmpty
      found = None
      found4 = None
      active = true
    }

    private def walkUp(from: Option[Cell], count: Int): Option[Cell] = {
      (0 until count).foldLeft(from)((cur, _) => cur.flatMap(marks.upOf))
    }

    def step(): Boolean = {
      if (!active) {
        false
      } else {
        val next2 = walkUp(p2, 2)
        val next4 = walkUp(p4, 4)
        (next2, next4) match {
          case (Some(m2), Some(m4)) =>
            p2 = next2
            p4 = next4
            if (!passed) {
              if (rmark.isDefined && m2.same(rmark)) {
                passed = true
              }
              true
            } else if (marks.on(m2) && marks.on(m4)) {
              found = next2
              found4 = next4
              active = false
              false
            } else {
              true
            }
          case _ =>
            active = false
            false
        }
      }
    }

    def save(): Unit = {
      ctx.b.label(name + ".active") = active
      ctx.b.label(name + ".passed") = passed
      ctx.saveCell(name + ".P2", p2)
      ctx.saveCell(name + ".P4", p4)
      ctx.saveCell(name + ".rmark", rmark)
      ctx.saveCell(name + ".found", found)
      ctx.saveCell(name + ".found4", found4)
    }
  }

  // ------------------------------------------------------------------ tests

  /** Phase of the test driver `testKmpAndDp`: which component is being stepped.
    * Python では文字列 `'kmp' | 'marks' | 'dp' | 'done'`。
    */
  enum DrivePhase(val label: String) {
    case Kmp extends DrivePhase("kmp")
    case Marks extends DrivePhase("marks")
    case Dp extends DrivePhase("dp")
    case Done extends DrivePhase("done")
  }

  /** integer place -> Place over a list of nodes (place 2i+1 = node i). */
  def placeOf(nodes: IndexedSeq[Node], place: Int): Place = {
    val i = (place - 1) / 2
    Place(nodes(i), if (place % 2 == 1) { 0 } else { 1 })
  }

  private def feedInput(vm: VM, x: String): Vector[Node] = {
    x.map { c =>
      vm.begin()
      val b = new Builder
      b.ptr("prev") = vm.top
      b.label("c") = c.toString
      emit(vm, b)
    }.toVector
  }

  /** the mark of position 2r+1: walk up 2r from the bottom */
  private def thresholdMark(marks: Marks, r: Int): Option[Cell] = {
    if (r > 0) {
      (0 until 2 * r).foldLeft(marks.last)((rm, _) => marks.upOf(rm.get))
    } else {
      None
    }
  }

  /** k from the found mark: position of a mark = number of `pred` hops from its KMP cell */
  private def foundK(kmp: KmpWindow, marks: Marks, found: Cell): Int = {
    var kc = marks.kcOf(found)
    var cnt = 0
    while (kc.isDefined) {
      kc = kmp.predOf(kc.get)
      cnt += 1
    }
    (cnt - 1) / 2
  }

  /** brute force over the places string: the smallest k in (r, hmax] with palindromic
    * suffixes of lengths 2k+1 and 4k+1
    */
  private def bruteDoublePalindrome(x: String, lo: Int, hi: Int, r: Int): Option[Int] = {
    val places = "#" + x.flatMap(c => c.toString + SPACE)
    val win = places.substring(lo, hi + 1)
    val palLengths = (1 to win.length).filter { ell =>
      val suffix = win.takeRight(ell)
      suffix == suffix.reverse
    }.toSet
    val hmax = (hi - lo) / 4
    (r + 1 to hmax).find(k => palLengths.contains(2 * k + 1) && palLengths.contains(4 * k + 1))
  }

  /** Feed x into the VM (one node per symbol), then run KmpWindow over places
    * [lo, hi], Marks and DpCheck across further steps; compare with brute force.
    *
    * Python 版と同じく、入力を流す間は部品の状態を保存しないので、最初の追加ステップで
    * `RTQueueView` が入力節点から `K.A.phase` を読もうとして KeyError（Scala では
    * `NoSuchElementException`）になる。忠実に移植してある。
    */
  def testKmpAndDp(x: String, lo: Int, hi: Int, r: Int = 0): (Option[Int], Option[Int], Stats) = {
    val vm = new VM
    val nodes = feedInput(vm, x)
    // then drive the components over extra steps with dummy symbols
    var phase: DrivePhase = DrivePhase.Kmp
    var result: Option[Int] = None
    var extra = 0
    val limit = 4 * (hi - lo + 1) + 20
    while (extra < limit && phase != DrivePhase.Done) {
      vm.begin()
      val prev = vm.top
      val b = new Builder
      val ctx = new Ctx(vm, prev, b, "a")
      b.ptr("prev") = prev
      b.label("c") = "a"
      val kmp = new KmpWindow(ctx, "K")
      val marks = new Marks(ctx, "M", kmp)
      val dp = new DpCheck(ctx, "D", marks)
      if (extra == 0) {
        kmp.start(placeOf(nodes, lo), placeOf(nodes, hi))
        if (!kmp.active) {
          phase = DrivePhase.Marks
          marks.start()
        }
      } else {
        phase match {
          case DrivePhase.Kmp =>
            if (!kmp.step()) {
              phase = DrivePhase.Marks
              marks.start()
            }
          case DrivePhase.Marks =>
            if (!marks.step()) {
              phase = DrivePhase.Dp
              dp.start(thresholdMark(marks, r))
            }
          case DrivePhase.Dp =>
            if (!dp.step()) {
              phase = DrivePhase.Done
              result = dp.found.map(found => foundK(kmp, marks, found))
            }
          case DrivePhase.Done => ()
        }
      }
      kmp.save()
      marks.save()
      dp.save()
      emit(vm, b)
      extra += 1
    }
    (result, bruteDoublePalindrome(x, lo, hi, r), vm.stats)
  }

  /** `python3 scavm_pal.py` の移植（Python 版と同じ理由で最初の試行で例外になる）。 */
  def main(args: Array[String]): Unit = {
    val random = new PyRandom(11L)
    var bad = 0
    var tot = 0
    var worst = 0
    for (trial <- 0 until 300) {
      val n = random.randint(2, 14)
      var x = (0 until n).map(_ => random.choice("ab")).mkString
      if (trial % 3 == 0) {
        val p = (0 until random.randint(1, 3)).map(_ => random.choice("ab")).mkString
        x = (p * 8).take(n)
      }
      val hi = random.randint(1, 2 * n)
      val lo = random.randint(1, hi)
      val r = random.choice(Vector(0, 0, 1, 2))
      val (got, exp, st) = testKmpAndDp(x, lo, hi, r)
      tot += 1
      if (got != exp) {
        bad += 1
        if (bad <= 5) {
          println(s"BAD $x $lo $hi $r got ${got.fold("None")(_.toString)} exp ${exp.fold("None")(_.toString)}")
        }
      }
      worst = math.max(worst, st.radius)
    }
    println(s"kmp+marks+dp: $tot trials, bad $bad, max hops/step $worst")
  }
}
