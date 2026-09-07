package pal

import Scavm.{Label, Node, NodeRef, Self, VM}
import ScavmStructs.{Builder, emit}
import ScavmPal.{Cell, CellArg, Cells, Ctx, DpCheck, KmpWindow, Marks, Place, SPACE, placeOf, testKmpAndDp}

/** `scavm_pal.py` の観測可能な振る舞いを固定する。
  *
  * Python 版の `test_kmp_and_dp` / `__main__` は自身のバグ（入力を流す間に部品の状態を
  * 保存しないので最初の追加ステップで KeyError）で動かない。そこでこのスイートでは、
  * 入力ステップでも `save()` する「直した」ドライバを Python と Scala の両方で走らせ、
  * 300 試行の結果・ステップ数・単位ごとのトレース・VM 統計が完全一致することを検査する。
  */
class ScavmPalSuite extends munit.FunSuite {

  // ------------------------------------------------------------------ small pieces

  private def feed(vm: VM, x: String): Vector[Node] = {
    x.map { c =>
      vm.begin()
      val b = new Builder
      b.ptr("prev") = vm.top
      b.label("c") = c.toString
      emit(vm, b)
    }.toVector
  }

  /** `prev` から `prev` ポインタを辿って `target` を今ステップの到達済みにする。 */
  private def reach(vm: VM, start: Node, target: NodeRef): Unit = {
    var node = start
    while (!(node eq target)) {
      node = vm.get(node, "prev").get
    }
  }

  test("Place / Cell `same` is node identity plus half/slot equality") {
    val vm = new VM
    val nodes = feed(vm, "ab")
    assert(Place(nodes(0), 0).same(Some(Place(nodes(0), 0))))
    assert(!Place(nodes(0), 0).same(Some(Place(nodes(0), 1))))
    assert(!Place(nodes(0), 0).same(Some(Place(nodes(1), 0))))
    assert(!Place(nodes(0), 0).same(None))
    assert(Cell(Self, 2).same(Some(Cell(Self, 2))))
    assert(!Cell(Self, 2).same(Some(Cell(Self, 3))))
    assert(!Cell(nodes(0), 0).same(None))
  }

  test("placeOf: place 2i+1 is (node i, 0) and 2i+2 is (node i, 1)") {
    val vm = new VM
    val nodes = feed(vm, "abc")
    assertEquals(placeOf(nodes, 1), Place(nodes(0), 0))
    assertEquals(placeOf(nodes, 2), Place(nodes(0), 1))
    assertEquals(placeOf(nodes, 5), Place(nodes(2), 0))
    assertEquals(placeOf(nodes, 6), Place(nodes(2), 1))
  }

  test("Ctx.pleft / psym walk the places string '#a_b_c_' leftwards") {
    val vm = new VM
    val nodes = feed(vm, "abc")
    vm.begin()
    val b = new Builder
    val ctx = new Ctx(vm, vm.top, b, "z")
    var p: Option[Place] = Some(placeOf(nodes, 6))
    val syms = Vector.newBuilder[Option[String]]
    while (p.isDefined) {
      syms += ctx.psym(p)
      p = ctx.pleft(p)
    }
    syms += ctx.psym(None)
    assertEquals(syms.result(), Vector(Some(SPACE), Some("c"), Some(SPACE), Some("b"), Some(SPACE), Some("a"), None))
    assertEquals(ctx.pleft(None), None)
    assertEquals(ctx.sym(Self), "z")
    assertEquals(ctx.psym(Some(Place(Self, 0))), Some("z"))
    assertEquals(ctx.psym(Some(Place(Self, 1))), Some(SPACE))
  }

  test("Ctx.get / lab are Self-aware; save/load of places, cells and labels round-trip") {
    val vm = new VM
    val nodes = feed(vm, "ab")
    vm.begin()
    val b = new Builder
    val ctx = new Ctx(vm, vm.top, b, "z")
    assertEquals(ctx.get(Self, "nothing"), None)
    assertEquals(ctx.lab(Self, "nothing"), Label.Null)
    b.ptr("p") = Some(nodes(0))
    b.label("l") = 5
    assertEquals(ctx.get(Self, "p"), Some(nodes(0)))
    assertEquals(ctx.lab(Self, "l"), Label.Num(5))
    assertEquals(ctx.get(nodes(1), "prev"), Some(nodes(0)))
    assertEquals(ctx.lab(nodes(1), "c"), Label.Str("b"))
    intercept[NoSuchElementException](ctx.lab(nodes(1), "nothing"))
    ctx.savePlace("pl", Some(Place(nodes(1), 1)))
    ctx.savePlace("pn", None)
    ctx.saveCell("ce", Some(Cell(nodes(1), 3)))
    ctx.saveCell("cn", None)
    b.label("flag") = true
    assertEquals(b.ptr("pn"), None)
    assertEquals(b.label("pn.h"), Label.Num(0))
    assertEquals(b.label("cn.s"), Label.Num(0))
    val n = emit(vm, b)
    vm.begin()
    val ctx2 = new Ctx(vm, Some(n), new Builder, "z")
    assertEquals(ctx2.loadPlace("pl"), Some(Place(nodes(1), 1)))
    assertEquals(ctx2.loadPlace("pn"), None)
    assertEquals(ctx2.loadCell("ce"), Some(Cell(nodes(1), 3)))
    assertEquals(ctx2.loadCell("cn"), None)
    assertEquals(ctx2.loadLab("flag", Label.Bool(false)), Label.Bool(true))
    assertEquals(ctx2.loadBool("flag", false), true)
    val fresh = new Ctx(vm, None, new Builder, "z")
    assertEquals(fresh.loadPlace("pl"), None)
    assertEquals(fresh.loadCell("ce"), None)
    assertEquals(fresh.loadBool("flag", true), true)
  }

  test("Cells.create writes the field layout of python Cells.new, and get* read it back") {
    val vm = new VM
    val nodes = feed(vm, "ab")
    vm.begin()
    val b = new Builder
    val ctx = new Ctx(vm, vm.top, b, "z")
    val cells = new Cells(ctx, "X.K", KmpWindow.PTR, KmpWindow.LAB)
    val c0 = cells.create("fail" -> CellArg.none, "wn" -> CellArg.OfPlace(Place(nodes(1), 1)), "pred" -> CellArg.none)
    val c1 = cells.create("fail" -> CellArg.OfCell(c0), "wn" -> CellArg.place(None), "pred" -> CellArg.cell(Some(c0)))
    assertEquals(c0, Cell(Self, 0))
    assertEquals(c1, Cell(Self, 1))
    assertEquals(
      b.label.toVector.map(_._1),
      Vector("X.K.0.fail.s", "X.K.0.wn.h", "X.K.0.pred.s", "X.K.1.fail.s", "X.K.1.wn.h", "X.K.1.pred.s")
    )
    assertEquals(b.ptr.keys.toVector, Vector("X.K.0.fail", "X.K.0.wn", "X.K.0.pred", "X.K.1.fail", "X.K.1.wn", "X.K.1.pred"))
    assertEquals(cells.getCell(c0, "fail"), None)
    assertEquals(cells.getPlace(c0, "wn"), Some(Place(nodes(1), 1)))
    assertEquals(cells.getCell(c1, "fail"), Some(c0))
    assertEquals(cells.getPlace(c1, "wn"), None)
    assertEquals(cells.getCell(c1, "pred"), Some(c0))
    val m = new Cells(ctx, "M", Marks.PTR, Marks.LAB)
    val mk = m.create("below" -> CellArg.none, "kc" -> CellArg.OfCell(c1), "on" -> CellArg.bool(true))
    assertEquals(m.getLab(mk, "on"), Label.Bool(true))
    assertEquals(m.getCell(mk, "kc"), Some(c1))
    intercept[IllegalArgumentException](m.create("on" -> CellArg.none))
    // across a step the Self references resolve to the emitted node
    val n = emit(vm, b)
    vm.begin()
    val ctx2 = new Ctx(vm, Some(n), new Builder, "z")
    val cells2 = new Cells(ctx2, "X.K", KmpWindow.PTR, KmpWindow.LAB)
    assertEquals(cells2.getCell(Cell(n, 1), "fail"), Some(Cell(n, 0)))
    assertEquals(cells2.getPlace(Cell(n, 0), "wn"), Some(Place(nodes(1), 1)))
  }

  // ------------------------------------------------------------------ the fixed driver

  /** Python 側のドライバ（Scala の `drive` と 1 行ずつ同じものを印字する）。 */
  private val pythonDriver =
    """import random
      |from scavm import VM
      |from scavm_structs import Builder, emit
      |from scavm_pal import Ctx, KmpWindow, Marks, DpCheck, _place_of, SPACE
      |
      |def reach(vm, start, target):
      |    node = start
      |    while node is not target:
      |        node = vm.get(node, 'prev')
      |
      |def drive(x, lo, hi, r):
      |    vm = VM(); nodes = []
      |    for c in x:
      |        vm.begin(); b = Builder(); ctx = Ctx(vm, vm.top, b, c)
      |        b.ptr['prev'] = vm.top; b.label['c'] = c
      |        K = KmpWindow(ctx, 'K'); M = Marks(ctx, 'M', K); D = DpCheck(ctx, 'D', M)
      |        K.save(); M.save(); D.save(); nodes.append(emit(vm, b))
      |    phase = 'kmp'; result = None; steps = 0; trace = []
      |    for extra in range(4 * (hi - lo + 1) + 20):
      |        vm.begin(); prev = vm.top; b = Builder(); ctx = Ctx(vm, prev, b, 'a')
      |        b.ptr['prev'] = prev; b.label['c'] = 'a'
      |        K = KmpWindow(ctx, 'K'); M = Marks(ctx, 'M', K); D = DpCheck(ctx, 'D', M)
      |        if extra == 0:
      |            reach(vm, prev, _place_of(nodes, lo).node); reach(vm, prev, _place_of(nodes, hi).node)
      |            K.start(_place_of(nodes, lo), _place_of(nodes, hi))
      |            if not K.active:
      |                phase = 'marks'; M.start()
      |        elif phase == 'kmp':
      |            if not K.step():
      |                phase = 'marks'; M.start()
      |        elif phase == 'marks':
      |            if not M.step():
      |                phase = 'dp'
      |                rmark = None
      |                if r > 0:
      |                    rm = M.last
      |                    for _ in range(2 * r):
      |                        if rm is not None:
      |                            rm = M.up_of(rm)
      |                    if rm is None:
      |                        r = 0
      |                    rmark = rm
      |                D.start(rmark)
      |        elif phase == 'dp':
      |            if not D.step():
      |                phase = 'done'
      |                if D.found is not None:
      |                    kc = M.kc_of(D.found); cnt = 0
      |                    while kc is not None:
      |                        kc = K.pred_of(kc); cnt += 1
      |                    result = (cnt - 1) // 2
      |        steps += 1
      |        trace.append(phase[0] + str(K.zero * 1) + str(K.jumping * 1) + str(vm.hops))
      |        K.save(); M.save(); D.save(); emit(vm, b)
      |        if phase == 'done':
      |            break
      |    places = '#' + ''.join(c + SPACE for c in x)
      |    win = places[lo:hi + 1]
      |    pal_lengths = {ell for ell in range(1, len(win) + 1) if win[-ell:] == win[-ell:][::-1]}
      |    hmax = (hi - lo) // 4
      |    exp = next((k for k in range(r + 1, hmax + 1) if (2*k+1) in pal_lengths and (4*k+1) in pal_lengths), None)
      |    return result, exp, steps, ''.join(trace), vm.stats(), r
      |
      |random.seed(11)
      |bad = 0
      |for trial in range(300):
      |    n = random.randint(2, 14)
      |    x = ''.join(random.choice('ab') for _ in range(n))
      |    if trial % 3 == 0:
      |        p = ''.join(random.choice('ab') for _ in range(random.randint(1, 3))); x = (p * 8)[:n]
      |    n = len(x); hi = random.randint(1, 2 * n); lo = random.randint(1, hi); r = random.choice([0, 0, 1, 2])
      |    got, exp, steps, trace, st, r = drive(x, lo, hi, r)
      |    bad += got != exp
      |    print(x, lo, hi, r, got, exp, steps, trace, st['radius'], st['fields'], st['labels'])
      |print('bad', bad)
      |""".stripMargin

  private final case class Driven(result: Option[Int], expected: Option[Int], steps: Int, trace: String, radius: Int, fields: Int, labels: Int, r: Int)

  private def bruteExpected(x: String, lo: Int, hi: Int, r: Int): Option[Int] = {
    val places = "#" + x.flatMap(c => c.toString + SPACE)
    val win = places.substring(lo, hi + 1)
    val palLengths = (1 to win.length).filter { ell =>
      val suffix = win.takeRight(ell)
      suffix == suffix.reverse
    }.toSet
    val hmax = (hi - lo) / 4
    (r + 1 to hmax).find(k => palLengths.contains(2 * k + 1) && palLengths.contains(4 * k + 1))
  }

  /** the mark of position 2r+1 (walk up 2r from the bottom); `None` (and r = 0) if the chain is shorter */
  private def thresholdMark(marks: Marks, r: Int): (Option[Cell], Int) = {
    if (r > 0) {
      val rm = (0 until 2 * r).foldLeft(marks.last)((cur, _) => cur.flatMap(marks.upOf))
      (rm, if (rm.isEmpty) { 0 } else { r })
    } else {
      (None, 0)
    }
  }

  private def foundK(kmp: KmpWindow, marks: Marks, found: Cell): Int = {
    var kc = marks.kcOf(found)
    var cnt = 0
    while (kc.isDefined) {
      kc = kmp.predOf(kc.get)
      cnt += 1
    }
    (cnt - 1) / 2
  }

  /** the Python driver above, in Scala. */
  private def drive(x: String, lo: Int, hi: Int, r0: Int): Driven = {
    val vm = new VM
    val nodes = x.map { c =>
      vm.begin()
      val b = new Builder
      val ctx = new Ctx(vm, vm.top, b, c.toString)
      b.ptr("prev") = vm.top
      b.label("c") = c.toString
      val k = new KmpWindow(ctx, "K")
      val m = new Marks(ctx, "M", k)
      val d = new DpCheck(ctx, "D", m)
      k.save()
      m.save()
      d.save()
      emit(vm, b)
    }.toVector
    var phase = "kmp"
    var result: Option[Int] = None
    var steps = 0
    var r = r0
    val trace = new StringBuilder
    var extra = 0
    val limit = 4 * (hi - lo + 1) + 20
    while (extra < limit && phase != "done") {
      vm.begin()
      val prev = vm.top
      val b = new Builder
      val ctx = new Ctx(vm, prev, b, "a")
      b.ptr("prev") = prev
      b.label("c") = "a"
      val k = new KmpWindow(ctx, "K")
      val m = new Marks(ctx, "M", k)
      val d = new DpCheck(ctx, "D", m)
      if (extra == 0) {
        reach(vm, prev.get, placeOf(nodes, lo).node)
        reach(vm, prev.get, placeOf(nodes, hi).node)
        k.start(placeOf(nodes, lo), placeOf(nodes, hi))
        if (!k.active) {
          phase = "marks"
          m.start()
        }
      } else if (phase == "kmp") {
        if (!k.step()) {
          phase = "marks"
          m.start()
        }
      } else if (phase == "marks") {
        if (!m.step()) {
          phase = "dp"
          val (rmark, effective) = thresholdMark(m, r)
          r = effective
          d.start(rmark)
        }
      } else if (phase == "dp") {
        if (!d.step()) {
          phase = "done"
          result = d.found.map(found => foundK(k, m, found))
        }
      }
      steps += 1
      trace.append(phase.head).append(if (k.zero) { 1 } else { 0 }).append(if (k.jumping) { 1 } else { 0 }).append(vm.hops)
      k.save()
      m.save()
      d.save()
      emit(vm, b)
      extra += 1
    }
    val st = vm.stats
    Driven(result, bruteExpected(x, lo, hi, r), steps, trace.toString, st.radius, st.fields, st.labels, r)
  }

  private def pyOpt(o: Option[Int]): String = o.fold("None")(_.toString)

  private def scalaDriverOutput: String = {
    val random = new PyRandom(11L)
    val sb = new StringBuilder
    var bad = 0
    for (trial <- 0 until 300) {
      val n0 = random.randint(2, 14)
      var x = (0 until n0).map(_ => random.choice("ab")).mkString
      if (trial % 3 == 0) {
        val p = (0 until random.randint(1, 3)).map(_ => random.choice("ab")).mkString
        x = (p * 8).take(n0)
      }
      val n = x.length
      val hi = random.randint(1, 2 * n)
      val lo = random.randint(1, hi)
      val r = random.choice(Vector(0, 0, 1, 2))
      val d = drive(x, lo, hi, r)
      if (d.result != d.expected) {
        bad += 1
      }
      sb.append(s"$x $lo $hi ${d.r} ${pyOpt(d.result)} ${pyOpt(d.expected)} ${d.steps} ${d.trace} ${d.radius} ${d.fields} ${d.labels}\n")
    }
    sb.append(s"bad $bad\n")
    sb.toString
  }

  test("KmpWindow + Marks + DpCheck: 300 driven trials match python line by line") {
    val out = scalaDriverOutput
    assert(out.linesIterator.exists(_.startsWith("bad ")))
    PyDiff.assertSameAsPython(out, "-c", pythonDriver)
  }

  test("KmpWindow on a window of length 1 is complete at start; Marks makes one mark") {
    val d = drive("ab", 3, 3, 0)
    assertEquals(d.result, None)
    assertEquals(d.trace.head, 'm')
  }

  test("a genuine double palindrome is found: window 'aaaaaaaaa' (places of a^5) gives k = 1") {
    // places '#a_a_a_a_a_' [1..9] = 'a_a_a_a_a' has palindromic suffixes of length 3 and 5: k = 1
    val d = drive("aaaaa", 1, 9, 0)
    assertEquals(d.expected, Some(1))
    assertEquals(d.result, Some(1))
  }

  // ------------------------------------------------------------------ the python bug, pinned

  test("testKmpAndDp fails like python (KeyError 'K.A.phase' on the first extra step)") {
    val e = intercept[NoSuchElementException](testKmpAndDp("ab", 1, 2))
    assert(e.getMessage.contains("K.A.phase"), e.getMessage)
    intercept[NoSuchElementException](ScavmPal.main(Array.empty))
    val py = PyDiff.python("-c", "import subprocess,sys; p=subprocess.run([sys.executable,'scavm_pal.py'],capture_output=True,text=True); print(p.returncode); print(p.stderr.strip().splitlines()[-1])")
    assertEquals(py, "1\nKeyError: 'K.A.phase'\n")
  }
}
