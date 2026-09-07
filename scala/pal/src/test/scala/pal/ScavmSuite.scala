package pal

import Scavm.{Label, Node, Self, Stack, Stats, VM, demoExtensionOnly, sameTarget}

/** `scavm.py` の観測可能な振る舞いを固定する（Python 版にはテストファイルがない）。 */
class ScavmSuite extends munit.FunSuite {

  private def feed(vm: VM, label: Label): Node = {
    vm.begin()
    vm.emit(label, Seq("prev" -> vm.top))
  }

  test("demo_extension_only('abba') and (ab)^50 as in python") {
    val (outs, st) = demoExtensionOnly("abba")
    assertEquals(outs, Vector(1, 0, 0, 0))
    assertEquals(st, Stats(steps = 4, radius = 1, fields = 2, labels = 3))
    val (outs2, st2) = demoExtensionOnly("ab" * 50)
    assertEquals(outs2.takeRight(4), Vector(0, 0, 0, 0))
    assertEquals(st2, Stats(steps = 100, radius = 2, fields = 2, labels = 3))
  }

  test("main prints exactly what python3 scavm.py prints") {
    PyDiff.assertSameAsPython(TestUtil.captureStdout(Scavm.main(Array.empty)), "scavm.py")
  }

  test("demo on '', 'aa', 'aab', 'aba' (values taken from python)") {
    // the first node stores L = None (the marker), so a second symbol can never extend it:
    // the demo tracks the palindrome centred at the middle of the whole string only
    assertEquals(demoExtensionOnly(""), (Vector.empty[Int], Stats(0, 0, 0, 0)))
    assertEquals(demoExtensionOnly("aa"), (Vector(1, 0), Stats(2, 1, 2, 2)))
    assertEquals(demoExtensionOnly("aab"), (Vector(1, 0, 0), Stats(3, 1, 2, 3)))
    assertEquals(demoExtensionOnly("aba"), (Vector(1, 0, 1), Stats(3, 2, 2, 2)))
  }

  test("VM: t starts at -1, begin advances it, emit sets top and steps") {
    val vm = new VM
    assertEquals(vm.t, -1)
    assertEquals(vm.top, None)
    val n0 = feed(vm, Label.Num(0))
    assertEquals(vm.t, 0)
    assert(vm.top.exists(_ eq n0))
    assertEquals(n0.t, 0)
    assertEquals(vm.stats, Stats(1, 0, 1, 1))
  }

  test("VM.get follows a pointer, counts a hop and makes the target reachable") {
    val vm = new VM
    val n0 = feed(vm, Label.Num(0))
    val n1 = feed(vm, Label.Num(1))
    vm.begin()
    assertEquals(vm.hops, 0)
    val back = vm.get(n1, "prev")
    assert(back.exists(_ eq n0))
    assertEquals(vm.hops, 1)
    assertEquals(vm.label(n0), Label.Num(0)) // n0 was touched this step
    assertEquals(vm.get(n0, "prev"), None)
    assertEquals(vm.get(n0, "missing"), None) // absent field: None, still one hop
    assertEquals(vm.hops, 3)
    vm.emit(Label.Num(2), Seq("prev" -> Some(n1), "far" -> Some(n0)))
    assertEquals(vm.radius, 3)
  }

  test("VM.get / label on a node not reached this step is an assertion error") {
    val vm = new VM
    val n0 = feed(vm, Label.Num(0))
    feed(vm, Label.Num(1))
    vm.begin()
    val e = intercept[AssertionError](vm.get(n0, "prev"))
    assert(e.getMessage.contains("not reachable this step"), e.getMessage)
    intercept[AssertionError](vm.label(n0))
  }

  test("VM.emit rejects pointers to nodes not reached this step") {
    val vm = new VM
    val n0 = feed(vm, Label.Num(0))
    val n1 = feed(vm, Label.Num(1))
    vm.begin()
    val e = intercept[AssertionError](vm.emit(Label.Num(2), Seq("prev" -> Some(n1), "far" -> Some(n0))))
    assert(e.getMessage.contains("pointer far"), e.getMessage)
  }

  test("VM.emit resolves Self to the created node") {
    val vm = new VM
    vm.begin()
    val n = vm.emit(Label.Null, Seq("me" -> Some(Self), "none" -> None))
    assert(n.pointer("me").exists(_ eq n))
    assertEquals(n.pointer("none"), None)
    assertEquals(n.pointers.keys.toVector, Vector("me", "none"))
    vm.begin()
    assert(vm.get(n, "me").exists(_ eq n)) // a self pointer is not "newer"
  }

  test("VM.emit checks the finite label shape") {
    val vm = new VM
    vm.begin()
    intercept[AssertionError](vm.emit(Label.Num(65), Seq.empty))
    intercept[AssertionError](vm.emit(Label.Num(-65), Seq.empty))
    intercept[AssertionError](vm.emit(Label.Str("a" * 17), Seq.empty))
    intercept[AssertionError](vm.emit(Label.tuple(Label.Num(1), Label.Str("b" * 17)), Seq.empty))
    intercept[AssertionError](vm.emit(Label.Dict(Vector("k" -> Label.Num(100))), Seq.empty))
    vm.emit(Label.tuple(Label.Num(64), Label.Num(-64), Label.Str("a" * 16), Label.Bool(true), Label.Null), Seq.empty)
    assertEquals(vm.stats.labels, 1)
  }

  test("stats count distinct labels and the maximal number of fields") {
    val vm = new VM
    feed(vm, Label.Dict(Vector("a" -> Label.Num(1))))
    feed(vm, Label.Dict(Vector("a" -> Label.Num(1))))
    feed(vm, Label.Dict(Vector("a" -> Label.Num(2))))
    vm.begin()
    vm.emit(Label.Dict(Vector("a" -> Label.Num(2))), Seq("prev" -> vm.top, "x" -> None, "y" -> None))
    assertEquals(vm.stats, Stats(steps = 4, radius = 0, fields = 3, labels = 2))
  }

  test("Label: dict lookup, tuple index, accessors and python repr") {
    val d = Label.Dict(Vector("k" -> Label.Str("v"), "n" -> Label.Num(3), "b" -> Label.Bool(true), "z" -> Label.Null))
    assertEquals(d("k").asStr, "v")
    assertEquals(d("n").asInt, 3)
    assertEquals(d("b").asBool, true)
    assertEquals(d("b").asInt, 1)
    assert(d("z").isNull)
    assertEquals(d.get("missing"), None)
    val e = intercept[NoSuchElementException](d("missing"))
    assert(e.getMessage.contains("missing"))
    intercept[IllegalArgumentException](d(0))
    intercept[IllegalArgumentException](d("k").asInt)
    val t = Label.tuple(Label.Str("sym"), Label.Str("a"), Label.Num(1))
    assertEquals(t(1), Label.Str("a"))
    assertEquals(t.pythonRepr, "('sym', 'a', 1)")
    assertEquals(Label.tuple(Label.Num(1)).pythonRepr, "(1,)")
    assertEquals(Label.tuple().pythonRepr, "()")
    assertEquals(d.pythonRepr, "{'k': 'v', 'n': 3, 'b': True, 'z': None}")
    assertEquals(Label.Str("it's").pythonRepr, "\"it's\"")
    assertEquals(Label.Str("a\\b\n").pythonRepr, "'a\\\\b\\n'")
    assertEquals(Label.Bool(false).pythonRepr, "False")
  }

  test("LabelMap keeps insertion order and overwrites in place") {
    val m = new Scavm.LabelMap
    m("a") = 1
    m("b") = "x"
    m("c") = true
    m("a") = Label.Num(2)
    assertEquals(m.toVector, Vector("a" -> Label.Num(2), "b" -> Label.Str("x"), "c" -> Label.Bool(true)))
    assertEquals(m.size, 3)
    assert(m.contains("b"))
    assertEquals(m.get("d"), None)
    intercept[NoSuchElementException](m("d"))
    assertEquals(m.toLabel("b"), Label.Str("x"))
  }

  test("Node.toString mirrors python repr N<t><label>") {
    val vm = new VM
    val n = feed(vm, Label.tuple(Label.Str("sym"), Label.Str("a"), Label.Num(1)))
    assertEquals(n.toString, "N0('sym', 'a', 1)")
  }

  test("sameTarget is identity, with None == None") {
    val vm = new VM
    val n0 = feed(vm, Label.Num(0))
    val n1 = feed(vm, Label.Num(1))
    assert(sameTarget(None, None))
    assert(sameTarget(Some(n0), Some(n0)))
    assert(sameTarget(Some(Self), Some(Self)))
    assert(!sameTarget(Some(n0), Some(n1)))
    assert(!sameTarget(Some(n0), None))
  }

  test("Stack placeholder: empty iff no <name>_top pointer") {
    val vm = new VM
    val s = new Stack("S")
    assert(s.empty(vm, None))
    vm.begin()
    val n = vm.emit(Label.Null, Seq("S_top" -> None))
    vm.begin()
    assert(s.empty(vm, Some(n)))
    val m = vm.emit(Label.Null, Seq("S_top" -> Some(n)))
    vm.begin()
    assert(!s.empty(vm, Some(m)))
  }
}
