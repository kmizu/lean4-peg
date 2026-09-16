package pal

import Scavm.{Label, Node, NodeRef, Self, Stats, VM, sameTarget}
import ScavmStructs.{Builder, CounterView, RTQueueView, StackCell, StackView, emit, testQueue, testStack}

/** `scavm_structs.py` の観測可能な振る舞いを固定する。 */
class ScavmStructsSuite extends munit.FunSuite {

  /** 1 ステップ: builder を作り、`body` で構造を触り、`finish` した結果を emit する。 */
  private def step[A](vm: VM)(body: (Builder, Option[Node]) => A)(finish: A => Unit): Node = {
    vm.begin()
    val b = new Builder
    val view = body(b, vm.top)
    finish(view)
    emit(vm, b)
  }

  test("python's own test_stack / test_queue statistics") {
    assertEquals(testStack(), Stats(steps = 200, radius = 5, fields = 7, labels = 17))
    assertEquals(testQueue(), Stats(steps = 3000, radius = 29, fields = 43, labels = 329))
  }

  test("main prints exactly what python3 scavm_structs.py prints") {
    PyDiff.assertSameAsPython(TestUtil.captureStdout(ScavmStructs.main(Array.empty)), "scavm_structs.py")
  }

  test("Builder hands out per-name slot indices in order") {
    val b = new Builder
    assertEquals(b.slot("S"), 0)
    assertEquals(b.slot("S"), 1)
    assertEquals(b.slot("T"), 0)
    assertEquals(b.slot("S"), 2)
  }

  test("StackView: push across steps, then pop in LIFO order, one cell per step") {
    val vm = new VM
    val nodes = (0 until 4).map { i =>
      step(vm) { (b, prev) =>
        val s = new StackView(vm, prev, b, "S")
        assertEquals(s.empty, i == 0)
        s.push(prev, vslot = i)
        s
      }(_.finish())
    }
    // the values were the previous tops: None, n0, n1, n2
    val popped = (0 until 4).map { _ =>
      var got: (Option[NodeRef], Int) = (None, -1)
      step(vm) { (b, prev) =>
        val s = new StackView(vm, prev, b, "S")
        got = s.pop2()
        s
      }(_.finish())
      got
    }
    assert(sameTarget(popped(0)._1, Some(nodes(2))))
    assertEquals(popped(0)._2, 3)
    assert(sameTarget(popped(1)._1, Some(nodes(1))))
    assert(sameTarget(popped(2)._1, Some(nodes(0))))
    assert(sameTarget(popped(3)._1, None))
    assertEquals(popped(3)._2, 0)
    step(vm) { (b, prev) =>
      val s = new StackView(vm, prev, b, "S")
      assert(s.empty)
      intercept[NoSuchElementException](s.pop())
      s
    }(_.finish())
  }

  test("StackView: cells created this step are addressed by Self; peek/peek2/belowOfTop") {
    val vm = new VM
    val n0 = step(vm) { (b, prev) => new StackView(vm, prev, b, "S") }(_.finish())
    step(vm) { (b, prev) =>
      val s = new StackView(vm, prev, b, "S")
      s.push(Some(n0), 1)
      s.push(Some(Self), 2)
      assertEquals(s.top, Some(StackCell(Self, "S", 1)))
      assert(sameTarget(s.peek, Some(Self)))
      assertEquals(s.peek2._2, 2)
      val below = s.belowOfTop
      assert(below.exists { case (v, vs) => sameTarget(v, Some(n0)) && vs == 1 })
      assertEquals(b.ptr("S.1.below"), Some(Self))
      assertEquals(b.label("S.1.bname"), Label.Str("S"))
      assertEquals(b.label("S.1.bslot"), Label.Num(0))
      assertEquals(b.label("S.0.bname"), Label.Str(""))
      s
    } { s =>
      s.finish()
      assertEquals(s.b.ptr("S.top"), Some(Self))
      assertEquals(s.b.label("S.tname"), Label.Str("S"))
      assertEquals(s.b.label("S.tslot"), Label.Num(1))
    }
    step(vm) { (b, prev) =>
      val s = new StackView(vm, prev, b, "S")
      assertEquals(s.top.map(_.slot), Some(1))
      assert(sameTarget(s.pop(), prev)) // Self became the previous node
      assertEquals(s.belowOfTop, None)
      assert(sameTarget(s.pop(), Some(n0)))
      assert(s.empty)
      s
    }(_.finish())
  }

  test("StackView.copyFrom aliases another stack's chain and keeps the creator's field names") {
    val vm = new VM
    step(vm) { (b, prev) =>
      val s = new StackView(vm, prev, b, "S")
      val t = new StackView(vm, prev, b, "T")
      s.push(None, 7)
      t.copyFrom(s)
      assertEquals(t.top, Some(StackCell(Self, "S", 0)))
      (s, t)
    } { case (s, t) =>
      s.finish()
      t.finish()
      assertEquals(t.b.label("T.tname"), Label.Str("S"))
    }
    step(vm) { (b, prev) =>
      val t = new StackView(vm, prev, b, "T")
      assertEquals(t.pop2()._2, 7)
      assert(t.empty)
      t
    }(_.finish())
  }

  test("CounterView: inc/dec/sign across steps and reset") {
    val vm = new VM
    def apply(ops: String): Int = {
      var sign = 0
      step(vm) { (b, prev) =>
        val c = new CounterView(vm, prev, b, "c")
        for (op <- ops) {
          op match {
            case '+' => c.inc()
            case '-' => c.dec()
            case '0' => c.reset()
            case _ => ()
          }
        }
        sign = c.sign
        c
      }(_.finish())
      sign
    }
    assertEquals(apply(""), 0)
    assertEquals(apply("+"), 1)
    assertEquals(apply("+"), 1)
    assertEquals(apply("-"), 1)
    assertEquals(apply("-"), 0)
    assertEquals(apply("-"), -1)
    assertEquals(apply("--"), -1)
    assertEquals(apply("+++"), 0)
    assertEquals(apply("+"), 1)
    assertEquals(apply("0"), 0)
    assertEquals(apply("-"), -1)
  }

  test("RTQueueView: FIFO across steps with the real-time rotation") {
    val vm = new VM
    val pushed = scala.collection.mutable.ArrayDeque.empty[Option[NodeRef]]
    val ops = "p" * 7 + "o" * 3 + "p" * 13 + "o" * 17
    for ((op, t) <- ops.zipWithIndex) {
      step(vm) { (b, prev) =>
        val q = new RTQueueView(vm, prev, b, "Q")
        if (op == 'p') {
          q.push(prev, t)
          pushed.append(prev)
        } else {
          val (got, vs) = q.pop2()
          val exp = pushed.removeHead()
          assert(sameTarget(got, exp), s"step $t")
          assert(vs >= 0)
        }
        q.work()
        assertEquals(q.empty, pushed.isEmpty, s"step $t phase ${q.phase}")
        q
      }(_.finish())
    }
    assertEquals(vm.stats.steps, ops.length)
  }

  test("RTQueueView: phase is persisted in the label, NAMES order, clear") {
    val vm = new VM
    val n = step(vm) { (b, prev) =>
      val q = new RTQueueView(vm, prev, b, "Q")
      assertEquals(q.phase, RTQueueView.Phase.Idle)
      assertEquals(q.s.keys.toVector, RTQueueView.NAMES)
      q.push(None)
      q.work() // c < 0 -> a rotation starts and finishes within ROT units
      q
    }(_.finish())
    assertEquals(n.label("Q.phase"), Label.Str("idle"))
    step(vm) { (b, prev) =>
      val q = new RTQueueView(vm, prev, b, "Q")
      assert(!q.empty)
      q.clear()
      assert(q.empty)
      assertEquals(q.phase, RTQueueView.Phase.Idle)
      intercept[AssertionError](q.pop())
      q
    }(_.finish())
    assertEquals(RTQueueView.Phase.fromLabel(Label.Str("copy")), RTQueueView.Phase.Copy)
    intercept[IllegalArgumentException](RTQueueView.Phase.fromLabel(Label.Str("nope")))
  }

  test("RTQueueView on a node without the queue's fields is a KeyError, as in python") {
    val vm = new VM
    vm.begin()
    val n = vm.emit(Label.Dict(Vector("c" -> Label.Str("a"))), Seq.empty)
    vm.begin()
    val e = intercept[NoSuchElementException](new RTQueueView(vm, Some(n), new Builder, "K.A"))
    assert(e.getMessage.contains("K.A.phase"), e.getMessage)
  }
}
