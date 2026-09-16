package pal

import Scavm.{Self, Stats, VM}
import ScavmStructs.{Builder, emit}
import ScaffoldInput.InputHead

/** Port of `test_scaffold_input.py`: readonly input heads must clone and move
  * without pointer-identity tests. The random driver is also run in Python with the
  * same seeds and its per-step hop counts and VM statistics compared line by line.
  */
class ScaffoldInputSuite extends munit.FunSuite {

  private final case class Exercised(stats: Stats, hops: Vector[Int])

  /** Python `exercise(size, seed)`: three heads driven at random against an independent
    * position oracle. Include queue rotations, old-head clones and clones of newly
    * constructed cells before the new physical scaffold node is emitted.
    */
  private def exercise(size: Int, seed: Long): Exercised = {
    val random = new PyRandom(seed)
    val vm = new VM
    val text = new StringBuilder
    val positions = Array(0, 0, 0)
    val hops = Vector.newBuilder[Int]
    for (_ <- 0 until size) {
      vm.begin()
      val b = new Builder
      val c = random.choice("ab")
      text.append(c)
      b.label("input") = c
      val heads = (0 until 3).map(i => new InputHead(vm, vm.top, b, s"h$i")).toVector
      for (h <- heads) {
        h.append(Self)
      }
      for (_ <- 0 until 3) {
        val i = random.randrange(3)
        if (random.random() < 0.2) {
          val j = random.randrange(3)
          heads(i).copyFrom(heads(j))
          positions(i) = positions(j)
        } else if (random.random() < 0.55 && heads(i).canRight) {
          heads(i).right()
          positions(i) += 1
        } else if (positions(i) > 0) {
          heads(i).left()
          positions(i) -= 1
        }
        val expected = if (positions(i) == 0) { None } else { Some(text.charAt(positions(i) - 1).toString) }
        assertEquals(heads(i).read(), expected)
      }
      for ((h, i) <- heads.zipWithIndex) {
        assertEquals(h.canRight, positions(i) < text.length)
        h.finish()
      }
      hops += vm.hops
      emit(vm, b)
    }
    Exercised(vm.stats, hops.result())
  }

  test("cloning and motion against an independent position oracle") {
    for (seed <- 0 until 5) {
      exercise(200, seed.toLong)
    }
  }

  test("old heads and rotating queues remain bounded") {
    val stats = exercise(3000, 18L).stats
    assert(stats.radius <= 426, stats)
    assert(stats.fields <= 432, stats)
  }

  test("cloning cannot duplicate a partially broadcast arrival") {
    val vm = new VM
    vm.begin()
    val b = new Builder
    b.label("input") = "a"
    val a = new InputHead(vm, None, b, "a")
    val other = new InputHead(vm, None, b, "b")
    a.append(Self)
    val incompatible = intercept[IllegalArgumentException](other.copyFrom(a))
    assert(incompatible.getMessage.contains("arrival"), incompatible.getMessage)
    other.append(Self)
    other.copyFrom(a)
    val duplicate = intercept[IllegalArgumentException](other.append(Self))
    assert(duplicate.getMessage.contains("arrival"), duplicate.getMessage)
    other.right()
    assert(!other.canRight)
  }

  test("copies require the same scaffold step") {
    val vm = new VM
    vm.begin()
    val b = new Builder
    val a = new InputHead(vm, None, b, "a")
    val other = new InputHead(vm, None, new Builder, "b")
    val e = intercept[IllegalArgumentException](a.copyFrom(other))
    assert(e.getMessage.contains("step"), e.getMessage)
  }

  test("origin and live right boundary") {
    val vm = new VM
    vm.begin()
    val b = new Builder
    val h = new InputHead(vm, vm.top, b, "h")
    assertEquals(h.read(), None)
    assert(!h.canRight)
    intercept[IllegalArgumentException](h.left())
    intercept[IllegalArgumentException](h.right())
    b.label("input") = "a"
    h.append(Self)
    h.right()
    assertEquals(h.read(), Some("a"))
    assert(!h.canRight)
    h.left()
    assertEquals(h.read(), None)
    h.right()
    assertEquals(h.read(), Some("a"))
    h.finish()
    emit(vm, b)
  }

  test("the random driver's hop counts and statistics match python for every seed") {
    val out = new StringBuilder
    for (seed <- 0 until 5) {
      val e = exercise(200, seed.toLong)
      out.append(s"$seed ${e.stats.pythonRepr} ${e.hops.mkString(",")}\n")
    }
    val e = exercise(3000, 18L)
    out.append(s"18 ${e.stats.pythonRepr} ${e.hops.max}\n")
    PyDiff.assertSameAsPython(out.toString, "-c",
      """import random
        |from scavm import VM, SELF
        |from scavm_structs import Builder, emit
        |from scaffold_input import InputHead
        |def exercise(size, seed):
        |  random.seed(seed)
        |  vm, text, positions, hops = VM(), [], [0, 0, 0], []
        |  for step in range(size):
        |    vm.begin(); b = Builder(); c = random.choice("ab"); text.append(c); b.label["input"] = c
        |    heads = [InputHead(vm, vm.top, b, f"h{i}") for i in range(3)]
        |    for h in heads: h.append(SELF)
        |    for _ in range(3):
        |      i = random.randrange(3)
        |      if random.random() < .2:
        |        j = random.randrange(3); heads[i].copy_from(heads[j]); positions[i] = positions[j]
        |      elif random.random() < .55 and heads[i].can_right():
        |        heads[i].right(); positions[i] += 1
        |      elif positions[i] > 0:
        |        heads[i].left(); positions[i] -= 1
        |    for h in heads: h.finalize()
        |    hops.append(vm.hops); emit(vm, b)
        |  return vm.stats(), hops
        |for seed in range(5):
        |  stats, hops = exercise(200, seed); print(seed, stats, ",".join(map(str, hops)))
        |stats, hops = exercise(3000, 18); print(18, stats, max(hops))
        |""".stripMargin)
  }
}
