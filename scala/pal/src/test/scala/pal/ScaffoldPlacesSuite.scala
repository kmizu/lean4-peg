package pal

import Scavm.{Self, VM}
import ScavmStructs.{Builder, emit}
import ScaffoldPlaces.PlaceHead

/** Port of `test_scaffold_places.py`: Galil's interleaved places are a view of
  * unchanged binary input. The driver is also run in Python with the same seed and
  * its per-tick reads, flags, hop counts and final statistics compared line by line.
  */
class ScaffoldPlacesSuite extends munit.FunSuite {

  private def flag(b: Boolean): Int = if (b) { 1 } else { 0 }

  /** The Python test body (`random.Random(935)`, 2000 ticks); returns the trace. */
  private def drive(): String = {
    val rng = new PyRandom(935L)
    val vm = new VM
    val word = new StringBuilder
    val positions = Array(0, 0, 0)
    val out = new StringBuilder
    for (tick <- 0 until 2000) {
      vm.begin()
      val b = new Builder
      val heads = Vector("c", "l", "r").map(name => new PlaceHead(vm, vm.top, b, name))
      if (tick % 3 == 0) {
        val symbol = rng.choice("ab")
        word.append(symbol)
        b.label("input") = symbol
        for (head <- heads) {
          head.append(Self)
        }
      } else {
        b.label("input") = "a"
      }
      val i = rng.randrange(3)
      val j = rng.randrange(3)
      if (tick % 7 == 0) {
        heads(i).copyFrom(heads(j))
        positions(i) = positions(j)
      } else if (rng.randrange(2) != 0 && positions(i) < 2 * word.length) {
        heads(i).right()
        positions(i) += 1
      } else if (positions(i) != 0) {
        heads(i).left()
        positions(i) -= 1
      }
      val line = heads.zip(positions).map { case (head, position) =>
        val expected = if (position == 0) { None } else if (position % 2 == 0) { Some("s") } else { Some(word.charAt(position / 2).toString) }
        // each observation once: `isFirst` peeks the left stack, which is one hop
        val read = head.read()
        val canRight = head.canRight
        val isFirst = head.isFirst
        assertEquals(read, expected)
        assertEquals(canRight, position < 2 * word.length)
        assertEquals(isFirst, position == 1)
        head.finish()
        s"${read.getOrElse("None")}/${flag(canRight)}/${flag(isFirst)}"
      }
      out.append(s"$tick $i $j ${vm.hops} ${line.mkString(" ")}\n")
      emit(vm, b)
    }
    out.append(vm.stats.pythonRepr).append("\n")
    out.toString
  }

  test("moves and copies across virtual spaces and live input") {
    drive()
  }

  test("the driver's reads, flags, hops and statistics match python tick by tick") {
    PyDiff.assertSameAsPython(drive(), "-c",
      """import random
        |from scavm import VM, SELF
        |from scavm_structs import Builder, emit
        |from scaffold_places import PlaceHead
        |rng = random.Random(935)
        |vm, word, positions = VM(), "", [0, 0, 0]
        |for tick in range(2000):
        |  vm.begin(); b = Builder()
        |  heads = [PlaceHead(vm, vm.top, b, name) for name in ("c", "l", "r")]
        |  if tick % 3 == 0:
        |    symbol = rng.choice("ab"); word += symbol; b.label["input"] = symbol
        |    for head in heads: head.append(SELF)
        |  else:
        |    b.label["input"] = "a"
        |  i, j = rng.randrange(3), rng.randrange(3)
        |  if tick % 7 == 0:
        |    heads[i].copy_from(heads[j]); positions[i] = positions[j]
        |  elif rng.randrange(2) and positions[i] < 2 * len(word):
        |    heads[i].right(); positions[i] += 1
        |  elif positions[i]:
        |    heads[i].left(); positions[i] -= 1
        |  line = []
        |  for head in heads:
        |    line.append(f"{head.read()}/{int(head.can_right())}/{int(head.is_first())}"); head.finalize()
        |  print(tick, i, j, vm.hops, *line)
        |  emit(vm, b)
        |print(vm.stats())
        |""".stripMargin)
  }
}
