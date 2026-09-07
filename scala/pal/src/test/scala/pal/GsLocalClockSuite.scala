package pal

/** Port of `test_gs_local_clock.py`, plus a check of the derived rates
  * against the Python module.
  */
class GsLocalClockSuite extends munit.FunSuite {
  import GsLocalClock.{DEFAULT, DEFAULT_DUAL, derive, deriveDual}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  test("flag jobs fit the symbolic head bound") {
    val program = GsFlagHeads.compileFlags()
    val rng = new PyRandom(915)
    val words = scala.collection.mutable.ArrayBuffer.from(PyItertools.wordsBelow("ab", 9))
    words ++= (0 until 30).map(_ => rng.word("ab", 512))
    var word = "ab"
    (0 until 4).foreach { _ =>
      word = (word + "a") * 8 + "b"
      words += word
    }
    words.foreach { word =>
      val job = new FlagVM(word, 0, word.length, Some(program))
      job.run()
      assert(job.steps <= DEFAULT.flagView * (2 * word.length + 1) + 1, (word.length, word.take(40), job.steps))
    }
  }

  test("matching deadlines include preprocessing") {
    val program = GsMatchHeads.compileMatcher()
    val budget = DEFAULT.matching / 4
    val rng = new PyRandom(916)
    val patterns = scala.collection.mutable.ArrayBuffer.from((1 until 7).flatMap(PyItertools.words("ab", _)))
    patterns ++= Vector("a" * 257, "ab" * 129, ("a" * 8 + "b") * 8 + "b")
    patterns ++= (0 until 15).map(_ => rng.word("ab", 257))
    patterns.foreach { pattern =>
      val text = pattern * 3 + rng.word("ab", 50) + pattern
      val vm = new StreamingMatcher(pattern, Some(program))
      // Deliberately do not drain pattern preprocessing before the first
      // arrival. It must share the fixed per-arrival service budget.
      text.zipWithIndex.foreach { case (char, index) =>
        val end = index + 1
        val before = vm.outputs.size
        vm.append(char)
        var remaining = budget
        while (remaining > 0 && !vm.waiting) {
          vm.step()
          remaining -= 1
        }
        val expected = end >= pattern.length && text.substring(end - pattern.length, end) == pattern
        assertEquals(vm.outputs.drop(before), if (expected) Vector(end) else Vector.empty[Int],
          (pattern.length, pattern.take(30), end))
      }
    }
  }

  test("derived rates agree with gs_local_clock.py") {
    def show(rates: Rates): String = {
      s"${rates.k} ${rates.decomposition} ${rates.flagView} ${rates.matching} ${rates.flags} ${rates.overhead} ${rates.round}"
    }
    val actual = (Vector(4, 5, 6, 8, 12).map(k => show(derive(k)) + " | " + show(deriveDual(k))) ++
      Vector(show(DEFAULT) + " | " + show(DEFAULT_DUAL))).mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_local_clock import derive, derive_dual, DEFAULT, DEFAULT_DUAL\n" +
        "def show(r): return f'{r.k} {r.decomposition} {r.flag_view} {r.matching} {r.flags} {r.overhead} {r.round}'\n" +
        "for k in (4, 5, 6, 8, 12): print(show(derive(k)), '|', show(derive_dual(k)))\n" +
        "print(show(DEFAULT), '|', show(DEFAULT_DUAL))")
    intercept[IllegalArgumentException](derive(3))
  }
}
