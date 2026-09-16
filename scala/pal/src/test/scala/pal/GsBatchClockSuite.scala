package pal

/** Port of `test_gs_batch_clock.py`, plus a check of the derived batch rates. */
class GsBatchClockSuite extends munit.FunSuite {
  import GsBatchClock.{DEFAULT_BATCH, deriveBatch}
  import GsDualFlags.compileDualFlags

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  def isPalindrome(word: String): Boolean = word == word.reverse

  test("all four job intervals") {
    val p = compileDualFlags(unit = false)
    val rng = new PyRandom(1406)
    val words = PyItertools.wordsBelow("ab", 10) ++
      (for (n <- Vector(32, 64, 128, 256, 512); _ <- 0 until 8) yield rng.word("ab", n)) ++
      Vector("a" * 2048, "ab" * 2048, ("a" * 8 + "b") * 80 + "b")
    words.foreach { word =>
      (1 to 4).foreach { job =>
        val half = math.max(1, word.length / job)
        val prefix = word.take(job * half)
        if (prefix.length == job * half) {
          val lower = (job - 1) * half
          val vm = new DualFlagVM(prefix, lower, prefix.length, Some(p))
          val expected = (prefix.length - 1 to lower by -1).map(n => isPalindrome(prefix.take(n))).toVector
          assertEquals(vm.runFlags(), expected, (word.take(30), word.length, job))
          assert(vm.steps + 1 <= DEFAULT_BATCH.flags * half)
        }
      }
    }
  }

  test("derived batch rates agree with gs_batch_clock.py") {
    def show(rates: BatchRates): String = {
      s"${rates.k} ${rates.decomposition} ${rates.singleStage} ${rates.firstJob} ${rates.matching} ${rates.flags}"
    }
    val actual = (Vector(6, 7, 8, 12).map(k => show(deriveBatch(k))) :+ show(DEFAULT_BATCH)).mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c",
      "from gs_batch_clock import derive_batch, DEFAULT_BATCH\n" +
        "def show(r): return f'{r.k} {r.decomposition} {r.single_stage} {r.first_job} {r.matching} {r.flags}'\n" +
        "for k in (6, 7, 8, 12): print(show(derive_batch(k)))\nprint(show(DEFAULT_BATCH))")
    intercept[IllegalArgumentException](deriveBatch(5))
    intercept[IllegalArgumentException](deriveBatch(3))
  }
}
