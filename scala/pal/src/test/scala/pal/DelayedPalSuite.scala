package pal

import scala.collection.mutable

/** Port of `test_delayed_pal.py`. */
class DelayedPalSuite extends munit.FunSuite {
  import DelayedPal.{DelayedPal, recognize}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  def isPalindrome(word: String): Boolean = word == word.reverse

  def checkPrefixes(word: String): DelayedPal = {
    val machine = new DelayedPal
    word.zipWithIndex.foreach { case (char, index) =>
      val size = index + 1
      assertEquals(machine.feed(char), isPalindrome(word.take(size)), (word.take(80), size))
      assert(machine.stages.length <= 2)
    }
    machine
  }

  test("all binary prefixes") {
    assert(recognize(""))
    (0 until 13).foreach(size => PyItertools.words("ab", size).foreach(checkPrefixes))
  }

  test("stage boundaries and periodic patterns") {
    Vector(16, 32, 64, 128, 256, 512).foreach { width =>
      val left = ("a" * 16 + "b") * (width / 17) + "a" * (width % 17)
      checkPrefixes(left + left.reverse)
      checkPrefixes(left + "a" + left.reverse)
      checkPrefixes(left + "b" + left.reverse)
    }
    Vector("a" * 2048, "ab" * 1024, ("a" * 64 + "b") * 64).foreach { word =>
      val machine = checkPrefixes(word)
      val statistics = machine.statistics()
      assert(statistics("completed_jobs") > 20)
      // Python's dict order.
      assertEquals(statistics.keys.toVector, Vector("characters", "job_steps", "match_steps", "completed_jobs", "live_stages"))
      assertEquals(statistics("characters"), word.length)
    }
  }

  test("long random palindromes and perturbations") {
    val rng = new PyRandom(810)
    (0 until 100).foreach { _ =>
      val left = rng.word("ab", rng.randrange(1, 300))
      val middle = Vector("", "a", "b")(rng.randbelow(3))
      val palindrome = left + middle + left.reverse
      checkPrefixes(palindrome)
      val place = rng.randbelow(left.length)
      val changed = palindrome.take(place) + (if (palindrome(place) == 'a') "b" else "a") + palindrome.drop(place + 1)
      assert(!recognize(changed))
    }
  }

  test("windows cannot read future input") {
    val data = mutable.ArrayBuffer.from("abba")
    val fixed = new Window(data, 1, Some(3))
    val growing = new Window(data, 1)
    val reverse = new Window(data, 0, Some(4), backwards = true)
    data ++= "ab"
    assertEquals(fixed.length, 2)
    assertEquals(growing.length, 5)
    assertEquals((0 until reverse.length).map(reverse(_)).mkString, "abba")
    intercept[IndexOutOfBoundsException](fixed(2))
    intercept[IllegalArgumentException](new Window(data, 0, Some(7)))
    intercept[IllegalArgumentException](new DelayedPal().feed('#'))
  }
}
