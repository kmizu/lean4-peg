package pal

/** Port of `test_gs_overlap.py`. */
class GsOverlapSuite extends munit.FunSuite {
  import GsOverlap.{decompose, iterBorders, iterPalindromicPrefixes}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  def words(alphabet: String, maximum: Int): Vector[String] = PyItertools.wordsBelow(alphabet, maximum + 1)

  def expectedBorders(word: String): Vector[Int] = {
    (word.length - 1 to 1 by -1).filter(size => word.take(size) == word.takeRight(size)).toVector
  }

  def isPalindrome(word: String): Boolean = word == word.reverse

  test("borders exhaustive") {
    words("ab", 12).foreach(word => assertEquals(iterBorders(word.toIndexedSeq), expectedBorders(word), word))
    words("abc", 7).foreach(word => assertEquals(iterBorders(word.toIndexedSeq), expectedBorders(word), word))
  }

  test("palindrome prefixes exhaustive") {
    words("ab", 11).foreach { word =>
      val expected = (word.length to 1 by -1).filter(size => isPalindrome(word.take(size))).toVector
      assertEquals(iterPalindromicPrefixes(word.toIndexedSeq), expected, word)
    }
  }

  test("nontrivial decompositions and shortened passes") {
    val samples = scala.collection.mutable.ArrayBuffer.empty[String]
    for (run <- 4 until 17; repeats <- Vector(4, 5, 8)) {
      samples += ("a" * run + "b") * repeats + "a" * run
    }
    var nested = "a"
    (0 until 6).foreach { level =>
      nested = nested * 4 + "bc"(level % 2)
      samples ++= Vector(nested, nested.dropRight(1), nested + nested.reverse)
    }
    var multipleStages = 0
    samples.foreach { word =>
      val meter = new Meter
      assertEquals(iterBorders(word.toIndexedSeq, meter = meter), expectedBorders(word), word.take(80))
      if (meter.stages > 1) {
        multipleStages += 1
      }
      // A growth regression, not a replacement for the complexity argument or
      // a bound on native instructions. These cases trigger the deletion loop.
      assert(meter.comparisons + meter.events < 100 * word.length)
    }
    assert(multipleStages > 20)
  }

  test("decomposition contract") {
    val samples = words("ab", 8) ++ (4 until 13).map(run => ("a" * run + "b") * 8)
    Vector(4, 5, 8).foreach { k =>
      samples.foreach { word =>
        val part = decompose(word.toIndexedSeq, k = k)
        if (word.isEmpty) {
          assertEquals(part.cut, 0)
        } else {
          assert((k - 1) * part.cut < word.length, (word, k, part))
          val suffix = word.drop(part.cut)
          val periods = (1 to suffix.length / k).filter { period =>
            suffix.take(k * period) == suffix.take(period) * k &&
              (1 until period).forall(divisor => period % divisor != 0 || suffix.take(period) != suffix.take(divisor) * (period / divisor))
          }
          assert(periods.size <= 1, (word, k, part))
          assertEquals(part.period, periods.headOption)
          part.period.foreach { period =>
            var reach = period
            while (reach < suffix.length && suffix(reach) == suffix(reach - period)) {
              reach += 1
            }
            assertEquals(part.reach, reach)
          }
          assertEquals(iterBorders(word.toIndexedSeq, k = k), expectedBorders(word), (word, k))
        }
      }
    }
  }

  test("long and random inputs") {
    val rng = new PyRandom(603)
    val samples = (0 until 120).map(_ => rng.word("abc", rng.randrange(1, 1025))) ++
      Vector("a" * 4096, "ab" * 2048, "aba" * 1365, "aaaab" * 819)
    samples.foreach(word => assertEquals(iterBorders(word.toIndexedSeq), expectedBorders(word), word.take(80)))
  }

  test("view and bounds") {
    Vector("", "a", "aba", "a#b").foreach { word =>
      val view = new PalindromeView(word.toIndexedSeq)
      val expected = word.map(Some(_)).toVector ++ Vector(view.separator) ++ word.reverse.map(Some(_)).toVector
      assertEquals((0 until view.length).map(view(_)).toVector, expected)
      intercept[IndexOutOfBoundsException](view(-1))
      intercept[IndexOutOfBoundsException](view(view.length))
    }
    // Python also rejects the non-int values True and 4.0, which the Scala
    // signature excludes statically.
    Vector(0, 3).foreach(k => intercept[IllegalArgumentException](iterBorders("aba".toIndexedSeq, k = k)))
    // Likewise for size=True.
    Vector(-1, 4).foreach(size => intercept[IllegalArgumentException](decompose("aba".toIndexedSeq, Some(size))))
  }
}
