package pal

import scala.collection.mutable

/** Port of `test_gs_events.py`. */
class GsEventsSuite extends munit.FunSuite {
  import GsEvents.{IndexedJob, PatternMatcher, borders, decomposition, palindromeJob}
  import GsOverlap.{decompose, iterBorders}

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  /** Run a job to completion, collecting the border lengths it emits. */
  def executeBorders[S](job: IndexedJob[S, ?]): Vector[Int] = {
    val outputs = mutable.ArrayBuffer.empty[Int]
    while (!job.done) {
      job.step() match {
        case Some(IndexedOp.Border(length)) => outputs += length
        case _ => ()
      }
    }
    outputs.toVector
  }

  /** Run a job to completion, collecting the flag bits it emits. */
  def executeFlags[S](job: IndexedJob[S, ?]): Vector[Boolean] = {
    val outputs = mutable.ArrayBuffer.empty[Boolean]
    while (!job.done) {
      job.step() match {
        case Some(IndexedOp.Flag(value)) => outputs += value
        case _ => ()
      }
    }
    outputs.toVector
  }

  def isPalindrome(word: String): Boolean = word == word.reverse

  test("resumable operations match direct algorithm") {
    PyItertools.wordsBelow("ab", 11).foreach { word =>
      val size = word.length
      val job = new IndexedJob(word.toIndexedSeq, decomposition(size))
      executeBorders(job)
      assertEquals(job.result, decompose(word.toIndexedSeq, k = 8), word)
      assert(job.steps <= 42 * size + 1)
      val borderJob = new IndexedJob(word.toIndexedSeq, borders(size))
      assertEquals(executeBorders(borderJob), iterBorders(word.toIndexedSeq, k = 8), word)
      assert(borderJob.steps <= 107 * size + 1)
    }
  }

  test("flag intervals include epsilon and full word") {
    Vector("", "a", "aba", "abba", "abab", "aaaaba", "ab" * 17).foreach { word =>
      for (lower <- 0 to word.length; upper <- lower to word.length + 1) {
        val job = palindromeJob(word.toIndexedSeq, lower, upper)
        val expected = (upper - 1 to lower by -1).map(size => isPalindrome(word.take(size))).toVector
        assertEquals(executeFlags(job), expected, (word, lower, upper))
        assert(job.steps <= 215 * word.length + 109)
      }
    }
  }

  test("pattern matches meet indexed clock") {
    val rng = new PyRandom(804)
    val patterns = mutable.ArrayBuffer("a", "ab", "aba", "a" * 31, ("a" * 16 + "b") * 16 + "a" * 16)
    patterns ++= (0 until 50).map(_ => rng.word("ab", rng.randrange(1, 100)))
    patterns.foreach { pattern =>
      val text = mutable.ArrayBuffer.empty[Char]
      val matcher = new PatternMatcher(pattern.toIndexedSeq, text)
      val stream = pattern * 3 + "aba" + pattern + pattern.dropRight(1) + "b" + pattern * 2
      stream.zipWithIndex.foreach { case (char, i) =>
        val index = i + 1
        text += char
        var reported = false
        var budget = 80
        while (budget > 0 && !matcher.waiting) {
          budget -= 1
          matcher.step().foreach { endpoint =>
            assertEquals(endpoint, index, (pattern, index, endpoint))
            reported = true
          }
        }
        assertEquals(reported, stream.take(index).endsWith(pattern), (pattern, index))
      }
    }
  }

  test("periodic deletion event bounds") {
    val samples = mutable.ArrayBuffer.from(Vector(8, 16, 32, 64).map(run => ("a" * run + "b") * 32 + "a" * run))
    var nested = "a"
    (0 until 4).foreach { i =>
      nested = nested * 8 + "bc"(i % 2)
      samples ++= Vector(nested, nested + nested.reverse)
    }
    samples.foreach { word =>
      val job = new IndexedJob(word.toIndexedSeq, decomposition(word.length))
      executeBorders(job)
      assertEquals(job.result, decompose(word.toIndexedSeq, k = 8))
      assert(job.steps <= 42 * word.length + 1)
      val borderJob = new IndexedJob(word.toIndexedSeq, borders(word.length))
      assertEquals(executeBorders(borderJob), iterBorders(word.toIndexedSeq, k = 8))
      assert(borderJob.steps <= 107 * word.length + 1)
    }
  }
}
