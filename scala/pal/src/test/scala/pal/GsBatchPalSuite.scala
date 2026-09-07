package pal

import scala.collection.mutable

/** Independent integer-coordinate observer of the fixed batch PAL schedule.
  *
  * Port of `test_gs_batch_pal.py`.
  */
class GsBatchPalSuite extends munit.FunSuite {
  import GsBatchClock.DEFAULT_BATCH

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  final class ObserverStage(word: String, matching: Program, flagging: Program) {
    val width: Int = word.length
    val matcher: StreamingMatcher = new StreamingMatcher(word.reverse, Some(matching))
    var job: Option[DualFlagVM] = None
    var batch: Int = -1
    val results: Array[Option[mutable.ArrayBuffer[Boolean]]] = Array.fill(4)(None)

    def feed(word: String): Option[Boolean] = {
      val half = width / 2
      val now = word.length
      if (now > width) {
        matcher.append(word.last)
      }
      if (now > width && (now - width) % half == 0) {
        val released = (now - width) / half - 1
        if (released < 4) {
          assert(job.isEmpty)
          batch = released
          job = Some(new DualFlagVM(word.drop(width), released * half, now - width, Some(flagging)))
        }
      }
      // Existing result consumption precedes this round's service, as it does
      // in the emitted source, so a release-boundary overrun cannot be hidden.
      var middle: Option[Boolean] = None
      if (now >= 2 * width) {
        val result = results((now - 2 * width) / half)
        assert(result.exists(_.nonEmpty))
        middle = Some(result.get.remove(result.get.length - 1))
      }
      job.foreach { active =>
        var budget = DEFAULT_BATCH.flags
        while (budget > 0 && job.isDefined) {
          budget -= 1
          if (active.done) {
            results(batch) = Some(mutable.ArrayBuffer.from(active.flags))
            assertEquals(active.flags.length, half)
            job = None
          } else {
            active.step()
          }
        }
      }
      var matched = false
      (0 until DEFAULT_BATCH.matching).foreach { _ =>
        matcher.step().foreach { output =>
          assertEquals(output + width, now)
          matched = true
        }
      }
      middle.map(_ && matched)
    }
  }

  def recognizeAll(word: String, matching: Program, flagging: Program): Boolean = {
    var stages = Vector.empty[ObserverStage]
    var data = ""
    var answer = true
    word.foreach { char =>
      data += char
      val now = data.length
      stages = stages.filter(stage => now < 4 * stage.width)
      if (now >= 2 && (now & (now - 1)) == 0) {
        stages :+= new ObserverStage(data, matching, flagging)
      }
      var current: Option[Boolean] = if (now == 1) Some(true) else if (now < 4) Some(data.head == data.last) else None
      stages.foreach { stage =>
        stage.feed(data).foreach { result =>
          assert(current.isEmpty)
          current = Some(result)
        }
      }
      assert(current.isDefined)
      assertEquals(current.get, data == data.reverse, data)
      answer = current.get
    }
    answer
  }

  test("prefix answers and release deadlines") {
    val matching = GsMatchHeads.compileMatcher(unit = false)
    val flagging = GsDualFlags.compileDualFlags(unit = false)
    val rng = new PyRandom(1407)
    val words = PyItertools.wordsBelow("ab", 9) ++
      (for (n <- Vector(32, 64, 128, 256, 512); _ <- 0 until 3) yield rng.word("ab", n)) ++
      Vector("a" * 512, "ab" * 512, ("a" * 8 + "b") * 64 + "b")
    words.foreach(word => assertEquals(recognizeAll(word, matching, flagging), word == word.reverse, word.take(30)))
  }
}
