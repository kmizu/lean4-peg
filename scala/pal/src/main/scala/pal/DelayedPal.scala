package pal

import scala.collection.IndexedSeq
import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** A live view of a slice of the arrived characters; a growing window has no
  * fixed end, a reversed window reads its fixed slice backwards.
  */
final class Window(val data: mutable.ArrayBuffer[Char], val start: Int, val end: Option[Int] = None,
                   val backwards: Boolean = false) extends IndexedSeq[Char] {
  if (start < 0 || end.exists(stop => !(start <= stop && stop <= data.length))) {
    throw new IllegalArgumentException("window must contain only arrived characters")
  }
  if (backwards && end.isEmpty) {
    throw new IllegalArgumentException("a reversed window needs a fixed endpoint")
  }

  def length: Int = end.getOrElse(data.length) - start

  def apply(index: Int): Char = {
    if (!(0 <= index && index < length)) {
      throw new IndexOutOfBoundsException(index.toString)
    }
    if (backwards) data(end.get - 1 - index) else data(start + index)
  }
}

/** Two overlapping dyadic stages for a directly clocked PAL experiment.
  *
  * This accepts original words, but is still an indexed reference machine, not
  * an ordinary PEG. Rates below bound yielded indexed operations. Local-head
  * lowering and its own service bound must precede SCA/PEG compilation.
  *
  * Port of `delayed_pal.py`; the schedule is explained in `DELAYED_PAL.md`.
  */
object DelayedPal {
  import GsEvents.{IndexedJob, PatternMatcher, palindromeJob}

  val MATCH_RATE: Int = 80
  val JOB_RATE: Int = 1024

  /** One dyadic stage of width `K`: an outer GS matcher for the first `K`
    * characters reversed, and four sequential offline middle-flag jobs.
    */
  final class Stage(val data: mutable.ArrayBuffer[Char], val width: Int) {
    val matcher: PatternMatcher[Char] = new PatternMatcher(new Window(data, 0, Some(width), backwards = true), new Window(data, width))
    var job: Option[IndexedJob[Option[Char], Unit]] = None
    var jobIndex: Int = -1
    var jobFlags: mutable.ArrayBuffer[Boolean] = mutable.ArrayBuffer.empty
    val results: Array[Option[mutable.ArrayBuffer[Boolean]]] = Array.fill(4)(None)
    var jobSteps: Int = 0
    var matchSteps: Int = 0
    var jobsCompleted: Int = 0

    private def releaseJob(now: Int): Unit = {
      val half = width / 2
      if (now > width && (now - width) % half == 0) {
        val batch = (now - width) / half - 1
        if (batch < 4) {
          if (job.isDefined) {
            throw new AssertionError("offline palindrome job overran its release interval")
          }
          jobIndex = batch
          jobFlags = mutable.ArrayBuffer.empty
          val size = (batch + 1) * half
          job = Some(palindromeJob(new Window(data, width, Some(width + size)), batch * half, size))
        }
      }
    }

    private def serviceJob(): Unit = {
      job.foreach { active =>
        var budget = JOB_RATE
        while (budget > 0 && job.isDefined) {
          budget -= 1
          val event = active.step()
          jobSteps += 1
          event match {
            case Some(IndexedOp.Flag(value)) => jobFlags += value
            case _ => ()
          }
          if (active.done) {
            if (jobFlags.length != width / 2) {
              throw new AssertionError("incomplete palindrome flag block")
            }
            results(jobIndex) = Some(jobFlags)
            job = None
            jobFlags = mutable.ArrayBuffer.empty
            jobsCompleted += 1
          }
        }
      }
    }

    private def serviceMatcher(now: Int): Boolean = {
      var matched = false
      var budget = MATCH_RATE
      while (budget > 0 && !matcher.waiting) {
        budget -= 1
        val endpoint = matcher.step()
        matchSteps += 1
        endpoint.foreach { end =>
          if (end + width != now) {
            throw new AssertionError("positive pattern match missed its arrival deadline")
          }
          matched = true
        }
      }
      matched
    }

    /** Serve one arrival; the answer for the current prefix while this stage is
      * responsible for it (`2K <= now < 4K`).
      */
    def tick(now: Int): Option[Boolean] = {
      releaseJob(now)
      serviceJob()
      val matched = serviceMatcher(now)
      if (now < 2 * width) {
        None
      } else {
        val batch = (now - 2 * width) / (width / 2)
        val flags = results(batch).filter(_.nonEmpty).getOrElse {
          throw new AssertionError("middle palindrome flags missed their deadline")
        }
        val middle = flags.remove(flags.length - 1)
        Some(matched && middle)
      }
    }
  }

  /** Feed one binary character; report that exact prefix's PAL membership. */
  final class DelayedPal {
    val data: mutable.ArrayBuffer[Char] = mutable.ArrayBuffer.empty
    val stages: mutable.ArrayBuffer[Stage] = mutable.ArrayBuffer.empty
    var nextWidth: Int = 2
    var retiredJobSteps: Int = 0
    var retiredMatchSteps: Int = 0
    var retiredJobs: Int = 0

    private def retireStages(now: Int): Unit = {
      while (stages.nonEmpty && now == 4 * stages.head.width) {
        val retired = stages.remove(0)
        retiredJobSteps += retired.jobSteps
        retiredMatchSteps += retired.matchSteps
        retiredJobs += retired.jobsCompleted
      }
    }

    def feed(char: Char): Boolean = {
      if (char != 'a' && char != 'b') {
        throw new IllegalArgumentException("binary input required")
      }
      data += char
      val now = data.length
      retireStages(now)
      if (now == nextWidth) {
        stages += new Stage(data, nextWidth)
        nextWidth *= 2
      }
      var result: Option[Boolean] = if (now < 2) Some(true) else if (now < 4) Some(data(0) == char) else None
      stages.foreach { stage =>
        stage.tick(now).foreach { answer =>
          if (result.isDefined) {
            throw new AssertionError("overlapping active answer intervals")
          }
          result = Some(answer)
        }
      }
      if (stages.length > 2 || result.isEmpty) {
        throw new AssertionError("dyadic stage coverage failed")
      }
      result.get
    }

    /** Python's insertion-ordered dict of counters. */
    def statistics(): VectorMap[String, Int] = {
      VectorMap(
        "characters" -> data.length,
        "job_steps" -> (retiredJobSteps + stages.map(_.jobSteps).sum),
        "match_steps" -> (retiredMatchSteps + stages.map(_.matchSteps).sum),
        "completed_jobs" -> (retiredJobs + stages.map(_.jobsCompleted).sum),
        "live_stages" -> stages.length
      )
    }
  }

  def recognize(word: String): Boolean = {
    val machine = new DelayedPal
    var answer = true
    word.foreach(char => answer = machine.feed(char))
    answer
  }
}
