package pal

import scala.collection.IndexedSeq

import Action.Return

/** One resumable indexed operation (`gs_events.py` event tuple). */
sealed abstract class IndexedOp(val op: String)

object IndexedOp {

  /** A bookkeeping event. */
  case object Work extends IndexedOp("work")

  /** Compare two indexed cells; the driver answers with their equality. */
  final case class Compare(left: Int, right: Int) extends IndexedOp("compare")

  /** A found border length. */
  final case class Border(length: Int) extends IndexedOp("border")

  /** One palindrome-prefix flag bit. */
  final case class Flag(value: Boolean) extends IndexedOp("flag")
}

/** Resumable indexed GS operations, separate from the direct reference.
  *
  * One yielded operation is a comparison, bookkeeping event, or output bit.
  * Integer cursor arithmetic is still an indexed-machine operation. These are
  * not local SCA instructions; the distinction matters to every clock below.
  *
  * Port of `gs_events.py`. The generators use the [[Generator]] state-machine
  * encoding (see [[Coroutine]]); the `site` numbers follow the textual order of
  * the Python `yield`s. The indexed bounds are explained in `GS_OVERLAP.md`.
  */
object GsEvents {
  import GsOverlap.shiftWithoutPeriod
  import IndexedOp.*

  type IndexedGenerator[R] = Generator[IndexedOp, R]

  private def requireSizeAndK(size: Int, k: Int): Unit = {
    if (size < 0 || k < 4) {
      throw new IllegalArgumentException("nonnegative size and integer k >= 4 required")
    }
  }

  /** `_first(start, size, k, bound)`: the shortest basic prefix of
    * `word[start:start+size]` repeated k times, as `(period, k * period)`.
    */
  final class FirstPeriod(start: Int, size: Int, k: Int, bound: Option[Int] = None)
    extends IndexedGenerator[Option[(Int, Int)]]("_first") {
    private var p = 1
    private var q = 0

    private def outerHead(): Action[IndexedOp, Option[(Int, Int)]] = {
      if (p < size && bound.forall(p < _)) {
        emitAt(1, Work)
      } else {
        Return(None)
      }
    }

    private def innerHead(): Action[IndexedOp, Option[(Int, Int)]] = {
      if (p + q < size && q < (k - 1) * p) {
        emitAt(2, Compare(start + q, start + p + q))
      } else {
        afterInner()
      }
    }

    private def afterInner(): Action[IndexedOp, Option[(Int, Int)]] = {
      if (q == (k - 1) * p) {
        Return(Some((p, p + q)))
      } else {
        p += shiftWithoutPeriod(q, k)
        q = 0
        outerHead()
      }
    }

    protected def step(response: Option[Boolean]): Action[IndexedOp, Option[(Int, Int)]] = {
      site match {
        // start: gs_events.py:13 def _first
        case 0 => outerHead()
        // site 1 = gs_events.py:16 yield WORK
        case 1 => innerHead()
        // site 2 = gs_events.py:18 yield ("compare", start + q, start + p + q)
        case 2 =>
          if (response.get) {
            q += 1
            emitAt(3, Work)
          } else {
            afterInner()
          }
        // site 3 = gs_events.py:21 yield WORK
        case _ => innerHead()
      }
    }
  }

  /** `_second(start, size, k, first, reach)`: a second k-prefix-period beyond
    * the first period's reach.
    */
  final class SecondPeriod(start: Int, size: Int, k: Int, first: Int, reach: Int)
    extends IndexedGenerator[Option[Int]]("_second") {
    private var p = 1
    private var q = 0

    private def outerHead(): Action[IndexedOp, Option[Int]] = {
      if (p < size) {
        emitAt(1, Work)
      } else {
        Return(None)
      }
    }

    private def innerHead(): Action[IndexedOp, Option[Int]] = {
      if (p + q < size) {
        emitAt(2, Compare(start + q, start + p + q))
      } else {
        shift()
      }
    }

    private def shift(): Action[IndexedOp, Option[Int]] = {
      if (k * first <= q && q <= reach) {
        p += first
        q -= first
      } else {
        p += shiftWithoutPeriod(q, k)
        q = 0
      }
      outerHead()
    }

    protected def step(response: Option[Boolean]): Action[IndexedOp, Option[Int]] = {
      site match {
        // start: gs_events.py:29 def _second
        case 0 => outerHead()
        // site 1 = gs_events.py:32 yield WORK
        case 1 => innerHead()
        // site 2 = gs_events.py:34 yield ("compare", start + q, start + p + q)
        case 2 =>
          if (response.get) {
            q += 1
            emitAt(3, Work)
          } else {
            shift()
          }
        // site 3 = gs_events.py:37 yield WORK
        case _ =>
          if (p + q > reach && q >= (k - 1) * p) {
            Return(Some(p))
          } else {
            innerHead()
          }
      }
    }
  }

  /** `decomposition(size, k)`: the GS prefix decomposition of `word[:size]`. */
  final class DecompositionJob(size: Int, k: Int = 8) extends IndexedGenerator[Decomposition]("decomposition") {
    requireSizeAndK(size, k)

    private var start = 0
    private var first = 0
    private var reach = 0
    private var second = 0
    private var firstSearch: FirstPeriod = new FirstPeriod(0, 0, k)
    private var secondSearch: SecondPeriod = new SecondPeriod(0, 0, k, 0, 0)

    private def outer(): Action[IndexedOp, Decomposition] = {
      firstSearch = new FirstPeriod(start, size - start, k)
      callAt(1, firstSearch)
    }

    private def extendHead(): Action[IndexedOp, Decomposition] = {
      if (reach < size - start) {
        emitAt(2, Compare(start + reach, start + reach - first))
      } else {
        searchSecond()
      }
    }

    private def searchSecond(): Action[IndexedOp, Decomposition] = {
      secondSearch = new SecondPeriod(start, size - start, k, first, reach)
      callAt(4, secondSearch)
    }

    private def deleteHead(second: Int): Action[IndexedOp, Decomposition] = {
      firstSearch = new FirstPeriod(start, size - start, k, Some(second))
      callAt(5, firstSearch)
    }

    protected def step(response: Option[Boolean]): Action[IndexedOp, Decomposition] = {
      site match {
        // start: gs_events.py:49 def decomposition
        case 0 => outer()
        // site 1 = gs_events.py:54 yield from _first(start, size - start, k)
        case 1 =>
          firstSearch.result match {
            case None => Return(Decomposition(start, None, 0))
            case Some((period, found)) =>
              first = period
              reach = found
              extendHead()
          }
        // site 2 = gs_events.py:59 yield ("compare", start + reach, start + reach - first)
        case 2 =>
          if (response.get) {
            reach += 1
            emitAt(3, Work)
          } else {
            searchSecond()
          }
        // site 3 = gs_events.py:62 yield WORK
        case 3 => extendHead()
        // site 4 = gs_events.py:63 yield from _second(start, size - start, k, first, reach)
        case 4 =>
          secondSearch.result match {
            case None => Return(Decomposition(start, Some(first), reach))
            case Some(found) =>
              second = found
              deleteHead(second)
          }
        // site 5 = gs_events.py:67 yield from _first(start, size - start, k, second)
        case 5 =>
          firstSearch.result match {
            case None => outer()
            case Some((period, _)) =>
              start += period
              emitAt(6, Work)
          }
        // site 6 = gs_events.py:71 yield WORK
        case _ => deleteHead(second)
      }
    }
  }

  def decomposition(size: Int, k: Int = 8): DecompositionJob = new DecompositionJob(size, k)

  /** `borders(size, k)`: emit all nonempty proper border lengths of `word[:size]`
    * in decreasing order (`GS_OVERLAP.md`, stage by stage).
    */
  final class BordersJob(size: Int, k: Int = 8) extends IndexedGenerator[Unit]("borders") {
    requireSizeAndK(size, k)

    private var limit = size
    private var position = 1
    private var cut = 0
    private var period: Option[Int] = None
    private var reach = 0
    private var minimum = 0
    private var matched = 0
    private var checked = 0
    private var decomposition: DecompositionJob = new DecompositionJob(0, k)

    private def stageHead(): Action[IndexedOp, Unit] = {
      if (limit != 0) {
        decomposition = new DecompositionJob(limit, k)
        callAt(1, decomposition)
      } else {
        Return(())
      }
    }

    private def positionHead(): Action[IndexedOp, Unit] = {
      if (position <= limit - minimum) {
        emitAt(3, Work)
      } else {
        limit = minimum - 1
        position = 0
        stageHead()
      }
    }

    private def scanHead(): Action[IndexedOp, Unit] = {
      if (position + cut + matched < limit) {
        emitAt(4, Compare(cut + matched, size - limit + position + cut + matched))
      } else {
        afterScan()
      }
    }

    private def afterScan(): Action[IndexedOp, Unit] = {
      if (position + cut + matched == limit) {
        checked = 0
        checkHead()
      } else {
        shift()
      }
    }

    private def checkHead(): Action[IndexedOp, Unit] = {
      if (checked < cut) {
        emitAt(6, Compare(checked, size - limit + position + checked))
      } else {
        afterCheck()
      }
    }

    private def afterCheck(): Action[IndexedOp, Unit] = {
      if (checked == cut) {
        emitAt(8, Border(limit - position))
      } else {
        shift()
      }
    }

    private def shift(): Action[IndexedOp, Unit] = {
      if (period.exists(p => k * p <= matched && matched <= reach)) {
        position += period.get
        matched -= period.get
      } else {
        position += shiftWithoutPeriod(matched, k)
        matched = 0
      }
      positionHead()
    }

    protected def step(response: Option[Boolean]): Action[IndexedOp, Unit] = {
      site match {
        // start: gs_events.py:74 def borders
        case 0 => stageHead()
        // site 1 = gs_events.py:79 yield from decomposition(limit, k)
        case 1 =>
          val part = decomposition.result
          cut = part.cut
          period = part.period
          reach = part.reach
          emitAt(2, Work)
        // site 2 = gs_events.py:81 yield WORK
        case 2 =>
          minimum = math.max(1, 2 * cut)
          matched = 0
          positionHead()
        // site 3 = gs_events.py:84 yield WORK
        case 3 => scanHead()
        // site 4 = gs_events.py:86 yield ("compare", cut + matched, size - limit + position + cut + matched)
        case 4 =>
          if (response.get) {
            matched += 1
            emitAt(5, Work)
          } else {
            afterScan()
          }
        // site 5 = gs_events.py:89 yield WORK
        case 5 => scanHead()
        // site 6 = gs_events.py:93 yield ("compare", checked, size - limit + position + checked)
        case 6 =>
          if (response.get) {
            checked += 1
            emitAt(7, Work)
          } else {
            afterCheck()
          }
        // site 7 = gs_events.py:96 yield WORK
        case 7 => checkHead()
        // site 8 = gs_events.py:98 yield ("border", limit - position)
        case _ => shift()
      }
    }
  }

  def borders(size: Int, k: Int = 8): BordersJob = new BordersJob(size, k)

  /** Emit flags for lengths upper-1 .. lower, including epsilon when asked.
    *
    * Drives a `borders` job on the mirror view of length `2 * size + 1` and
    * forwards its operations, translating border lengths into descending flag
    * bits (Python's `palindrome_flags`).
    */
  final class PalindromeFlags(size: Int, lower: Int, upper: Int, k: Int = 8)
    extends IndexedGenerator[Unit]("palindrome_flags") {
    if (!(0 <= lower && lower <= upper && upper <= size + 1)) {
      throw new IllegalArgumentException("invalid palindrome flag interval")
    }

    private var remaining = upper - 1
    private val source = new BordersJob(2 * size + 1, k)
    private var sourceDone = false
    private var length = 0

    /** The main loop: pull the next source event. */
    private def pump(response: Option[Boolean]): Action[IndexedOp, Unit] = {
      var answer = response
      while (remaining >= math.max(lower, 1) && !sourceDone) {
        source.send(answer) match {
          case Returned(_) => sourceDone = true
          case Yielded(Border(found)) =>
            answer = None
            if (found <= remaining) {
              if (found < lower) {
                return finalLoop()
              }
              length = found
              return fillHead()
            }
          case Yielded(event) =>
            return emitAt(1, event)
        }
      }
      finalLoop()
    }

    private def fillHead(): Action[IndexedOp, Unit] = {
      if (remaining > length) {
        emitAt(2, Flag(false))
      } else {
        emitAt(3, Flag(true))
      }
    }

    private def finalLoop(): Action[IndexedOp, Unit] = {
      if (remaining >= lower) {
        emitAt(4, Flag(remaining == 0))
      } else {
        Return(())
      }
    }

    protected def step(response: Option[Boolean]): Action[IndexedOp, Unit] = {
      site match {
        // start: gs_events.py:108 def palindrome_flags
        case 0 => pump(None)
        // site 1 = gs_events.py:123 yield event
        case 1 => pump(response)
        // site 2 = gs_events.py:131 yield ("flag", False)
        case 2 =>
          remaining -= 1
          fillHead()
        // site 3 = gs_events.py:133 yield ("flag", True)
        case 3 =>
          remaining -= 1
          pump(None)
        // site 4 = gs_events.py:136 yield ("flag", remaining == 0)
        case _ =>
          remaining -= 1
          finalLoop()
      }
    }
  }

  def palindromeFlags(size: Int, lower: Int, upper: Int, k: Int = 8): PalindromeFlags = {
    new PalindromeFlags(size, lower, upper, k)
  }

  /** Service one yielded indexed operation per step, retaining no trace. */
  final class IndexedJob[S, R](val word: IndexedSeq[S], val program: IndexedGenerator[R]) {
    private var response: Option[Boolean] = None
    var done: Boolean = false
    private var outcome: Option[R] = None
    var steps: Int = 0

    /** The generator's return value once `done`. */
    def result: R = outcome.getOrElse(throw new IllegalStateException("job not completed"))

    /** Perform one operation; `None` when the job just completed. */
    def step(): Option[IndexedOp] = {
      if (done) {
        throw new IllegalStateException("job already completed")
      }
      steps += 1
      program.send(response) match {
        case Returned(value) =>
          done = true
          outcome = Some(value)
          None
        case Yielded(event) =>
          response = event match {
            case Compare(left, right) => Some(word(left) == word(right))
            case _ => None
          }
          Some(event)
      }
    }
  }

  /** Incremental GS fixed-pattern matcher with interleaved prefix checking.
    *
    * Text is a growing indexed view. step() returns a positive match's text-end
    * index, or None. waiting means the next comparison needs another character.
    * This class never performs a whole-pattern comparison as a hidden step.
    */
  final class PatternMatcher[S](val pattern: IndexedSeq[S], val text: IndexedSeq[S], val k: Int = 8) {
    if (pattern.isEmpty || k < 4) {
      throw new IllegalArgumentException("a nonempty pattern and k >= 4 are required")
    }

    val preparation: IndexedJob[S, Decomposition] = new IndexedJob(pattern, new DecompositionJob(pattern.length, k))
    var part: Option[Decomposition] = None
    var position: Int = 0
    var matched: Int = 0
    var checked: Int = 0
    var prefixOk: Boolean = true
    var quota: Int = 0
    var mode: String = "compare"
    var steps: Int = 0

    def waiting: Boolean = {
      part.exists(found => mode == "compare" && position + found.cut + matched >= text.length)
    }

    private def afterPrefixWork(): Option[Int] = {
      mode = "compare"
      if (matched != pattern.length - part.get.cut) {
        None
      } else {
        if (prefixOk && checked != part.get.cut) {
          throw new AssertionError("prefix verifier missed the full-match deadline")
        }
        mode = "shift"
        if (prefixOk) Some(position + pattern.length) else None
      }
    }

    private def shiftStep(found: Decomposition): Unit = {
      if (found.period.exists(period => k * period <= matched && matched <= found.reach)) {
        position += found.period.get
        matched -= found.period.get
      } else {
        position += shiftWithoutPeriod(matched, k)
        matched = 0
      }
      checked = 0
      prefixOk = true
      mode = "compare"
    }

    private def prefixStep(cut: Int): Option[Int] = {
      if (pattern(checked) != text(position + checked)) {
        prefixOk = false
      }
      checked += 1
      quota -= 1
      if (!prefixOk || checked == cut || quota == 0) afterPrefixWork() else None
    }

    def step(): Option[Int] = {
      if (waiting) {
        return None
      }
      steps += 1
      part match {
        case None =>
          preparation.step()
          if (preparation.done) {
            part = Some(preparation.result)
          }
          None
        case Some(found) =>
          if (mode == "shift") {
            shiftStep(found)
            None
          } else if (mode == "prefix") {
            prefixStep(found.cut)
          } else if (pattern(found.cut + matched) != text(position + found.cut + matched)) {
            mode = "shift"
            None
          } else {
            matched += 1
            if (prefixOk && checked < found.cut) {
              mode = "prefix"
              quota = 2
              None
            } else {
              afterPrefixWork()
            }
          }
      }
    }
  }

  def palindromeJob[S](word: IndexedSeq[S], lower: Int, upper: Int, k: Int = 8): IndexedJob[Option[S], Unit] = {
    new IndexedJob(new PalindromeView(word), new PalindromeFlags(word.length, lower, upper, k))
  }
}
