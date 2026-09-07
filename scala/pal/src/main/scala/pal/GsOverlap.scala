package pal

import scala.collection.IndexedSeq

import scala.collection.mutable

/** Comparison/loop-event counters of the reference algorithm, not machine
  * instructions or input time.
  */
final class Meter {
  var comparisons: Int = 0
  var events: Int = 0
  var stages: Int = 0
  var nonzeroCuts: Int = 0

  def same[S](word: IndexedSeq[S], left: Int, right: Int): Boolean = {
    comparisons += 1
    word(left) == word(right)
  }
}

/** `word[:size] = u v` with `cut = |u|`, the unique basic k-prefix-period of
  * `v` (if any) and its reach within `v`.
  */
final case class Decomposition(cut: Int, period: Option[Int], reach: Int)

/** An indexed view of `u # reverse(u)`, with a fresh internal separator.
  *
  * This avoids allocating that string in the reference algorithm. It is not
  * an input transformation performed by an emitted PEG; there is no such PEG
  * yet. A local-head realization must implement this view too.
  *
  * Symbols are `Some(char)`; the separator is `None`, which equals no symbol
  * of the word (Python uses a fresh `object()`).
  */
final class PalindromeView[S](val word: IndexedSeq[S]) extends IndexedSeq[Option[S]] {
  val middle: Int = word.length

  /** The fresh separator. */
  val separator: Option[S] = None

  def length: Int = 2 * middle + 1

  def apply(index: Int): Option[S] = {
    if (index < 0 || index >= length) {
      throw new IndexOutOfBoundsException(index.toString)
    }
    if (index < middle) {
      Some(word(index))
    } else if (index == middle) {
      separator
    } else {
      Some(word(2 * middle - index))
    }
  }
}

/** Table-free Galil--Seiferas prefix decomposition and right overlaps.
  *
  * This is an indexed reference algorithm, not an SCA or a PAL PEG. Its fixed
  * set of integer cursors and random-access reads still need local-head lowering.
  * Meter counts comparisons/loop events, not machine instructions or input time.
  *
  * The matching shifts come from Galil--Seiferas (1983), pp. 282--287. The
  * shortening overlap pass here is explained separately in `GS_OVERLAP.md`.
  *
  * Port of `gs_overlap.py`.
  */
object GsOverlap {

  def shiftWithoutPeriod(matched: Int, k: Int): Int = math.max(1, (matched + k - 1) / k)

  private def requireK(k: Int, what: String): Unit = {
    if (k < 4) {
      throw new IllegalArgumentException(s"the $what requires an integer k >= 4")
    }
  }

  /** Shortest basic prefix repeated k times; stop at its first k copies.
    *
    * A bound restricts the candidate period length, not the compared input.
    * In particular, deletion passes must not extend a found period to its full
    * reach: doing that repeatedly on a long run would cost quadratic time.
    *
    * @return `(period, k * period)` when found
    */
  private def firstPeriod[S](word: IndexedSeq[S], start: Int, size: Int, k: Int, meter: Meter,
                             bound: Option[Int] = None): Option[(Int, Int)] = {
    var p = 1
    var q = 0
    while (p < size && bound.forall(p < _)) {
      meter.events += 1
      while (p + q < size && q < (k - 1) * p && meter.same(word, start + q, start + p + q)) {
        q += 1
        meter.events += 1
      }
      if (q == (k - 1) * p) {
        return Some((p, p + q))
      }
      p += shiftWithoutPeriod(q, k)
      q = 0
    }
    None
  }

  private def secondPeriod[S](word: IndexedSeq[S], start: Int, size: Int, k: Int, first: Int, reach: Int,
                              meter: Meter): Option[Int] = {
    var p = 1
    var q = 0
    while (p < size) {
      meter.events += 1
      while (p + q < size && meter.same(word, start + q, start + p + q)) {
        q += 1
        meter.events += 1
        if (p + q > reach && q >= (k - 1) * p) {
          return Some(p)
        }
      }
      if (k * first <= q && q <= reach) {
        p += first
        q -= first
      } else {
        p += shiftWithoutPeriod(q, k)
        q = 0
      }
    }
    None
  }

  /** Find `word[:size] = u v` with at most one basic k-prefix-period in v.
    *
    * The result's reach is measured within v. For a nonempty pattern,
    * `(k-1)*len(u) < size`. No substring copies participate in this procedure.
    */
  def decompose[S](word: IndexedSeq[S], size: Option[Int] = None, k: Int = 4,
                   meter: Meter = new Meter): Decomposition = {
    requireK(k, "decomposition")
    val patternSize = size.getOrElse(word.length)
    if (patternSize < 0 || patternSize > word.length) {
      throw new IllegalArgumentException("pattern size must be a prefix length")
    }
    var start = 0
    while (true) {
      firstPeriod(word, start, patternSize - start, k, meter) match {
        case None => return Decomposition(start, None, 0)
        case Some((first, found)) =>
          var reach = found
          while (reach < patternSize - start && meter.same(word, start + reach, start + reach - first)) {
            reach += 1
            meter.events += 1
          }
          secondPeriod(word, start, patternSize - start, k, first, reach, meter) match {
            case None => return Decomposition(start, Some(first), reach)
            case Some(second) =>
              var deleting = true
              while (deleting) {
                firstPeriod(word, start, patternSize - start, k, meter, bound = Some(second)) match {
                  case None => deleting = false
                  case Some((period, _)) =>
                    start += period
                    meter.events += 1
                }
              }
          }
      }
    }
    throw new IllegalStateException("unreachable")
  }

  /** Visit all nonempty proper border lengths, strictly decreasing.
    *
    * The input is read through len/indexing only; no failure table, substring,
    * recursive call stack, or result array is constructed. Output storage is the
    * caller's choice (`emit`). The indexed operations are not yet local SCA
    * operations.
    */
  def eachBorder[S](word: IndexedSeq[S], k: Int = 4, meter: Meter = new Meter)(emit: Int => Unit): Unit = {
    requireK(k, "overlap pass")
    val size = word.length
    var limit = size
    var position = 1 // Exclude the whole input in the first stage.
    while (limit != 0) {
      val part = decompose(word, Some(limit), k = k, meter = meter)
      val cut = part.cut
      meter.stages += 1
      if (cut != 0) {
        meter.nonzeroCuts += 1
      }
      val minimum = math.max(1, 2 * cut)
      var matched = 0
      while (position <= limit - minimum) {
        meter.events += 1
        while (position + cut + matched < limit &&
          meter.same(word, cut + matched, size - limit + position + cut + matched)) {
          matched += 1
          meter.events += 1
        }
        if (position + cut + matched == limit) {
          var checked = 0
          while (checked < cut && meter.same(word, checked, size - limit + position + checked)) {
            checked += 1
            meter.events += 1
          }
          if (checked == cut) {
            emit(limit - position)
          }
        }
        if (part.period.exists(period => k * period <= matched && matched <= part.reach)) {
          position += part.period.get
          matched -= part.period.get
        } else {
          position += shiftWithoutPeriod(matched, k)
          matched = 0
        }
      }
      limit = minimum - 1
      position = 0 // This smaller length has not yet been considered.
    }
  }

  /** `iter_borders`, collected: all nonempty proper border lengths, decreasing. */
  def iterBorders[S](word: IndexedSeq[S], k: Int = 4, meter: Meter = new Meter): Vector[Int] = {
    val borders = mutable.ArrayBuffer.empty[Int]
    eachBorder(word, k, meter)(borders += _)
    borders.toVector
  }

  /** Nonempty palindrome-prefix lengths in decreasing order, offline. */
  def iterPalindromicPrefixes[S](word: IndexedSeq[S], k: Int = 4, meter: Meter = new Meter): Vector[Int] = {
    iterBorders(new PalindromeView(word), k = k, meter = meter)
  }
}
