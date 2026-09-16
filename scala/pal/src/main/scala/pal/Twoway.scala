package pal

import scala.collection.mutable

/** Two-way string matching (Crochemore & Perrin 1991) and what it buys for FPP.
  * （Python 版: `docs/palindromes-in-peg/twoway.py`）
  *
  * Why this file exists.  The blocker at the top of PROGRESS.md is "the longest border
  * of a non-periodic palindrome W in O(|W|) machine steps with heads only".  The KMP
  * route needs random access to fail[]; the naive outward-in scan (lps_halving) is
  * superlinear on inputs with long runs.  But a border is a period:
  *
  * {{{
  *     W has a border of length b   <=>   p = |W| - b is a period of W
  *                                 <=>   W occurs in W·W at position p   (0 < p <= |W|)
  * }}}
  *
  * so *all* borders of W are the occurrence positions of W in W·W, in increasing order
  * of p (decreasing border length), and the longest border is the first occurrence.
  * Two-way matching reports all occurrences of a pattern of length n in a text of
  * length 2n in O(n) time with O(1) extra space: a critical factorization of the
  * pattern (two maximal-suffix scans) and a search that keeps four integers.  Every
  * integer is a position or a distance between positions — a head, or two heads moved
  * in lockstep — so the whole thing is a multitape Turing machine with local moves.
  *
  * Galil's algorithm calls FPP twice; both become this:
  *   - nonchain `move`: longest border of the window  = first occurrence;
  *   - `dp(C, r)`: all palindromes ending at C = all borders of the window, emitted in
  *     decreasing length, which is exactly the order in which Galil marks their left
  *     ends on a tape before scanning with two heads at speeds 2 and 4.
  *
  * Correctness of `twoWaySearch` is checked against brute force on random and
  * exhaustive inputs; `period` and `borders` are checked on all binary strings up to
  * length 14; the comparison count is checked to be linear.
  */
object Twoway {

  /** Python の `counter=[0]`：比較回数を数える可変セル。 */
  final class Counter {
    var value: Int = 0
    def bump(): Unit = { value += 1 }
  }

  /** Crochemore-Perrin: (ms, p) with x[ms+1:] the maximal suffix for the order
    * (a < b iff greater(a, b) is False and a != b) and p its period.  ms may be -1.
    */
  private def maximalSuffix(x: String, greater: Boolean): (Int, Int) = {
    val n = x.length
    var ms = -1
    var j = 0
    var k = 1
    var p = 1
    while (j + k < n) {
      val a = x.charAt(j + k)
      val b = x.charAt(ms + k)
      val smaller = if (!greater) a < b else a > b
      if (smaller) {
        j += k
        k = 1
        p = j - ms
      } else if (a == b) {
        if (k != p) {
          k += 1
        } else {
          j += p
          k = 1
        }
      } else {
        ms = j
        j = ms + 1
        k = 1
        p = 1
      }
    }
    (ms, p)
  }

  /** (suffix, period): x[:suffix] · x[suffix:] is a critical factorization and
    * `period` is the local period there (= the global period when x is periodic).
    */
  def criticalFactorization(x: String): (Int, Int) = {
    val (ms1, p1) = maximalSuffix(x, greater = false)
    val (ms2, p2) = maximalSuffix(x, greater = true)
    if (ms2 > ms1) (ms2 + 1, p2) else (ms1 + 1, p1)
  }

  /** All occurrence positions of needle in haystack, increasing.  Comparisons are
    * counted in `counter` when given.
    */
  def twoWaySearch(needle: String, haystack: String, counter: Option[Counter] = None): Vector[Int] = {
    val n = needle.length
    val m = haystack.length
    if (n == 0) { return (0 to m).toVector }
    if (n > m) { return Vector.empty }
    val out = mutable.ArrayBuffer.empty[Int]

    def cmpEq(i: Int, j: Int): Boolean = {
      counter.foreach(_.bump())
      needle.charAt(i) == haystack.charAt(j)
    }

    val (suffix, period) = criticalFactorization(needle)
    // periodic pattern iff the prefix of length `suffix` repeats with `period`
    val periodic = suffix + period <= n && (0 until suffix).forall(i => needle.charAt(i) == needle.charAt(i + period))
    if (periodic) {
      var memory = 0
      var j = 0
      while (j <= m - n) {
        var i = math.max(suffix, memory)
        while (i < n && cmpEq(i, i + j)) { i += 1 }
        if (i >= n) {
          i = suffix - 1
          while (i + 1 > memory && cmpEq(i, i + j)) { i -= 1 }
          if (i + 1 <= memory) { out += j }
          j += period
          memory = n - period
        } else {
          j += i - suffix + 1
          memory = 0
        }
      }
    } else {
      val shift = math.max(suffix, n - suffix) + 1
      var j = 0
      while (j <= m - n) {
        var i = suffix
        while (i < n && cmpEq(i, i + j)) { i += 1 }
        if (i >= n) {
          i = suffix - 1
          while (i >= 0 && cmpEq(i, i + j)) { i -= 1 }
          if (i < 0) { out += j }
          j += shift
        } else {
          j += i - suffix + 1
        }
      }
    }
    out.toVector
  }

  // WARNING (2026-09-05): the reduction below is WRONG.  W occurs in W·W at position p
  // iff W is invariant under rotation by p, which is strictly stronger than "p is a
  // period of W" (e.g. 'aba' has period 2 but 'abaaba'[2:5] == 'aab').  Verified:
  // 320 failures on all binary strings up to length 8.  `twoWaySearch` itself is
  // correct (31,682 exhaustive + 3,000 random, 0 mismatches); only periods/period/
  // borders/longestBorder are broken.  See HANDOFF.md §3a/§3b for the fix direction.

  /** BROKEN — see warning above.  Kept for the record. */
  def periods(w: String, counter: Option[Counter] = None): Vector[Int] = {
    val n = w.length
    if (n == 0) { return Vector.empty }
    twoWaySearch(w, w + w, counter).filter(p => 1 <= p && p <= n)
  }

  def period(w: String, counter: Option[Counter] = None): Int = {
    periods(w, counter).headOption.getOrElse(0)
  }

  /** All proper border lengths of W, decreasing. */
  def borders(w: String, counter: Option[Counter] = None): Vector[Int] = {
    val n = w.length
    periods(w, counter).filter(_ < n).map(n - _)
  }

  def longestBorder(w: String, counter: Option[Counter] = None): Int = {
    val n = w.length
    if (n != 0) n - period(w, counter) else 0
  }

  // ------------------------------------------------------------------ references

  def bruteOccurrences(needle: String, haystack: String): Vector[Int] = {
    val n = needle.length
    val m = haystack.length
    (0 to m - n).filter(j => haystack.substring(j, j + n) == needle).toVector
  }

  def bruteBorders(w: String): Vector[Int] = {
    val n = w.length
    ((n - 1) to 1 by -1).filter(b => w.substring(0, b) == w.substring(n - b)).toVector
  }

  /** All strings over `alphabet` of length `n`, in `itertools.product` order. */
  def product(alphabet: String, n: Int): Iterator[String] = {
    if (n == 0) Iterator("")
    else product(alphabet, n - 1).flatMap(prefix => alphabet.iterator.map(c => prefix + c))
  }

  /** Adversarial families used by the linearity checks (shared with twoway_border). */
  def families(random: PyRandom): Vector[Int => String] = Vector(
    n => ("b" * (n / 2)) + "a" + ("b" * (n / 4)) + "aa" + ("b" * (n - n / 2 - n / 4 - 3)),
    n => ("a" * (n / 2)) + "b" + ("a" * (n / 2)),
    n => ("aaab" * n).substring(0, n),
    n => (0 until n).map(i => "ab".charAt(Integer.bitCount(i) % 2)).mkString,
    n => { val h = random.word("ab", n / 2); h + h.reverse },
    n => random.word("ab", n)
  )

  /** Flip character i of w. */
  def flip(w: String, i: Int): String = {
    w.substring(0, i) + (if (w.charAt(i) == 'b') "a" else "b") + w.substring(i + 1)
  }

  /** The `__main__` demo of twoway.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    val random = new PyRandom(7)
    // 1. search correctness: exhaustive small, random larger
    var bad = 0
    var tot = 0
    for (nl <- 1 until 6; hl <- 0 until 9; needle <- product("ab", nl); hay <- product("ab", hl)) {
      tot += 1
      if (twoWaySearch(needle, hay) != bruteOccurrences(needle, hay)) {
        bad += 1
        if (bad <= 3) {
          out.append(s"BAD search $needle $hay ${PyFormat.intListRepr(twoWaySearch(needle, hay))} " +
            s"${PyFormat.intListRepr(bruteOccurrences(needle, hay))}\n")
        }
      }
    }
    out.append(s"two-way search: $tot exhaustive (needle<=5, haystack<=8) -> mismatches $bad\n")
    bad = 0
    for (_ <- 0 until 3000) {
      val alpha = random.choice(Vector("ab", "ab", "abc"))
      val needle = random.word(alpha, random.randint(1, 12))
      var hay = random.word(alpha, random.randint(0, 60))
      if (random.random() < 0.5) {
        val k = random.randint(1, 4)
        hay = (needle * k + hay).take(60)
      }
      if (twoWaySearch(needle, hay) != bruteOccurrences(needle, hay)) {
        bad += 1
        if (bad <= 3) { out.append(s"BAD search $needle $hay\n") }
      }
    }
    out.append(s"two-way search: 3000 random -> mismatches $bad\n")

    // 2. borders / period via W·W, all binary strings up to length 14
    bad = 0
    tot = 0
    for (n <- 1 until 15; w <- product("ab", n)) {
      tot += 1
      if (borders(w) != bruteBorders(w)) {
        bad += 1
        if (bad <= 3) {
          out.append(s"BAD borders $w ${PyFormat.intListRepr(borders(w))} ${PyFormat.intListRepr(bruteBorders(w))}\n")
        }
      }
    }
    out.append(s"borders via two-way on W·W: $tot strings -> mismatches $bad\n")

    // 3. the actual blocker: longest border of every palindrome up to length 24
    bad = 0
    tot = 0
    for (n <- 1 until 25; h <- product("ab", (n + 1) / 2)) {
      val w = h + (if (n % 2 != 0) h.dropRight(1) else h).reverse
      tot += 1
      val want = bruteBorders(w)
      if (longestBorder(w) != want.headOption.getOrElse(0)) {
        bad += 1
        if (bad <= 3) { out.append(s"BAD lb $w\n") }
      }
    }
    out.append(s"longest border of palindromes up to length 24: $tot -> mismatches $bad\n")

    // 4. linearity: comparisons per |W| on adversarial and random inputs
    var worst = (0.0, "", 0)
    val fams = families(random)
    for (n <- Vector(64, 256, 1024, 4096); mk <- fams) {
      val w = mk(n)
      val c = new Counter
      borders(w, Some(c))
      val r = c.value.toDouble / w.length
      if (r > worst._1) { worst = (r, w.take(24) + "...", n) }
    }
    out.append("comparisons per |W| for all borders, worst over families at n=64..4096: " +
      s"${PyFormat.fixed(worst._1, 2)} on ${PyFormat.strRepr(worst._2)} (n=${worst._3})\n")
    // hill climb
    var best = (0.0, "", 0)
    for (n <- Vector(48, 96, 192); _ <- 0 until 4) {
      var w = random.word("ab", n)
      var cur: Option[Double] = None
      for (_ <- 0 until 300) {
        val i = random.randrange(n)
        val z = flip(w, i)
        val c = new Counter
        borders(z, Some(c))
        val cz = c.value.toDouble / n
        if (cur.forall(cz >= _)) { w = z; cur = Some(cz) }
      }
      if (cur.exists(_ > best._1)) { best = (cur.get, w.take(24) + "...", n) }
    }
    out.append(s"hill-climb worst comparisons per |W|: ${PyFormat.fixed(best._1, 2)} on ${PyFormat.strRepr(best._2)} (n=${best._3})\n")
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
