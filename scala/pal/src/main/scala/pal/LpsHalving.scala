package pal

import Twoway.{Counter, product}

/** Longest palindromic suffix by halving — the candidate that unblocks FPP.
  * （Python 版: `docs/palindromes-in-peg/lps_halving.py`）
  *
  * The blocker recorded at the top of PROGRESS.md is: given a palindrome `W` of length
  * `n` whose smallest period exceeds `n/2`, find its longest proper border in O(n)
  * machine steps, with heads and marks only (no random access, no arrays of numbers).
  *
  * Reduction.  For such a `W`, the longest proper border `u` is a palindrome of length
  * `b < n/2` (borders of a palindrome are its palindromic prefixes, hence also its
  * palindromic suffixes).  Every palindromic suffix of `W` shorter than `n/2` lies
  * inside the second half `Y = W[n - ceil(n/2) ..]`, and conversely every palindromic
  * suffix of `Y` is a proper palindromic suffix of `W`.  Hence
  *
  * {{{
  *     longest proper border of W  =  longest palindromic suffix of the second half of W.
  * }}}
  *
  * So the blocker becomes: LPS(Y) for an arbitrary string Y.  That halves:
  *
  *   - if |LPS(Y)| <= |Y|/2 it is a palindromic suffix of the second half of Y, and by
  *     the same argument it *is* the LPS of that half — recurse on |Y|/2;
  *   - otherwise it is longer than |Y|/2, and the "long case" search finds it.
  *
  * Running the long-case search first and recursing only when it fails costs
  * T(m) = long(m) + T(m/2), so the whole thing is linear as soon as the long case is.
  *
  * `longCaseScan` is the naive version of the long case: slide the start `s` from 0
  * upwards and test `Y[s..]` for being a palindrome by comparing outwards-in, stopping
  * at the first success.  Two heads moving towards each other plus a restart head: a
  * machine can do it with no memory at all.  The question this file answers
  * experimentally is whether its total comparison count is linear.
  */
object LpsHalving {

  /** Largest l > len(Y)//2 with Y[len(Y)-l:] a palindrome, else None.
    * Comparisons are counted in `counter` when given.
    */
  def longCaseScan(y: String, counter: Option[Counter] = None): Option[Int] = {
    val m = y.length
    val limit = m / 2 // we only look for l > m//2, i.e. s < m - m//2
    var s = 0
    while (s < m - limit) {
      var i = s
      var j = m - 1
      var ok = true
      while (ok && i < j) {
        counter.foreach(_.bump())
        if (y.charAt(i) != y.charAt(j)) {
          ok = false
        } else {
          i += 1
          j -= 1
        }
      }
      if (ok) { return Some(m - s) }
      s += 1
    }
    None
  }

  /** Length of the longest palindromic suffix of Y (0 for the empty string). */
  def lps(y: String, counter: Option[Counter] = None): Int = {
    val m = y.length
    if (m <= 1) { return m }
    longCaseScan(y, counter) match {
      case Some(got) => got
      case None =>
        val half = (m + 1) / 2 // the last ceil(m/2) characters
        lps(y.substring(m - half), counter)
    }
  }

  /** Longest proper border of a palindrome W whose period exceeds |W|/2. */
  def longestBorderOfPalindrome(w: String, counter: Option[Counter] = None): Int = {
    val n = w.length
    val half = (n + 1) / 2
    lps(w.substring(n - half), counter)
  }

  // ------------------------------------------------------------------ references

  def bruteLps(y: String): Int = {
    val m = y.length
    (m to 1 by -1).find(l => y.substring(m - l) == y.substring(m - l).reverse).getOrElse(0)
  }

  def bruteLongestBorder(w: String): Int = {
    val n = w.length
    ((n - 1) to 1 by -1).find(b => w.substring(0, b) == w.substring(n - b)).getOrElse(0)
  }

  def smallestPeriod(w: String): Int = {
    val n = w.length
    (1 to n).find(p => (0 until n - p).forall(i => w.charAt(i) == w.charAt(i + p))).get
  }

  /** The `__main__` demo of lps_halving.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    // 1. lps correctness on all binary strings up to length 16
    var bad = 0
    var n = 0
    var stop = false
    while (n <= 16 && !stop) {
      for (y <- product("ab", n)) {
        if (lps(y) != bruteLps(y)) {
          bad += 1
          if (bad <= 3) { out.append(s"BAD lps $y ${lps(y)} ${bruteLps(y)}\n") }
        }
      }
      if (n >= 14 && bad > 0) { stop = true }
      n += 1
    }
    out.append(s"lps: all binary strings up to length 16 -> mismatches $bad\n")

    // 2. the reduction, on every palindrome with period > n/2
    bad = 0
    var tested = 0
    for (len <- 2 until 21; half <- product("ab", (len + 1) / 2)) {
      val w = half + (if (len % 2 != 0) half.dropRight(1) else half).reverse
      if (w.length == len && w == w.reverse && smallestPeriod(w) * 2 > len) {
        tested += 1
        if (longestBorderOfPalindrome(w) != bruteLongestBorder(w)) {
          bad += 1
          if (bad <= 3) {
            out.append(s"BAD border $w ${longestBorderOfPalindrome(w)} ${bruteLongestBorder(w)}\n")
          }
        }
      }
    }
    out.append(s"longest border of non-periodic palindromes: $tested tested -> mismatches $bad\n")

    // 3. cost: is the long-case scan linear?
    var worst = (0.0, "")
    for (len <- 1 until 19; y <- product("ab", len)) {
      val c = new Counter
      lps(y, Some(c))
      val ratio = c.value.toDouble / math.max(len, 1)
      if (ratio > worst._1) { worst = (ratio, y) }
    }
    out.append("lps cost: worst comparisons/|Y| over all strings up to length 18 = " +
      s"${PyFormat.fixed(worst._1, 2)} on ${PyFormat.strRepr(worst._2)}\n")

    val random = new PyRandom(1)
    var worstLong = (0.0, "")
    for (_ <- 0 until 400) {
      val len = random.randint(50, 400)
      val kind = random.randrange(4)
      val y = kind match {
        case 0 => random.word("ab", len)
        case 1 =>
          val p = random.word("ab", random.randint(1, 5))
          (p * len).substring(0, len)
        case 2 =>
          val h = random.word("ab", len / 2)
          h + h.reverse
        case _ => ("a" * (len / 2)) + "b" + ("a" * (len / 2 - 1))
      }
      val c = new Counter
      lps(y, Some(c))
      val ratio = c.value.toDouble / y.length
      if (ratio > worstLong._1) { worstLong = (ratio, y.take(30) + "...") }
    }
    out.append("lps cost on 400 long strings (len 50-400): worst comparisons/|Y| = " +
      s"${PyFormat.fixed(worstLong._1, 2)} on ${PyFormat.strRepr(worstLong._2)}\n")
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
