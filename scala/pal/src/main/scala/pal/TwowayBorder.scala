package pal

import Twoway.{Counter, bruteBorders, criticalFactorization, flip, product}

/** Longest border by two-way *partial* matching — HANDOFF.md §3b item 1.
  * （Python 版: `docs/palindromes-in-peg/twoway_border.py`）
  *
  * b is a border of W  <=>  the prefix W[:b] matches at position n-b in W, i.e. the
  * two-way search of pattern W in text W, started at shift j = n-b, matches until it
  * runs off the end of the text.  Two-way normally reports full occurrences only; here
  * each alignment j is tested for "matches up to the end of the text" and the first
  * such j gives the longest border n-j.  The critical-factorization shifts stay valid
  * (they only use the pattern's structure), so the cost bound of two-way should carry
  * over.  This file measures whether it does.
  */
object TwowayBorder {

  def longestBorderTwoway(w: String, counter: Option[Counter] = None): Int = {
    val n = w.length
    if (n <= 1) { return 0 }
    val needle = w
    val text = w

    def eq(i: Int, j: Int): Boolean = {
      counter.foreach(_.bump())
      needle.charAt(i) == text.charAt(j)
    }

    val (suffix, period) = criticalFactorization(needle)
    val periodic = suffix + period <= n && (0 until suffix).forall(i => needle.charAt(i) == needle.charAt(i + period))
    var memory = 0
    var j = 1
    while (j < n) {
      val remaining = n - j // text has `remaining` chars left from j
      // forward part: compare needle[suffix..remaining) against text[j+suffix..n)
      var i = if (periodic) math.max(suffix, memory) else suffix
      while (i < remaining && eq(i, j + i)) { i += 1 }
      if (i >= remaining) {
        // backward part: needle[0..suffix) vs text[j..j+suffix)
        var k = math.min(suffix, remaining) - 1
        val lo = if (periodic) memory else 0
        while (k >= lo && eq(k, j + k)) { k -= 1 }
        if (k < lo) { return n - j }
        if (periodic) {
          j += period
          memory = n - period
        } else {
          j += math.max(suffix, n - suffix) + 1
        }
      } else if (periodic) {
        j += i - suffix + 1
        memory = 0
      } else {
        j += i - suffix + 1
      }
    }
    0
  }

  /** The `__main__` demo of twoway_border.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    val random = new PyRandom(11)
    var bad = 0
    var tot = 0
    for (n <- 1 until 17; w <- product("ab", n)) {
      tot += 1
      val want = bruteBorders(w).headOption.getOrElse(0)
      if (longestBorderTwoway(w) != want) {
        bad += 1
        if (bad <= 5) { out.append(s"BAD $w ${longestBorderTwoway(w)} $want\n") }
      }
    }
    out.append(s"longest border via two-way partial match: $tot strings <=16 -> mismatches $bad\n")
    var worst = (0.0, "", 0)
    val fams = Twoway.families(random) :+ ((n: Int) => "a" * n)
    for (n <- Vector(64, 256, 1024, 4096); mk <- fams) {
      val w = mk(n)
      val c = new Counter
      longestBorderTwoway(w, Some(c))
      val r = c.value.toDouble / w.length
      if (r > worst._1) { worst = (r, w.take(24), n) }
    }
    out.append(s"families: worst comparisons/|W| = ${PyFormat.fixed(worst._1, 2)} on ${PyFormat.strRepr(worst._2)}... n=${worst._3}\n")
    var best = (0.0, "", 0)
    for (n <- Vector(64, 128, 256); _ <- 0 until 5) {
      var w = random.word("ab", n)
      var cur: Option[Double] = None
      for (_ <- 0 until 400) {
        val i = random.randrange(n)
        val z = flip(w, i)
        val c = new Counter
        longestBorderTwoway(z, Some(c))
        val cz = c.value.toDouble / n
        if (cur.forall(cz >= _)) { w = z; cur = Some(cz) }
      }
      if (cur.exists(_ > best._1)) { best = (cur.get, w.take(24), n) }
    }
    out.append(s"hill-climb: worst comparisons/|W| = ${PyFormat.fixed(best._1, 2)} on ${PyFormat.strRepr(best._2)}... n=${best._3}\n")
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
