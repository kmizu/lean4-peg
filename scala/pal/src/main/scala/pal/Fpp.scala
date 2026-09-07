package pal

import java.math.{BigDecimal, RoundingMode}

import scala.collection.mutable

/** HISTORICAL NOTE (2026-09-05): fpp_tape.py now implements Fischer–Paterson's
  * unary adjacent-difference representation with local heads, including a seven
  * single-head-tape lowering. The objections below concern the earlier direct
  * failure-pointer encoding, not all KMP implementations. See FISCHER_PATERSON.md.
  *
  * FPP: all palindromic prefixes of a string, in linear time — reference implementation
  * and an analysis of what it costs in the machine model that compiles to a PEG.
  *
  * Galil's real-time recogniser calls FPP (Fischer & Paterson) twice: in the nonchain case
  * (the longest initial palindrome of the window) and in every stage of the double-palindrome
  * search (all initial palindromes of the window, marked on a tape).  So FPP is the last
  * missing component of the machine whose compilation yields a plain PEG for PAL.
  *
  * Reference algorithm.  `u[0..j]` is a palindrome iff `u[0..j]` equals its reverse, and the
  * palindromic prefixes of `u` are exactly the borders of `s = u # reverse(u)`: a border of
  * length L means `u[0..L-1] = reverse(u)[m-L..m-1] = reverse(u[0..L-1])`.  So one KMP
  * failure function over `s` gives all of them, in O(|u|) time.
  *
  * What the machine model can and cannot do with it (this is the point of the file):
  *
  *  - The failure function's values are positions, so they cannot live in tape cells.  They
  *    can live in *pointer-carrying cells* — a cell written by the head may store a pointer
  *    to any node already created — which the PEG encoding supports (a cell's fields are
  *    rules at the position where the cell was written).
  *  - The KMP cursor needs three operations: read `P[k+1]`, move to `k+1` on a match, and
  *    jump to `fail[k]` on a mismatch.
  *      - `P[k+1]` and `k+1` are easy if the cells carry a `next` pointer, which a
  *        right-to-left pass can build (a cell written later may point to one written
  *        earlier, so scanning right to left yields forward links).
  *      - `fail[k]` is easy if the cell for `k` carries a `fail` pointer, which a
  *        left-to-right pass can build (`fail[k] < k`, already created).
  *      - '''Both at once is the obstacle.'''  A left-to-right pass cannot store `next`
  *        (the target does not exist yet) and a right-to-left pass cannot store `fail`
  *        (the target does not exist yet), and the cursor needs both on the *same* cell.
  *        Splitting into two chains does not help: keeping a cursor into both chains in
  *        step requires moving forward in the fail chain, which is the same wall.
  *  - A zipper (a stack of the cells below the cursor plus a queue of those above) gives
  *    `+1` without pointers, but then the jump has to pop "until the top is the target",
  *    which is a pointer comparison — and the model has none.  Persistent snapshots remove
  *    the comparison but lose the cells created after the snapshot.
  *
  * `kmpFail` and `palindromicPrefixes` below are the reference; `analysis()` reports, for
  * random strings, how much of the work each attempted encoding can actually perform, which
  * is the measurement the next attempt should improve on.
  *
  * Python 原典: `fpp.py`。`main` は Python の `__main__` と同じ文字列を出力する
  * （`analysis()` の乱数列まで Python の `random` を再現している）。
  */
object Fpp {

  /** standard failure function; fail[j] = length of the longest proper border of s[0..j-1]. */
  def kmpFail(s: String): Vector[Int] = {
    val m = s.length
    val fail = Array.fill(m + 1)(0)
    var k = 0
    for (j <- 1 until m) {
      while (k > 0 && s(k) != s(j)) {
        k = fail(k)
      }
      if (s(k) == s(j)) {
        k += 1
      }
      fail(j + 1) = k
    }
    fail.toVector
  }

  /** lengths L >= 1 with u[0..L-1] a palindrome, via the borders of u # reverse(u). */
  def palindromicPrefixes(u: String, sep: Char = '#'): Vector[Int] = {
    assert(!u.contains(sep))
    val s = u + sep + u.reverse
    val fail = kmpFail(s)
    val out = mutable.ArrayBuffer.empty[Int]
    var l = fail(s.length)
    while (l > 0) {
      if (l <= u.length) {
        out += l
      }
      l = fail(l)
    }
    out.sorted.toVector
  }

  def brute(u: String): Vector[Int] =
    (1 to u.length).filter(l => u.take(l) == u.take(l).reverse).toVector

  /** The KMP cursor's moves, classified. */
  final case class CursorMoves(read: Int, jump: Int, plus1: Int)

  /** The KMP cursor's moves, classified: '+1' (needs a successor), 'jump' (needs a
    * stored fail pointer), 'read' (needs the symbol one to the right of the cursor).
    */
  def cursorTrace(s: String): CursorMoves = {
    val m = s.length
    val fail = Array.fill(m + 1)(0)
    var k = 0
    var read = 0
    var jump = 0
    var plus1 = 0
    for (j <- 1 until m) {
      read += 1
      while (k > 0 && s(k) != s(j)) {
        k = fail(k)
        jump += 1
        read += 1
      }
      if (s(k) == s(j)) {
        k += 1
        plus1 += 1
      }
      fail(j + 1) = k
    }
    CursorMoves(read, jump, plus1)
  }

  /** Python の `analysis(trials=200, seed=5)` が print する 2 行。 */
  def analysis(trials: Int = 200, seed: Int = 5): String = {
    val random = new PythonRandom(seed)
    var worst: Option[(Double, String)] = None
    var totalRead = 0
    var totalJump = 0
    var totalPlus1 = 0
    var totalLen = 0
    for (_ <- 0 until trials) {
      val n = random.randint(4, 200)
      val kind = random.randrange(3)
      val u = kind match {
        case 0 => Vector.fill(n)(random.choice("ab")).mkString
        case 1 =>
          val p = Vector.fill(random.randint(1, 4))(random.choice("ab")).mkString
          (p * n).take(n)
        case _ =>
          val h = Vector.fill(n / 2)(random.choice("ab")).mkString
          h + h.reverse
      }
      val s = u + "#" + u.reverse
      val mv = cursorTrace(s)
      totalRead += mv.read
      totalJump += mv.jump
      totalPlus1 += mv.plus1
      totalLen += s.length
      val r = (mv.jump + mv.plus1).toDouble / s.length
      if (worst.forall(r > _._1)) {
        worst = Some((r, u.take(20)))
      }
    }
    val perCharacter = (totalJump + totalPlus1).toDouble / totalLen
    s"cursor moves over $trials strings: reads $totalRead, jumps $totalJump, +1s $totalPlus1 " +
      s"for $totalLen characters (${fixed2(perCharacter)} cursor moves per character)\n" +
      s"  worst ratio ${fixed2(worst.get._1)} on ${pythonRepr(worst.get._2)}...\n"
  }

  /** Python の `f"{x:.2f}"`: 倍精度の正確な値を偶数丸め。 */
  private def fixed2(x: Double): String = new BigDecimal(x).setScale(2, RoundingMode.HALF_EVEN).toPlainString

  /** Python の `repr(str)`（ここで現れるのは 'a'/'b' だけなので単一引用符で囲むだけ）。 */
  private def pythonRepr(s: String): String = "'" + s + "'"

  /** Python の `if __name__ == '__main__':` ブロックの出力。 */
  def mainText(): String = {
    val out = new StringBuilder
    var bad = 0
    for (n <- 0 to 12) {
      for (u <- binaryWords(n)) {
        if (palindromicPrefixes(u) != brute(u)) {
          bad += 1
          if (bad <= 3) {
            out.append(s"BAD $u ${pythonList(palindromicPrefixes(u))} ${pythonList(brute(u))}\n")
          }
        }
      }
    }
    out.append(s"FPP reference: all binary strings up to length 12 -> mismatches $bad\n")
    out.append(analysis())
    out.toString
  }

  private def pythonList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")

  /** Python の `itertools.product('ab', repeat=n)`（辞書式順）。 */
  def binaryWords(n: Int): Iterator[String] =
    Iterator.range(0, 1 << n).map(i => (0 until n).map(b => if (((i >> (n - 1 - b)) & 1) == 0) { 'a' } else { 'b' }).mkString)

  def main(args: Array[String]): Unit = {
    print(mainText())
  }

  // ---------------------------------------------------------------- the way in: periods
  // The KMP route needs random access to fail[].  A *constant-space* route does not:
  // Crochemore-Perrin's maximal-suffix computation finds the period of a string with a
  // fixed number of indices (i, j, k, p) and one left-to-right scan, and indices are what
  // a Turing machine has — heads.  The border chain then comes out as O(log m) arithmetic
  // progressions: the longest border is m - period, the borders longer than m/2 are exactly
  // m - t*period, and the rest is the border chain of a string at most half as long, so the
  // total work telescopes to O(m).

  /** (index just before the maximal suffix, its period) — Crochemore-Perrin.
    * Uses four indices and one left-to-right scan: exactly what heads give a machine.
    */
  def maximalSuffix(x: String, greater: Boolean = true): (Int, Int) = {
    val n = x.length
    var ms = -1
    var j = 0
    var k = 1
    var p = 1
    while (j + k < n) {
      val a = x(j + k)
      val b = x(ms + k)
      if (if (greater) { a < b } else { a > b }) {
        j += k; k = 1; p = j - ms
      } else if (a == b) {
        if (k == p) {
          j += p; k = 1
        } else {
          k += 1
        }
      } else {
        ms = j; j = ms + 1; k = 1; p = 1
      }
    }
    (ms, p)
  }

  /** (critical position ell, candidate period p) by the two maximal suffixes. */
  def criticalFactorization(x: String): (Int, Int) = {
    val (i1, p1) = maximalSuffix(x, true)
    val (i2, p2) = maximalSuffix(x, false)
    if (i1 >= i2) { (i1, p1) } else { (i2, p2) }
  }

  /** the smallest period of x when it is at most |x|/2 (the 'periodic' case, which is
    * exactly Galil's chain case); None otherwise.  Constant space, linear time.
    */
  def periodIfPeriodic(x: String): Option[Int] = {
    val n = x.length
    if (n == 0) {
      None
    } else {
      val (ell, p) = criticalFactorization(x)
      if (p <= n / 2 && x.take(p) == x.slice(p, 2 * p).take(p) && x.take(ell + 1) == x.slice(p, p + ell + 1)) {
        // verify p is a period of the whole word (one scan)
        if ((0 until n - p).forall(i => x(i) == x(i + p))) { Some(p) } else { None }
      } else {
        None
      }
    }
  }

  /** Python 原典の `borders_via_periods` は未定義の `period(cur)` を呼ぶ（NameError）。
    * この行き止まりをそのまま残す: 空でない入力では同じ箇所で例外になる。
    */
  private def period(cur: String): Int =
    throw new NotImplementedError(s"period() was never defined in fpp.py (dead end); called on ${cur.take(20)}")

  /** all border lengths of x, in decreasing order, by peeling arithmetic progressions. */
  def bordersViaPeriods(x: String): Vector[Int] = {
    val out = mutable.ArrayBuffer.empty[Int]
    var cur = x
    var running = true
    while (running && cur.nonEmpty) {
      val n = cur.length
      val p = period(cur)
      if (p == n) { // no nontrivial border
        running = false
      } else {
        val b = n - p // longest border
        // borders longer than n/2 are exactly n - t*p while positive and > n/2
        var t = 1
        while (n - t * p > 0 && n - t * p >= n - b && n - t * p > n / 2) {
          out += n - t * p
          t += 1
        }
        // continue with the longest border of length <= n/2 in the chain
        val nxt = n - t * p
        if (nxt <= 0) {
          cur = ""
        } else {
          out += nxt
          cur = cur.take(nxt)
          // the remaining chain is the border chain of cur, handled by the next round
        }
        if (out.size > 4 * x.length + 8) {
          throw new IllegalStateException("runaway")
        }
      }
    }
    val seen = mutable.ArrayBuffer.empty[Int]
    for (b <- out) {
      if (b > 0 && (seen.isEmpty || seen.last != b)) {
        seen += b
      }
    }
    seen.toVector
  }

  def bordersReference(x: String): Vector[Int] = {
    val f = kmpFail(x)
    val out = mutable.ArrayBuffer.empty[Int]
    var l = f(x.length)
    while (l > 0) {
      out += l
      l = f(l)
    }
    out.toVector
  }

  /** CPython の `random.Random` の再現（MT19937 + `_randbelow_with_getrandbits`）。
    *
    * `analysis()` が Python と同じ乱数列を使うために必要。整数 seed のみ対応。
    */
  final class PythonRandom(seed: Int) {
    private val N = 624
    private val M = 397
    private val MASK = 0xffffffffL
    private val mt = new Array[Long](N)
    private var mti = N + 1

    initGenrand(19650218L)
    initByArray(Array(math.abs(seed).toLong))

    private def initGenrand(s: Long): Unit = {
      mt(0) = s & MASK
      for (i <- 1 until N) {
        mt(i) = (1812433253L * (mt(i - 1) ^ (mt(i - 1) >>> 30)) + i) & MASK
      }
      mti = N
    }

    private def initByArray(key: Array[Long]): Unit = {
      var i = 1
      var j = 0
      var k = math.max(N, key.length)
      while (k > 0) {
        mt(i) = ((mt(i) ^ ((mt(i - 1) ^ (mt(i - 1) >>> 30)) * 1664525L)) + key(j) + j) & MASK
        i += 1
        j += 1
        if (i >= N) { mt(0) = mt(N - 1); i = 1 }
        if (j >= key.length) { j = 0 }
        k -= 1
      }
      k = N - 1
      while (k > 0) {
        mt(i) = ((mt(i) ^ ((mt(i - 1) ^ (mt(i - 1) >>> 30)) * 1566083941L)) - i) & MASK
        i += 1
        if (i >= N) { mt(0) = mt(N - 1); i = 1 }
        k -= 1
      }
      mt(0) = 0x80000000L
    }

    private def genrandUint32(): Long = {
      if (mti >= N) {
        for (kk <- 0 until N) {
          val y = (mt(kk) & 0x80000000L) | (mt((kk + 1) % N) & 0x7fffffffL)
          mt(kk) = mt((kk + M) % N) ^ (y >>> 1) ^ (if ((y & 1L) == 0L) { 0L } else { 0x9908b0dfL })
        }
        mti = 0
      }
      var y = mt(mti)
      mti += 1
      y ^= (y >>> 11)
      y ^= (y << 7) & 0x9d2c5680L
      y ^= (y << 15) & 0xefc60000L
      y ^= (y >>> 18)
      y & MASK
    }

    /** `getrandbits(k)` for `0 < k <= 32`. */
    def getrandbits(k: Int): Long = {
      require(0 < k && k <= 32)
      genrandUint32() >>> (32 - k)
    }

    /** `_randbelow_with_getrandbits(n)`: rejection sampling on `n.bit_length()` bits. */
    def randbelow(n: Int): Int = {
      val k = GalilClock.bitLength(n)
      var r = getrandbits(k)
      while (r >= n) {
        r = getrandbits(k)
      }
      r.toInt
    }

    /** `randrange(n)`. */
    def randrange(n: Int): Int = randbelow(n)

    /** `randint(a, b)` = `a + randbelow(b - a + 1)`. */
    def randint(a: Int, b: Int): Int = a + randbelow(b - a + 1)

    /** `choice(seq)`. */
    def choice(seq: String): Char = seq(randbelow(seq.length))
  }
}
