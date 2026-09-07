package pal

import scala.collection.mutable

import Stage2TmGalil.{Costed, Drivers, MARK, Tape, Yield}
import Twoway.product

/** Stage 3: Galil's algorithm with the chain case, on the stage-2 machinery.
  * （Python 版: `docs/palindromes-in-peg/stage3_tm_galil_chain.py`）
  *
  * Encoding (Galil): places.  Place 0 = left marker; input symbol i (1-based) sits at
  * place 2i-1; place 2i is a space symbol.  Every palindrome of the symbol string is an
  * odd-length palindrome of the place string centred at a place (a space for even
  * symbol-palindromes).  L, R, C, D are places; h is the period of the active
  * palindrome in places (always even); Galil's chain step is h_G = h/2.
  *
  * One iteration per new symbol (R advances by two places):
  *   - extension: a_{L-2} = c  ->  [L-2, R+2].  While a chain is alive, head D at
  *     place L-2+h predicts the extension symbol; if a_D != c the chain ends (Galil
  *     case 1) and a search for a coarser chain (step > CH_last - C) is started.
  *   - mismatch with a_D = c (Galil case 2b, chain case): C += h/2, L += h-2, R += 2.
  *     Cost O(h), paid because the centre moves h/2.
  *   - mismatch otherwise: `move` = KMP over the window (O(R-L)), paid because the
  *     centre moves >= (R-C)/4 (nonchain case); then the search for the new centre is
  *     replayed off-line (main1) with RATE*(R-C) units, then continues in the background.
  *   - background search dp(C, r): doubling stages over windows ending at C; a stage
  *     finds all palindromes ending at C via KMP and looks for a double palindrome
  *     (lengths 2h_G+1 and 4h_G+1) with step h_G > r; paced at RATE units per symbol.
  *     A found chain is used once its right half fits: R >= C + 4 h_G.
  *
  * Correctness is checked online (unbounded time); real-time-ness by the budgeted
  * driver: its output must equal the truth although the algorithm may lag.
  *
  * ==generator の扱い==
  *
  * 外側の `galil` は `Yield` コールバック方式（Stage2TmGalil 参照）。背景探索
  * `dp_search` だけは `advance(units)` で少しずつ進められる本物の generator なので、
  * `DpSearch`（と内部の `KmpSuffixPalindromes`）を再開可能な状態機械として移植した。
  * `next()` 1 回 = Python の `next(gen)` 1 回で、yield の回数・`m.rd` の回数は同一。
  */
object Stage3TmGalilChain {

  val SPACE: Char = '_'
  /** Search units per input symbol (stage i must finish before R-C ~ |u_i|/4). */
  val RATE: Int = 64

  final class Machine(val x: String) extends Costed {
    val tape: Tape[Char] = new Tape[Char]
    tape.set(0, MARK)
    var avail: Int = 0 // number of symbols fed
    var last: Int = 0 // last readable place
    var steps: Int = 0
    val out: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

    def feed(): Unit = {
      val i = avail + 1
      tape.set(2 * i - 1, x.charAt(i - 1))
      tape.set(2 * i, SPACE)
      avail = i
      last = 2 * i
    }

    def rd(place: Int): Char = {
      assert(0 <= place && place <= last, s"online violation at place $place")
      steps += 1
      tape.sym(place).getOrElse(throw new NoSuchElementException(s"place $place is empty"))
    }

    def tick(n: Int = 1): Unit = { steps += n }
  }

  private enum KmpPhase {
    case Build, Scan, Collect, Done
  }

  private enum SearchPhase {
    case Start, Kmp, Candidates
  }

  /** Lengths (in places, decreasing) of all palindromes ending at place `hi` that
    * start at or after place `lo`: KMP with pattern = reverse(window), text = window.
    * Cost O(hi - lo).  A resumable generator: `next()` runs to the next yield and
    * returns true, or returns false once `lengths` is complete.
    *
    * {{{
    *   for j in 1..n-1:  cj = P(j); yield;  while q>0 and P(q)!=cj: q=fail[q]; yield;  ...; fail[j+1]=q; yield
    *   for i in 0..n-1:  ti = T(i); yield;  while q>0 and P(q)!=ti: q=fail[q]; yield;  ...; yield
    *   while q > 0:      lengths.append(q); q = fail[q]; yield
    * }}}
    */
  final class KmpSuffixPalindromes(m: Machine, lo: Int, hi: Int) {
    private val n = hi - lo + 1
    private val fail = new Array[Int](n + 1)
    private var q = 0
    val lengths: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

    private var phase = KmpPhase.Build
    private var j = 1 // Build loop index
    private var i = 0 // Scan loop index
    private var inWhile = false // resumed inside the inner `while` (after reading the char)
    private var cur: Char = ' '

    private def pattern(k: Int): Char = m.rd(hi - k) // pattern = window reversed
    private def text(k: Int): Char = m.rd(lo + k) // text = window

    def next(): Boolean = {
      var yielded = false
      var finished = false
      while (!yielded && !finished) {
        phase match {
          case KmpPhase.Build =>
            if (!inWhile) {
              if (j >= n) { phase = KmpPhase.Scan; q = 0; i = 0 }
              else { cur = pattern(j); inWhile = true; yielded = true }
            } else if (q > 0 && pattern(q) != cur) {
              q = fail(q); yielded = true
            } else {
              if (pattern(q) == cur) { q += 1 }
              fail(j + 1) = q; j += 1; inWhile = false; yielded = true
            }
          case KmpPhase.Scan =>
            if (!inWhile) {
              if (i >= n) { phase = KmpPhase.Collect }
              else { cur = text(i); inWhile = true; yielded = true }
            } else if (q > 0 && pattern(q) != cur) {
              q = fail(q); yielded = true
            } else {
              if (pattern(q) == cur) { q += 1 }
              i += 1; inWhile = false; yielded = true
            }
          case KmpPhase.Collect =>
            if (q > 0) { lengths += q; q = fail(q); yielded = true }
            else { phase = KmpPhase.Done; finished = true }
          case KmpPhase.Done =>
            finished = true
        }
      }
      yielded
    }

    /** Drive to completion as `yield from` would, forwarding every yield. */
    def runWith(yld: Yield): Vector[Int] = {
      while (next()) { yld() }
      lengths.toVector
    }
  }

  /** Smallest h_G > r such that [C-4h_G, C] is a double palindrome, by doubling
    * stages; None if there is none.  A resumable generator (one yield per unit):
    * `next()` returns true at a yield, false when finished (`result` is then valid).
    */
  final class DpSearch(m: Machine, c: Int, r: Int) {
    private var i = 1
    private var lo = 0
    private var isFinal = false
    private var kmp: KmpSuffixPalindromes = null
    private var have: Set[Int] = Set.empty
    private var hmax = 0
    private var hg = 0
    private var checkPending = false
    private var hgPending = 0
    private var finished = false
    private var found: Option[Int] = None

    /** Valid once `next()` has returned false. */
    def result: Option[Int] = found
    def done: Boolean = finished

    private var phase = SearchPhase.Start

    def next(): Boolean = {
      if (finished) { return false }
      var yielded = false
      while (!yielded && !finished) {
        phase match {
          case SearchPhase.Start =>
            val ell = (8L * math.max(r, 1)) << (i - 1)
            lo = math.max(1L, c - ell).toInt
            isFinal = lo == 1
            kmp = new KmpSuffixPalindromes(m, lo, c)
            phase = SearchPhase.Kmp
          case SearchPhase.Kmp =>
            if (kmp.next()) { yielded = true }
            else {
              have = kmp.lengths.toSet
              hmax = (c - lo) / 4
              hg = r + 1
              checkPending = false
              phase = SearchPhase.Candidates
            }
          case SearchPhase.Candidates =>
            if (checkPending && have.contains(2 * hgPending + 1) && have.contains(4 * hgPending + 1)) {
              found = Some(hgPending); finished = true
            } else if (hg <= hmax) {
              m.tick(); hgPending = hg; hg += 1; checkPending = true; yielded = true
            } else if (isFinal) {
              found = None; finished = true
            } else {
              i += 1; phase = SearchPhase.Start
            }
        }
      }
      yielded
    }
  }

  /** The place of the last chain member at or before R: C + h_G * max((R-C)/h_G - 1, 0). */
  def chainLast(c: Int, r: Int, hg: Int): Int = {
    val i = (r - c) / hg - 1
    c + hg * math.max(i, 0)
  }

  /** Galil's algorithm with chain and nonchain cases; one `yld()` per elementary step. */
  def galil(m: Machine, yld: Yield): Unit = {
    val n = m.x.length
    m.feed()
    var left = 1
    var right = 1
    var centre = 1
    m.tick(); yld()
    m.out += 1
    var h: Option[Int] = None
    var d = 0
    var pending: Option[Int] = None // h_G found, waiting for R >= C + 4 h_G
    var verify: Option[Int] = None // verification pointer while confirming
    var search = new DpSearch(m, centre, 0)

    def advance(units: Int): Unit = {
      var k = 0
      while (k < units && !search.done) {
        search.next()
        k += 1
      }
    }

    /** `search = dp_search(m, C, r)` */
    def restartSearch(r: Int): Unit = { search = new DpSearch(m, centre, r) }

    while (m.avail < n) {
      m.feed()
      val c = m.rd(right + 2); yld() // new symbol (R+1 is a space)
      // --- background chain search (paced) ---------------------------------
      if (!search.done) {
        advance(RATE)
        for (_ <- 0 until RATE) { yld() }
        if (search.done) { pending = search.result }
      }
      // --- confirming a found chain: its mirror half [C, C+4h_G] holds once
      //     R >= C + 4h_G; beyond that, verify periodicity up to R at 4 places
      //     per symbol (Galil's right-dp, then D would have watched) -----------
      if (h.isEmpty && pending.isDefined) {
        val hg = pending.get
        val hh = 2 * hg
        if (verify.isEmpty && right >= centre + 4 * hg) { verify = Some(centre + 4 * hg + 1) }
        if (verify.isDefined) {
          var k = 0
          var stop = false
          while (k < 4 && !stop) {
            if (verify.get > right) { stop = true }
            else {
              val a1 = m.rd(verify.get); val a2 = m.rd(verify.get - hh); yld()
              if (a1 != a2) { // chain ended before R
                val r = chainLast(centre, verify.get - 1, hg) - centre
                pending = None; verify = None
                restartSearch(r)
                stop = true
              } else {
                verify = Some(verify.get + 1)
                k += 1
              }
            }
          }
          if (pending.isDefined && verify.get > right) {
            h = Some(hh); d = left - 2 + hh; pending = None; verify = None
            m.tick(hh); yld()
          }
        }
      }
      // --- extension ---------------------------------------------------------
      if (left >= 3 && m.rd(left - 2) == c) {
        yld()
        left -= 2; right += 2
        if (h.isDefined) {
          if (m.rd(d) != c) { // chain ends (Galil case 1)
            val r = chainLast(centre, right - 2, h.get / 2) - centre
            h = None; d = 0; pending = None; verify = None
            restartSearch(r)
          } else {
            d -= 2
          }
          yld()
        }
        m.out += (if (left == 1) 1 else 0)
      } else {
        yld()
        // --- mismatch, chain case (Galil case 2b) --------------------------------
        if (h.isDefined && m.rd(d) == c) {
          yld()
          val hh = h.get
          centre += hh / 2; left += hh - 2; right += 2; d = left - 2 + hh
          m.tick(hh); yld()
          m.out += (if (left == 1) 1 else 0)
        } else {
          // --- mismatch, nonchain: move -------------------------------------------
          val lengths = new KmpSuffixPalindromes(m, left, right).runWith(yld)
          var newL: Option[Int] = None
          val it = lengths.iterator
          while (newL.isEmpty && it.hasNext) {
            val ell = it.next()
            val st = right - ell + 1
            if (st >= 3 && m.rd(st - 2) == c) { newL = Some(st - 2) }
            else { yld() }
          }
          if (newL.isEmpty) {
            newL = Some(if (m.rd(right) == c) right else right + 2)
            yld()
          }
          right += 2; left = newL.get; centre = (left + right) / 2
          h = None; d = 0; pending = None; verify = None
          restartSearch(0)
          val units = RATE * (right - centre) // main1: off-line replay, paid by the move
          advance(units)
          for (_ <- 0 until units) { yld() }
          if (search.done) { pending = search.result }
          m.out += (if (left == 1) 1 else 0)
        }
      }
    }
  }

  def runOnline(x: String): (Vector[Int], Vector[Int]) = {
    val m = new Machine(x)
    Drivers.runOnline(m, yld => galil(m, yld), multi = true)
  }

  def runRealtime(x: String, budget: Int): Vector[Int] = {
    val m = new Machine(x)
    Drivers.runRealtime(m, yld => galil(m, yld), budget, x.length)
  }

  def brute(x: String): Vector[Int] = Stage2TmGalil.brute(x)

  /** The `__main__` demo, shared with stage 3b (same text, different algorithm). */
  def demoText(online: String => (Vector[Int], Vector[Int]), realtime: (String, Int) => Vector[Int]): String = {
    val out = new StringBuilder
    var bad = 0
    var tot = 0
    var worst = 0
    var worstX = ""
    for (nlen <- 1 until 13; x <- product("ab", nlen)) {
      tot += 1
      val (got, cost) = online(x)
      if (got != brute(x)) {
        bad += 1
        if (bad <= 5) {
          out.append(s"BAD online $x ${PyFormat.intListRepr(got)} ${PyFormat.intListRepr(brute(x))}\n")
        }
      }
      if (cost.max > worst) { worst = cost.max; worstX = x }
    }
    out.append(s"online: strings $tot bad $bad worst cost/symbol $worst at $worstX\n")
    for (x <- Vector("ab" * 100, "a" * 200, "aab" * 60, "abba" * 50, "aabab" * 40)) {
      val (got, cost) = online(x)
      val ok = got == brute(x)
      out.append(s"  ${x.take(8)}...: ok=${if (ok) "True" else "False"} steps/n = " +
        s"${PyFormat.fixed(cost.sum.toDouble / x.length, 1)}, max step ${cost.max}\n")
    }
    for (budget <- Vector(64, 128, 256)) {
      bad = 0
      for (nlen <- 1 until 13; x <- product("ab", nlen)) {
        if (realtime(x, budget) != brute(x)) { bad += 1 }
      }
      out.append(s"realtime budget $budget: mismatching strings $bad/$tot\n")
    }
    out.toString
  }

  /** The `__main__` demo of stage3_tm_galil_chain.py, as the text it prints. */
  def demo(): String = demoText(runOnline, runRealtime)

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
