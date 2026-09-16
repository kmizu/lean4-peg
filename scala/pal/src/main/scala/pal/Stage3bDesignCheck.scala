package pal

import Stage2TmGalil.{Drivers, Yield}
import Stage3TmGalilChain.{DpSearch, KmpSuffixPalindromes, Machine, RATE, chainLast}

/** Stage 3b — design check for the SCA port.  Same algorithm as stage 3, plus
  * (1) a cyclic head Dc over [C-h, C] that must agree with D at every step, and
  * (2) the extension test read through the mirror about the old centre (a_{R-lag},
  * lag = k*h - 2 after k chain moves) whenever L is virtual; asserted equal to the
  * direct read.  Galil's algorithm with the chain case, on the stage-2 machinery.
  * （Python 版: `docs/palindromes-in-peg/stage3b_design_check.py`。`Machine`,
  * `kmp_suffix_palindromes`, `dp_search` は stage 3 と同一のコードなので
  * `Stage3TmGalilChain` のものを共有する。）
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
  */
object Stage3bDesignCheck {

  val SPACE: Char = Stage3TmGalilChain.SPACE

  /** Galil's algorithm with the design-check assertions; one `yld()` per elementary step. */
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
    var dc = 0 // cyclic walker over [C-h, C]
    var dlo = 0
    var lag = 0
    var off = 0
    var search = new DpSearch(m, centre, 0)

    def advance(units: Int): Unit = {
      var k = 0
      while (k < units && !search.done) {
        search.next()
        k += 1
      }
    }

    def restartSearch(r: Int): Unit = { search = new DpSearch(m, centre, r) }

    /** `Dc -= 2; if Dc < Dlo: Dc += h` */
    def stepCyclic(hh: Int): Unit = {
      dc -= 2
      if (dc < dlo) { dc += hh }
    }

    while (m.avail < n) {
      m.feed()
      val c = m.rd(right + 2); yld() // new symbol (R+1 is a space)
      // --- background chain search (paced) ---------------------------------
      if (!search.done) {
        advance(RATE)
        for (_ <- 0 until RATE) { yld() }
        if (search.done) { pending = search.result }
      }
      // --- confirming a found chain ------------------------------------------
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
            dc = d; dlo = centre - hh // cyclic walker over [C-h, C]
            lag = 0; off = 0 // L is real
            m.tick(hh); yld()
          }
        }
      }
      // --- extension ---------------------------------------------------------
      val before: Option[Char] =
        if (h.isDefined && off > 0) {
          val mirror = m.rd(right - lag) // mirror read while L is virtual
          assert(left >= 3 && mirror == m.rd(left - 2), s"mirror $left $right $lag $off")
          Some(mirror)
        } else if (left >= 3) {
          Some(m.rd(left - 2))
        } else {
          None
        }
      if (before.contains(c)) {
        yld()
        left -= 2; right += 2
        if (h.isDefined) {
          val hh = h.get
          if (off > 0) { off -= 2 }
          val pred = m.rd(dc)
          assert(pred == m.rd(d), s"Dc $dc $d")
          stepCyclic(hh)
          if (pred != c) { // chain ends (Galil case 1)
            val r = chainLast(centre, right - 2, hh / 2) - centre
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
        if (h.isDefined && m.rd(dc) == c) {
          assert(m.rd(d) == c)
          yld()
          val hh = h.get
          centre += hh / 2; left += hh - 2; right += 2; d = left - 2 + hh
          stepCyclic(hh)
          assert(dc == d || (dc - d) % hh == 0, s"Dc after move $dc $d $hh")
          off += hh - 2
          lag = if (lag > 0) lag + hh else hh - 2
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
          h = None; d = 0; pending = None; verify = None; lag = 0; off = 0
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

  /** The `__main__` demo of stage3b_design_check.py, as the text it prints. */
  def demo(): String = Stage3TmGalilChain.demoText(runOnline, runRealtime)

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
