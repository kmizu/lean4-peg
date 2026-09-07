package pal

import scala.collection.mutable

import Twoway.product

/** Stage 2: Galil's real-time palindrome recogniser as a multitape Turing machine,
  * built incrementally.  This file = the machinery + `match` + the nonchain `move`
  * (FPP replaced by KMP on work tapes).  Everything the machine does is a generator
  * that yields once per elementary tape operation, so cost is counted mechanically.
  * （Python 版: `docs/palindromes-in-peg/stage2_tm_galil.py`）
  *
  * Model.  Cells hold a symbol and a set of marks.  Heads move by one cell per step.
  * The input tape receives one symbol per real time unit; a head may not read a cell
  * that has not arrived yet (the online constraint).  `runOnline` drives the
  * algorithm with unbounded time per symbol and records the cost per symbol;
  * `runRealtime` gives it a fixed budget per symbol and prints 0 while it lags
  * (Galil's on-line -> real-time transformation, valid under the predictability
  * condition, which we check empirically).
  *
  * Output: y[t] = 1 iff x[0..t] is a palindrome (all initial palindromes, incl. the
  * trivial one at t = 0).
  *
  * ==Python の generator の再現==
  *
  * Python 版のアルゴリズムは `yield` を 1 基本操作ごとに置いた generator で、driver が
  * `next()` で駆動する。ここではアルゴリズムを「`Yield` コールバックを受け取る関数」に
  * し、driver（`runOnline` / `runRealtime`）は 1 回の通し実行で「何回目の yield の後に
  * 何番目の出力が現れたか」を記録して Python の driver と同じ結果を計算する（`Drivers`）。
  * 出力は同一で、スレッドも状態機械も要らない。
  */
object Stage2TmGalil {

  /** Left end marker symbol (never matches an input symbol). */
  val MARK: Char = '#'

  /** Python の `yield`：1 基本操作の区切り。 */
  type Yield = () => Unit

  /** One tape cell: an optional symbol (Python's `None` when unset) and a set of marks. */
  final class Cell[A](var symbol: Option[A], val marks: mutable.Set[String] = mutable.Set.empty[String])

  /** A tape that grows on demand; `sym(i)` is `None` for a cell never written. */
  final class Tape[A] {
    val cells: mutable.ArrayBuffer[Cell[A]] = mutable.ArrayBuffer.empty

    def ensure(i: Int): Unit = {
      while (cells.size <= i) { cells += new Cell[A](None) }
    }

    def sym(i: Int): Option[A] = { ensure(i); cells(i).symbol }

    def set(i: Int, s: A): Unit = { ensure(i); cells(i).symbol = Some(s) }

    def marks(i: Int): mutable.Set[String] = { ensure(i); cells(i).marks }
  }

  /** What the drivers observe: the output list and the elementary step count. */
  trait Costed {
    def out: mutable.ArrayBuffer[Int]
    def steps: Int
  }

  /** One input tape plus work tapes.  `avail` = number of input symbols that have
    * arrived (the online constraint).  `steps` counts elementary operations.
    */
  final class Machine(val x: String) extends Costed {
    val inp: Tape[Char] = new Tape[Char]
    inp.set(0, MARK) // place 0 = left end marker
    var avail: Int = 0
    var steps: Int = 0
    val out: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

    // --- input feeding -------------------------------------------------------

    /** Make the next input symbol available (place = index+1). */
    def feed(): Unit = {
      if (avail < x.length) {
        inp.set(avail + 1, x.charAt(avail))
        avail += 1
      }
    }

    def readInput(place: Int): Char = {
      assert(place <= avail, s"online violation: place $place not yet available")
      inp.sym(place).getOrElse(throw new NoSuchElementException(s"place $place is empty"))
    }

    def tick(): Unit = { steps += 1 }
  }

  type Algorithm = (Machine, Yield) => Unit

  // ---------------------------------------------------------------------------- KMP on tapes

  /** All borders of the palindrome at input places [s, k] (length n = k-s+1),
    * as a list of lengths in decreasing order.  Reads the window backwards (a
    * palindrome read backwards is itself), builds the failure table on a work tape,
    * then follows the failure chain from state n.  Linear number of steps.
    * Yields once per elementary operation.
    */
  def kmpBordersOfPalindrome(m: Machine, k: Int, s: Int, yld: Yield): Vector[Int] = {
    val n = k - s + 1
    val fail = new Tape[Int] // cell j holds fail(j) for j = 1..n
    fail.set(1, 0); m.tick(); yld()
    var pi = 0
    for (j <- 2 to n) {
      val cj = m.readInput(k - j + 1); m.tick(); yld()
      while (pi > 0 && m.readInput(k - pi) != cj) {
        m.tick(); yld()
        pi = fail.sym(pi).get; m.tick(); yld()
      }
      m.tick(); yld()
      if (m.readInput(k - pi) == cj) { pi += 1 }
      fail.set(j, pi); m.tick(); yld()
    }
    val lengths = mutable.ArrayBuffer.empty[Int]
    var ell = fail.sym(n).get; m.tick(); yld()
    while (ell > 0) {
      lengths += ell
      ell = fail.sym(ell).get; m.tick(); yld()
    }
    lengths.toVector
  }

  // ---------------------------------------------------------------------------- the algorithm

  /** Online algorithm: match outwards from a tentative centre; on mismatch, find the
    * longest palindromic suffix that extends with the new symbol by KMP (this is the
    * nonchain `move` applied always; the chain case comes in stage 3).
    * Places: input symbol i (0-based) sits at place i+1; place 0 is the marker.
    * Active palindrome = input places [L, R]; it is a palindrome at all times.
    */
  def galilNonchainOnly(m: Machine, yld: Yield): Unit = {
    var left = 1 // first symbol: trivial palindrome
    var right = 1
    m.feed(); m.tick(); yld()
    m.out += 1 // x[0..0] is a palindrome
    while (m.avail < m.x.length) {
      m.feed()
      val c = m.readInput(right + 1); m.tick(); yld()
      // extension test: symbol left of L must equal c
      val before = m.readInput(left - 1); m.tick(); yld()
      if (before == c && before != MARK) {
        left -= 1
        right += 1
      } else {
        // mismatch: borders of the palindrome [L, R], longest first
        val lengths = kmpBordersOfPalindrome(m, right, left, yld)
        var newL: Option[Int] = None
        val it = lengths.iterator
        while (newL.isEmpty && it.hasNext) {
          val ell = it.next()
          val st = right - ell + 1
          m.tick(); yld()
          if (m.readInput(st - 1) == c) { newL = Some(st - 1) }
        }
        if (newL.isEmpty) {
          // empty border: "cc" if x[R] == c else "c"
          newL = Some(if (m.readInput(right) == c) right else right + 1)
          m.tick(); yld()
        }
        left = newL.get
        right += 1
      }
      m.out += (if (left == 1) 1 else 0)
    }
  }

  // ---------------------------------------------------------------------------- drivers

  /** Python の generator driver（`run_online` / `run_realtime`）を 1 パスで再現する。 */
  object Drivers {

    /** `run_online`: the steps spent per output symbol, measured at the yield after
      * which the output first appears.  `multi = false` records at most one cost per
      * yield (stage 2's `if`), `true` records every pending one (stage 3's `while`).
      */
    def runOnline(m: Costed, body: Yield => Unit, multi: Boolean): (Vector[Int], Vector[Int]) = {
      val cost = mutable.ArrayBuffer.empty[Int]
      var last = 0
      def record(): Unit = { cost += m.steps - last; last = m.steps }
      body { () =>
        if (multi) {
          while (m.out.size > cost.size) { record() }
        } else if (m.out.size > cost.size) {
          record()
        }
      }
      while (cost.size < m.out.size) { record() }
      (m.out.toVector, cost.toVector)
    }

    /** `run_realtime`: feed one symbol per real step; allow `budget` elementary steps
      * (yields) per real step; report the algorithm's output when it is caught up, else 0.
      * The body is run to completion once; `appearedAt(i)` = number of yields consumed
      * before output i became visible to the driver.
      */
    def runRealtime(m: Costed, body: Yield => Unit, budget: Int, n: Int): Vector[Int] = {
      val appearedAt = mutable.ArrayBuffer.empty[Int]
      var yields = 0
      body { () =>
        yields += 1
        while (appearedAt.size < m.out.size) { appearedAt += yields }
      }
      val totalYields = yields
      while (appearedAt.size < m.out.size) { appearedAt += totalYields + 1 } // visible after StopIteration
      val outs = mutable.ArrayBuffer.empty[Int]
      var consumed = 0
      var visible = 0
      var done = false
      for (t <- 0 until n) {
        var spent = 0
        while (!done && spent < budget && visible <= t) {
          if (consumed < totalYields) {
            consumed += 1
            spent += 1
          } else {
            done = true
            visible = m.out.size
          }
          while (visible < appearedAt.size && appearedAt(visible) <= consumed) { visible += 1 }
        }
        outs += (if (visible > t) m.out(t) else 0)
      }
      outs.toVector
    }
  }

  def runOnline(x: String, algo: Algorithm = galilNonchainOnly): (Vector[Int], Vector[Int]) = {
    val m = new Machine(x)
    Drivers.runOnline(m, yld => algo(m, yld), multi = false)
  }

  /** Feed one symbol per real step; allow `budget` elementary steps per real step;
    * print the algorithm's output when it is caught up, else 0.
    */
  def runRealtime(x: String, budget: Int, algo: Algorithm = galilNonchainOnly): Vector[Int] = {
    val m = new Machine(x)
    Drivers.runRealtime(m, yld => algo(m, yld), budget, x.length)
  }

  def brute(x: String): Vector[Int] = {
    (0 until x.length).map { t =>
      val prefix = x.substring(0, t + 1)
      if (prefix == prefix.reverse) 1 else 0
    }.toVector
  }

  /** The `__main__` demo of stage2_tm_galil.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    var bad = 0
    var tot = 0
    var worst = 0
    for (n <- 1 until 13; x <- product("ab", n)) {
      tot += 1
      val (got, cost) = runOnline(x)
      if (got != brute(x)) {
        bad += 1
        if (bad <= 3) {
          out.append(s"BAD online $x ${PyFormat.intListRepr(got)} ${PyFormat.intListRepr(brute(x))}\n")
        }
      }
      worst = math.max(worst, cost.max)
    }
    out.append(s"online: strings $tot bad $bad worst cost/symbol $worst\n")
    for (x <- Vector("ab" * 100, "a" * 200, "aab" * 60, "abba" * 50)) {
      val (_, cost) = runOnline(x)
      out.append(s"  ${x.take(6)}...: total steps/n = ${PyFormat.fixed(cost.sum.toDouble / x.length, 1)}, max step ${cost.max}\n")
    }
    // real-time with budget: correct only where the predictability condition holds
    for (budget <- Vector(8, 16, 32)) {
      bad = 0
      for (n <- 1 until 13; x <- product("ab", n)) {
        if (runRealtime(x, budget) != brute(x)) { bad += 1 }
      }
      out.append(s"realtime budget $budget: mismatching strings $bad/$tot\n")
    }
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
