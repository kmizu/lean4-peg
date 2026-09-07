package pal

import scala.collection.mutable

import Twoway.product

/** Verified algorithmic core for an explicit plain PEG for PAL (work in progress).
  * （Python 版: `docs/palindromes-in-peg/online_manacher.py`）
  *
  * Online Manacher over positions. Reading x left to right (this is the SCA direction; the
  * PEG reads reverse(x)), it maintains the longest palindromic suffix [s, k] of x[0..k] with
  * centre code C = s + k (code 2p = single position p, code 2p+1 = between p and p+1) and a
  * table LE of finalized left ends.
  *
  * Invariant that makes this a pointer-machine algorithm: every centre code < C is already
  * recorded, and codes are recorded in strictly increasing order, each exactly once.  So the
  * scan performed at a mismatch is a walk backwards along the chain of records, one hop per
  * step — exactly what a scaffolding automaton (hence a PEG memo table) can do.
  *
  * What is NOT yet pointer-machine friendly, and is the remaining work:
  *   - the comparison  LE[mc] <= s
  *   - the mirror arithmetic  LE[cc] = C - mc + LE[mc]  and  s' = k + 2s - mc
  * All three are reflections about the active centre C; a Turing-machine tape realizes them
  * by head movement (Galil 1978), a scaffold has to realize them with delayed lockstep walks.
  *
  * Checked against brute force on all binary strings up to length 14.
  */
object OnlineManacher {

  /** Result of one online run: the LPS start per prefix, the scan hops per step (one
    * entry per extension/mismatch step, i.e. `n - 1` of them), and the recording order.
    */
  final case class Trace(starts: Vector[Int], hops: Vector[Int], order: Vector[Int])

  def bruteLpsStart(x: String, k: Int): Int = {
    (0 to k).find(s => x.substring(s, k + 1) == x.substring(s, k + 1).reverse).get
  }

  def online(x: String): Trace = {
    val n = x.length
    val le = mutable.Map(-1 -> 0) // code -1: the empty palindrome left of position 0
    var centre = 0
    var s = 0
    val order = mutable.ArrayBuffer.empty[Int] // recording order of codes
    val starts = mutable.ArrayBuffer(0)
    val hops = mutable.ArrayBuffer.empty[Int]
    for (k1 <- 1 until n) { // k1 = index of the new character, k = k1 - 1
      val k = k1 - 1
      val c = x.charAt(k1)
      var h = 0
      if (s >= 1 && x.charAt(s - 1) == c) { // the active palindrome extends
        s -= 1
        hops += h
        starts += s
      } else {
        le(centre) = s // finalize the active centre
        order += centre
        var mc = centre - 1 // scan mirror centres, nearest first
        var scanning = true
        while (scanning) {
          h += 1
          val left = le(mc)
          val cc = 2 * centre - mc // mirror of mc about C
          if (left > s) { // strictly inside: the mirror is final too
            le(cc) = centre - mc + left
            order += cc
            mc -= 1
          } else {
            val sp = k + 2 * s - mc // candidate suffix palindrome [sp, k]
            if (sp >= 1 && x.charAt(sp - 1) == c) { // it extends with the new character
              centre = cc
              s = sp - 1
              scanning = false
            } else {
              le(cc) = sp // finalized
              order += cc
              if (mc == 2 * s - 1) { // that was the empty suffix: fall back to "c"
                centre = 2 * k1
                s = k1
                scanning = false
              } else {
                mc -= 1
              }
            }
          }
        }
        hops += h
        starts += s
      }
    }
    Trace(starts.toVector, hops.toVector, order.toVector)
  }

  /** The `__main__` demo of online_manacher.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    var bad = 0
    var total = 0
    var worst = 0
    for (n <- 1 until 15; x <- product("ab", n)) {
      total += 1
      val Trace(starts, hops, order) = online(x)
      val want = (0 until n).map(k => bruteLpsStart(x, k)).toVector
      val ok = starts == want && order == order.sorted && order.size == order.distinct.size
      if (!ok) {
        bad += 1
        if (bad <= 3) {
          out.append(s"BAD $x ${PyFormat.intListRepr(starts)} ${PyFormat.intListRepr(want)} ${PyFormat.intListRepr(order)}\n")
        }
      }
      worst = math.max(worst, if (hops.nonEmpty) hops.max else 0)
    }
    out.append(s"strings $total  bad $bad  max scan hops in one step $worst\n")
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
