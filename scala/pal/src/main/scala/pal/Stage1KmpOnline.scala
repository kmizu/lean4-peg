package pal

import scala.collection.mutable

import Twoway.{Counter, product}

/** Stage 1: online LPS tracking where the chain of palindromic suffixes of the active
  * window [s,k] is obtained by KMP over the window (borders of a palindrome = its
  * palindromic suffixes).  Positions are ints here, but every access is one the pointer
  * model allows: reading x[p] for a p we hold, p-1 (prev), and KMP fail links.
  * We count 'work' = number of such elementary operations per input character.
  * （Python 版: `docs/palindromes-in-peg/stage1_kmp_online.py` — モジュール本体が
  * そのままデモを実行する。ここでは `demo()` がその stdout を返す。）
  */
object Stage1KmpOnline {

  def bruteLpsStart(x: String, k: Int): Int = OnlineManacher.bruteLpsStart(x, k)

  /** fail[j] for window positions j=1..m (m=k-s+1) where window char j = x[k-j+1]
    * (scanning the palindrome backwards = forwards).  fail[j] = length of the longest
    * proper border of the window prefix of length j.  Returns fail list (index 1..m).
    */
  def kmpBorders(x: String, s: Int, k: Int, work: Counter): Array[Int] = {
    val m = k - s + 1
    val fail = new Array[Int](m + 1)
    var pi = 0
    for (j <- 2 to m) {
      val cj = x.charAt(k - j + 1)
      work.bump()
      while (pi > 0 && x.charAt(k - (pi + 1) + 1) != cj) {
        pi = fail(pi)
        work.bump()
      }
      if (x.charAt(k - (pi + 1) + 1) == cj) { pi += 1 }
      fail(j) = pi
    }
    fail
  }

  /** The start of the longest palindromic suffix of every prefix of x. */
  def online(x: String, work: Counter): Vector[Int] = {
    val n = x.length
    var s = 0
    val starts = mutable.ArrayBuffer(0)
    for (k1 <- 1 until n) {
      val c = x.charAt(k1)
      val k = k1 - 1
      if (s >= 1 && x.charAt(s - 1) == c) {
        s -= 1
        work.bump()
        starts += s
      } else {
        // mismatch: chain of palindromic suffixes of [s,k] = border chain
        val fail = kmpBorders(x, s, k, work)
        val m = k - s + 1
        var ell = fail(m) // longest proper border length
        var newS: Option[Int] = None
        while (newS.isEmpty && ell > 0) {
          val st = k - ell + 1 // start of that suffix palindrome
          work.bump()
          if (st >= 1 && x.charAt(st - 1) == c) {
            newS = Some(st - 1)
          } else {
            ell = fail(ell)
          }
        }
        // empty border: "cc" or "c"
        s = newS.getOrElse(if (x.charAt(k) == c) k else k1)
        starts += s
      }
    }
    starts.toVector
  }

  /** The module-level script of stage1_kmp_online.py, as the text it prints. */
  def demo(): String = {
    val out = new StringBuilder
    var bad = 0
    var tot = 0
    var worst = 0.0
    for (n <- 1 until 15; x <- product("ab", n)) {
      tot += 1
      val work = new Counter
      val starts = online(x, work)
      val want = (0 until n).map(k => bruteLpsStart(x, k)).toVector
      if (starts != want) {
        bad += 1
        if (bad <= 3) {
          out.append(s"BAD $x ${PyFormat.intListRepr(starts)} ${PyFormat.intListRepr(want)}\n")
        }
      }
      worst = math.max(worst, work.value.toDouble / n)
    }
    out.append(s"strings $tot bad $bad  worst work/n ${PyFormat.fixed(worst, 1)}\n")
    // periodic stress
    for (m <- Vector(50, 100, 200)) {
      val x = "ab" * m
      val work = new Counter
      online(x, work)
      out.append(s"(ab)^$m: work/n = ${PyFormat.fixed(work.value.toDouble / x.length, 1)}\n")
    }
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(demo())
  }
}
