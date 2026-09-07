package pal

/** CPython の `random` モジュールの決定的サブセット（MT19937 + CPython の整数シード）。
  *
  * Python 版の `__main__` デモや `test_*.py` は `random.seed(n)` で系列を固定している。
  * Scala 版が同じ出力をバイト一致で再現するには、同じ乱数系列が必要なので、
  * `Random.seed(int)` / `random()` / `getrandbits(k)` / `randint(a, b)` / `choice(seq)` を
  * CPython 3.x (`Modules/_randommodule.c`, `Lib/random.py`) と同じ算法で実装する。
  *
  * 対応するシードは非負の `Long`（CPython は任意長整数を 32 bit ワードに分割して
  * `init_by_array` に渡す。ここでは 64 bit までを同じ分割で扱う）。
  */
final class PyRandom(initialSeed: Long) {

  private val N = 624
  private val M = 397
  private val MatrixA = 0x9908b0df
  private val UpperMask = 0x80000000
  private val LowerMask = 0x7fffffff

  private val mt = new Array[Int](N)
  private var index = N + 1

  seed(initialSeed)

  /** `random.seed(a)`（`a` は非負整数）。`abs(a)` を 32 bit ワード列（下位から）にして
    * `init_by_array` に渡す。`a == 0` はワード `[0]` 1 個。
    */
  def seed(a: Long): Unit = {
    require(a >= 0L, s"PyRandom.seed: negative seed $a not supported")
    val low = (a & 0xffffffffL).toInt
    val high = (a >>> 32).toInt
    val key = if (high == 0) { Array(low) } else { Array(low, high) }
    initByArray(key)
  }

  private def initGenrand(s: Int): Unit = {
    mt(0) = s
    var i = 1
    while (i < N) {
      val prev = mt(i - 1)
      mt(i) = 1812433253 * (prev ^ (prev >>> 30)) + i
      i += 1
    }
    index = N
  }

  private def initByArray(key: Array[Int]): Unit = {
    initGenrand(19650218)
    var i = 1
    var j = 0
    var k = math.max(N, key.length)
    while (k > 0) {
      val prev = mt(i - 1)
      mt(i) = (mt(i) ^ ((prev ^ (prev >>> 30)) * 1664525)) + key(j) + j
      i += 1
      j += 1
      if (i >= N) {
        mt(0) = mt(N - 1)
        i = 1
      }
      if (j >= key.length) {
        j = 0
      }
      k -= 1
    }
    k = N - 1
    while (k > 0) {
      val prev = mt(i - 1)
      mt(i) = (mt(i) ^ ((prev ^ (prev >>> 30)) * 1566083941)) - i
      i += 1
      if (i >= N) {
        mt(0) = mt(N - 1)
        i = 1
      }
      k -= 1
    }
    mt(0) = 0x80000000
    index = N
  }

  private def twist(): Unit = {
    var kk = 0
    while (kk < N - M) {
      val y = (mt(kk) & UpperMask) | (mt(kk + 1) & LowerMask)
      mt(kk) = mt(kk + M) ^ (y >>> 1) ^ (if ((y & 1) != 0) { MatrixA } else { 0 })
      kk += 1
    }
    while (kk < N - 1) {
      val y = (mt(kk) & UpperMask) | (mt(kk + 1) & LowerMask)
      mt(kk) = mt(kk + (M - N)) ^ (y >>> 1) ^ (if ((y & 1) != 0) { MatrixA } else { 0 })
      kk += 1
    }
    val y = (mt(N - 1) & UpperMask) | (mt(0) & LowerMask)
    mt(N - 1) = mt(M - 1) ^ (y >>> 1) ^ (if ((y & 1) != 0) { MatrixA } else { 0 })
    index = 0
  }

  /** `genrand_uint32`: 32 bit の一様乱数（0 以上 2^32 未満）を `Long` で返す。 */
  def genrandUint32(): Long = {
    if (index >= N) {
      twist()
    }
    var y = mt(index)
    index += 1
    y ^= (y >>> 11)
    y ^= (y << 7) & 0x9d2c5680
    y ^= (y << 15) & 0xefc60000
    y ^= (y >>> 18)
    y.toLong & 0xffffffffL
  }

  /** `random.random()`: 53 bit 精度の `[0.0, 1.0)`。 */
  def random(): Double = {
    val a = genrandUint32() >>> 5
    val b = genrandUint32() >>> 6
    (a * 67108864.0 + b) * (1.0 / 9007199254740992.0)
  }

  /** `random.getrandbits(k)`（`1 <= k <= 64`）。CPython と同じく 32 bit ワードを
    * 下位から詰め、最後のワードだけ上位ビットを落とす。
    */
  def getrandbits(k: Int): Long = {
    require(k >= 1 && k <= 64, s"PyRandom.getrandbits: k=$k out of range")
    if (k <= 32) {
      genrandUint32() >>> (32 - k)
    } else {
      val low = genrandUint32()
      val high = genrandUint32() >>> (64 - k)
      (high << 32) | low
    }
  }

  /** `Random._randbelow_with_getrandbits(n)`: `[0, n)` の一様整数。 */
  def randbelow(n: Int): Int = {
    require(n > 0, s"PyRandom.randbelow: n=$n must be positive")
    val k = 32 - Integer.numberOfLeadingZeros(n)
    var r = getrandbits(k)
    while (r >= n) {
      r = getrandbits(k)
    }
    r.toInt
  }

  /** `random.randint(a, b)`: `[a, b]` の一様整数。 */
  def randint(a: Int, b: Int): Int = {
    val width = b + 1 - a
    require(width > 0, s"PyRandom.randint: empty range [$a, $b]")
    a + randbelow(width)
  }

  /** `random.choice(seq)`。 */
  def choice[A](seq: IndexedSeq[A]): A = {
    seq(randbelow(seq.length))
  }

  /** `random.choice(str)`: 1 文字を `String` として返す。 */
  def choice(chars: String): String = {
    chars.charAt(randbelow(chars.length)).toString
  }
}
