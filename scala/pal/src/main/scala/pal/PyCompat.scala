package pal

import java.math.{BigDecimal => JBigDecimal, RoundingMode}

/** Python の `random` モジュール（MT19937）の忠実な再実装。
  *
  * `twoway.py`, `twoway_border.py`, `lps_halving.py` のデモは `random.seed(n)` で
  * 固定した乱数列を使う。Python 版と stdout をバイト一致させるため、CPython の
  * `random.seed(int)`（`init_by_array`）、`random()`（`genrand_res53`）、
  * `getrandbits`、`_randbelow_with_getrandbits`、`choice`、`randint`、`randrange`
  * をそのまま移植した。Python 側のモジュールに対応しない補助ファイル。
  */
final class PyRandom(seed: Long) {
  private val N = 624
  private val M = 397
  private val mt = new Array[Int](N)
  private var index = N

  seedFromInt(seed)

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

  /** CPython `random.seed(int)`: 絶対値を 32 ビットの語に分けて `init_by_array`。 */
  private def seedFromInt(value: Long): Unit = {
    val abs = math.abs(value)
    val key =
      if (abs == 0L) Array(0)
      else {
        var rest = abs
        val words = scala.collection.mutable.ArrayBuffer.empty[Int]
        while (rest != 0L) {
          words += (rest & 0xffffffffL).toInt
          rest >>>= 32
        }
        words.toArray
      }
    initByArray(key)
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
      if (i >= N) { mt(0) = mt(N - 1); i = 1 }
      if (j >= key.length) { j = 0 }
      k -= 1
    }
    k = N - 1
    while (k > 0) {
      val prev = mt(i - 1)
      mt(i) = (mt(i) ^ ((prev ^ (prev >>> 30)) * 1566083941)) - i
      i += 1
      if (i >= N) { mt(0) = mt(N - 1); i = 1 }
      k -= 1
    }
    mt(0) = 0x80000000
    index = N
  }

  private def twist(): Unit = {
    var kk = 0
    while (kk < N) {
      val y = (mt(kk) & 0x80000000) | (mt((kk + 1) % N) & 0x7fffffff)
      val mag = if ((y & 1) != 0) 0x9908b0df else 0
      mt(kk) = mt((kk + M) % N) ^ (y >>> 1) ^ mag
      kk += 1
    }
    index = 0
  }

  /** `genrand_uint32` を符号なし 32 ビット値として Long で返す。 */
  def nextUInt32(): Long = {
    if (index >= N) { twist() }
    var y = mt(index)
    index += 1
    y ^= (y >>> 11)
    y ^= (y << 7) & 0x9d2c5680
    y ^= (y << 15) & 0xefc60000
    y ^= (y >>> 18)
    y.toLong & 0xffffffffL
  }

  /** `random.random()`: 53 ビット精度の [0, 1)。 */
  def random(): Double = {
    val a = nextUInt32() >>> 5
    val b = nextUInt32() >>> 6
    (a * 67108864.0 + b) * (1.0 / 9007199254740992.0)
  }

  /** `random.getrandbits(k)`（k <= 32 のみ。この移植ではそれで足りる）。 */
  def getrandbits(k: Int): Long = {
    require(k >= 0 && k <= 32, s"getrandbits($k): only 0..32 bits are supported")
    if (k == 0) 0L else nextUInt32() >>> (32 - k)
  }

  /** `Random._randbelow_with_getrandbits(n)`。 */
  def randbelow(n: Int): Int = {
    require(n > 0)
    val k = 32 - Integer.numberOfLeadingZeros(n)
    var r = getrandbits(k)
    while (r >= n) { r = getrandbits(k) }
    r.toInt
  }

  /** `random.randrange(stop)`。 */
  def randrange(stop: Int): Int = randbelow(stop)

  /** `random.randint(a, b)`: a 以上 b 以下。 */
  def randint(a: Int, b: Int): Int = a + randbelow(b - a + 1)

  /** `random.choice(seq)`。 */
  def choice[A](seq: IndexedSeq[A]): A = {
    require(seq.nonEmpty, "Cannot choose from an empty sequence")
    seq(randbelow(seq.length))
  }

  /** `random.choice("ab")`: 文字列から 1 文字。 */
  def choice(chars: String): Char = chars.charAt(randbelow(chars.length))

  /** `''.join(random.choice(chars) for _ in range(n))`。 */
  def word(chars: String, n: Int): String = {
    val sb = new StringBuilder(n)
    var i = 0
    while (i < n) { sb.append(choice(chars)); i += 1 }
    sb.toString
  }
}

/** Python の文字列整形（`f'{x:.2f}'`, `repr`, `json.dumps` の float）の再現。 */
object PyFormat {

  /** `format(x, '.<digits>f')`。Python は 2 進の正確な値を丸める（同点は偶数へ）。 */
  def fixed(x: Double, digits: Int): String = {
    new JBigDecimal(x).setScale(digits, RoundingMode.HALF_EVEN).toPlainString
  }

  /** `repr(x)` / `json.dumps(x)` for a float（最短往復桁、Python の指数表記規則）。 */
  def floatRepr(x: Double): String = {
    if (x.isNaN) { return "nan" }
    if (x.isInfinite) { return if (x > 0) "inf" else "-inf" }
    if (x == 0.0) { return if (1.0 / x < 0) "-0.0" else "0.0" }
    val sign = if (x < 0) "-" else ""
    val text = java.lang.Double.toString(math.abs(x))
    val (mantissa, exponent) = text.indexOf('E') match {
      case -1 => (text, 0)
      case i  => (text.substring(0, i), text.substring(i + 1).toInt)
    }
    val dot = mantissa.indexOf('.')
    val intPart = mantissa.substring(0, dot)
    val fracPart = mantissa.substring(dot + 1)
    val raw = intPart + fracPart
    val leading = raw.indexWhere(_ != '0')
    val digits = raw.substring(leading).reverse.dropWhile(_ == '0').reverse
    val decpt = intPart.length - leading + exponent
    val body =
      if (decpt <= -4 || decpt > 16) {
        val exp = decpt - 1
        val rest = if (digits.length > 1) "." + digits.substring(1) else ""
        val expSign = if (exp < 0) "-" else "+"
        f"${digits.charAt(0)}${rest}e$expSign${math.abs(exp)}%02d"
      } else if (decpt <= 0) {
        "0." + ("0" * (-decpt)) + digits
      } else if (decpt >= digits.length) {
        digits + ("0" * (decpt - digits.length)) + ".0"
      } else {
        digits.substring(0, decpt) + "." + digits.substring(decpt)
      }
    sign + body
  }

  /** `repr(s)` for a str（引用符の選択と基本エスケープ）。 */
  def strRepr(s: String): String = {
    val quote = if (s.contains('\'') && !s.contains('"')) '"' else '\''
    val sb = new StringBuilder
    sb.append(quote)
    s.foreach { c =>
      if (c == quote || c == '\\') { sb.append('\\').append(c) }
      else if (c == '\n') { sb.append("\\n") }
      else if (c == '\r') { sb.append("\\r") }
      else if (c == '\t') { sb.append("\\t") }
      else if (c < 0x20 || c == 0x7f) { sb.append(f"\\x${c.toInt}%02x") }
      else { sb.append(c) }
    }
    sb.append(quote)
    sb.toString
  }

  /** `repr(b)` for bytes given as a Latin-1 string（1 文字 = 1 バイト）。 */
  def bytesRepr(s: String): String = {
    val quote = if (s.contains('\'') && !s.contains('"')) '"' else '\''
    val sb = new StringBuilder
    sb.append('b').append(quote)
    s.foreach { c =>
      if (c == quote || c == '\\') { sb.append('\\').append(c) }
      else if (c == '\n') { sb.append("\\n") }
      else if (c == '\r') { sb.append("\\r") }
      else if (c == '\t') { sb.append("\\t") }
      else if (c < 0x20 || c >= 0x7f) { sb.append(f"\\x${c.toInt}%02x") }
      else { sb.append(c) }
    }
    sb.append(quote)
    sb.toString
  }

  /** `repr(list)` given the reprs of the elements. */
  def listRepr(items: Seq[String]): String = items.mkString("[", ", ", "]")

  /** `repr(list_of_int)`。 */
  def intListRepr(items: Seq[Int]): String = listRepr(items.map(_.toString))

  /** `json.dumps(s)` for a str（`ensure_ascii=False`）。 */
  def jsonString(s: String): String = {
    val sb = new StringBuilder
    sb.append('"')
    s.foreach {
      case '"'  => sb.append("\\\"")
      case '\\' => sb.append("\\\\")
      case '\n' => sb.append("\\n")
      case '\r' => sb.append("\\r")
      case '\t' => sb.append("\\t")
      case '\b' => sb.append("\\b")
      case '\f' => sb.append("\\f")
      case c if c < 0x20 => sb.append(f"\\u${c.toInt}%04x")
      case c => sb.append(c)
    }
    sb.append('"')
    sb.toString
  }
}
