package pal

/** CPython's `random.Random(seed)` for integer seeds: MT19937 seeded with
  * `init_by_array`, `getrandbits`, `_randbelow_with_getrandbits`, `randrange`
  * and `choice`. Test samples drawn with it are identical to the Python tests'.
  */
final class PyRandom(seed: Long) {
  private val N = 624
  private val mt = new Array[Long](N)
  private var index = N

  private def initGenrand(s: Long): Unit = {
    mt(0) = s & 0xffffffffL
    (1 until N).foreach { i =>
      mt(i) = (1812433253L * (mt(i - 1) ^ (mt(i - 1) >>> 30)) + i) & 0xffffffffL
    }
  }

  private def initByArray(key: Array[Long]): Unit = {
    initGenrand(19650218L)
    var i = 1
    var j = 0
    (0 until math.max(N, key.length)).foreach { _ =>
      mt(i) = ((mt(i) ^ ((mt(i - 1) ^ (mt(i - 1) >>> 30)) * 1664525L)) + key(j) + j) & 0xffffffffL
      i += 1
      j += 1
      if (i >= N) {
        mt(0) = mt(N - 1)
        i = 1
      }
      if (j >= key.length) {
        j = 0
      }
    }
    (0 until N - 1).foreach { _ =>
      mt(i) = ((mt(i) ^ ((mt(i - 1) ^ (mt(i - 1) >>> 30)) * 1566083941L)) - i) & 0xffffffffL
      i += 1
      if (i >= N) {
        mt(0) = mt(N - 1)
        i = 1
      }
    }
    mt(0) = 0x80000000L
  }

  {
    // CPython splits abs(seed) into 32-bit words, least significant first.
    val magnitude = math.abs(seed)
    val key = if (magnitude >>> 32 == 0) Array(magnitude) else Array(magnitude & 0xffffffffL, magnitude >>> 32)
    initByArray(key)
  }

  private def genrandUint32(): Long = {
    if (index >= N) {
      (0 until N).foreach { kk =>
        val y = (mt(kk) & 0x80000000L) | (mt((kk + 1) % N) & 0x7fffffffL)
        mt(kk) = mt((kk + 397) % N) ^ (y >>> 1) ^ (if ((y & 1L) != 0) 0x9908b0dfL else 0L)
      }
      index = 0
    }
    var y = mt(index)
    index += 1
    y ^= y >>> 11
    y ^= (y << 7) & 0x9d2c5680L
    y ^= (y << 15) & 0xefc60000L
    y ^= y >>> 18
    y & 0xffffffffL
  }

  /** `getrandbits(k)` for `0 <= k <= 32`. */
  def getrandbits(k: Int): Long = {
    require(0 <= k && k <= 32, "only up to 32 bits are supported")
    if (k == 0) 0L else genrandUint32() >>> (32 - k)
  }

  /** `_randbelow_with_getrandbits(n)`. */
  def randbelow(n: Int): Int = {
    val k = 32 - Integer.numberOfLeadingZeros(n)
    var r = getrandbits(k)
    while (r >= n) {
      r = getrandbits(k)
    }
    r.toInt
  }

  /** `randrange(start, stop)`. */
  def randrange(start: Int, stop: Int): Int = start + randbelow(stop - start)

  /** `choice(seq)`. */
  def choice(alphabet: String): Char = alphabet(randbelow(alphabet.length))

  /** `"".join(rng.choice(alphabet) for _ in range(size))`. */
  def word(alphabet: String, size: Int): String = {
    val builder = new StringBuilder(size)
    (0 until size).foreach(_ => builder += choice(alphabet))
    builder.result()
  }
}

/** `itertools.product` over an alphabet, in Python's lexicographic order. */
object PyItertools {

  /** `["".join(w) for w in itertools.product(alphabet, repeat=size)]`. */
  def words(alphabet: String, size: Int): Vector[String] = {
    (0 until size).foldLeft(Vector(""))((prefixes, _) => prefixes.flatMap(prefix => alphabet.map(prefix + _)))
  }

  /** All words of length `0 until sizes` (`for n in range(sizes)`). */
  def wordsBelow(alphabet: String, sizes: Int): Vector[String] = (0 until sizes).toVector.flatMap(words(alphabet, _))
}

class PyCompatSuite extends munit.FunSuite {

  test("PyRandom reproduces CPython's Random(909) randrange/choice sequence") {
    val rng = new PyRandom(909)
    val actual = (0 until 20).map(_ => rng.randrange(1, 500)).mkString(" ") + "\n" +
      (0 until 40).map(_ => rng.choice("ab#")).mkString + "\n"
    PyDiff.assertSameAsPython(actual, "-c",
      "import random\nr = random.Random(909)\nprint(' '.join(str(r.randrange(1, 500)) for _ in range(20)))\n" +
        "print(''.join(r.choice('ab#') for _ in range(40)))")
  }

  test("PyRandom matches a large seed and long draws") {
    val rng = new PyRandom(1407)
    val actual = (0 until 3000).map(_ => rng.choice("ab")).mkString + "\n"
    PyDiff.assertSameAsPython(actual, "-c",
      "import random\nr = random.Random(1407)\nprint(''.join(r.choice('ab') for _ in range(3000)))")
  }

  test("PyItertools.words follows itertools.product order") {
    assertEquals(PyItertools.words("ab", 2), Vector("aa", "ab", "ba", "bb"))
    assertEquals(PyItertools.wordsBelow("ab", 2), Vector("", "a", "b"))
  }
}
