package pal

/** Test helper standing in for Python's `itertools.product(alphabet, repeat=n)`. */
object Words {

  /** Every word of exactly `repeat` characters over `alphabet`, in lexicographic (product) order. */
  def product(alphabet: String, repeat: Int): Iterator[String] = {
    if (repeat == 0) {
      Iterator.single("")
    } else {
      product(alphabet, repeat - 1).flatMap(prefix => alphabet.iterator.map(c => prefix + c))
    }
  }

  /** Every word of length 0 to `limit` inclusive (Python `for n in range(limit + 1)`). */
  def upTo(alphabet: String, limit: Int): Iterator[String] = {
    (0 to limit).iterator.flatMap(n => product(alphabet, n))
  }
}
