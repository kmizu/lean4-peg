package pal

/** `itertools.product` over an alphabet, in Python's lexicographic order. */
object PyItertools {

  /** `["".join(w) for w in itertools.product(alphabet, repeat=size)]`. */
  def words(alphabet: String, size: Int): Vector[String] = {
    (0 until size).foldLeft(Vector(""))((prefixes, _) => prefixes.flatMap(prefix => alphabet.map(prefix + _)))
  }

  /** All words of length `0 until sizes` (`for n in range(sizes)`). */
  def wordsBelow(alphabet: String, sizes: Int): Vector[String] = (0 until sizes).toVector.flatMap(words(alphabet, _))
}

class PyItertoolsSuite extends munit.FunSuite {

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
