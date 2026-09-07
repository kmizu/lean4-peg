package pal

import PhasePeg.inverseRepeat

/** Inverse fixed-width expansion must preserve ordered PEG decisions (port of `test_phase_peg.py`). */
class PhasePegSuite extends munit.FunSuite {

  test("prefix result preserves committed choice and empty success") {
    for (compact <- Seq(false, true)) {
      val grammar = new Grammar("S = \"a\" / \"ab\";")
      assertEquals(grammar.parsePrefix("ab", compact), Some(1))
      assert(!grammar.accepts("ab", compact))
      assertEquals(grammar.parsePrefix("b", compact), None)
      assertEquals(new Grammar("S = \"\";").parsePrefix("ab", compact), Some(0))
    }
  }

  test("interpreter handles deep rules and still rejects nullable cycles") {
    assert(new Grammar("S = A !.; A = \"a\" A / \"\";").accepts("a" * 5000))
    assert(new Grammar("S = A !.; A = \"a\" A / \"\";").accepts("a" * 5000, compact = true))
    val plain = intercept[IllegalArgumentException] { new Grammar("S = S / \"\";").accepts("") }
    assert(plain.getMessage.contains("non-consuming recursion"))
    val compact = intercept[IllegalArgumentException] { new Grammar("S = S / \"\";").accepts("", compact = true) }
    assert(compact.getMessage.contains("non-consuming recursion"))
    val nullable = intercept[IllegalArgumentException] { new Grammar("S = \"\"*;").accepts("") }
    assert(nullable.getMessage.contains("nullable repetition"))
  }

  private def compare(source: String, width: Int, alphabet: String = "ab", limit: Int = 5): Unit = {
    val original = new Grammar(source)
    val transformed = new Grammar(inverseRepeat(source, width))
    for (word <- Words.upTo(alphabet, limit)) {
      val expanded = word.flatMap(c => c.toString * width)
      assertEquals(transformed.accepts(word), original.accepts(expanded), word)
      assertEquals(transformed.accepts(word, compact = true), original.accepts(expanded), word)
    }
  }

  test("default start matches interpreter even when S is not first") {
    val source = "A = \"aa\"; S = \"bb\";"
    val default = new Grammar(inverseRepeat(source, 2))
    assert(default.accepts("b"))
    assert(!default.accepts("a"))
    val selected = new Grammar(inverseRepeat(source, 2, start = "A"))
    assert(selected.accepts("a"))
    assert(!selected.accepts("b"))
    val error = intercept[IllegalArgumentException] { inverseRepeat(source, 2, start = "Missing") }
    assert(error.getMessage.contains("start"))
  }

  test("ordered choice cannot retry a different return phase") {
    val source = "S = (\"a\" / \"aa\") \"bb\" !.;"
    val transformed = new Grammar(inverseRepeat(source, 2))
    assert(!transformed.accepts("ab"))
    compare(source, 2)
  }

  test("phase crossings, predicates, repetition and recursive rules") {
    val sources = Seq(
      "S = &A A !.; A = \"a\" A \"b\" / \"\";",
      "S = !(\"aaa\") (\"a\" / \"b\")* !.;",
      "S = (\"aa\" / \"a\")* (\"bb\" / \"b\") !.;",
      "S = . A !.; A = \"a\" . / \"bb\" / \"\";",
      "S = (\"a\" / \"aa\")* !.;"
    )
    for (width <- Seq(1, 2, 3); source <- sources) {
      compare(source, width)
    }
  }

  test("repetition cannot give back a virtual character") {
    for (source <- Seq("S = \"a\"* \"aa\" !.;", "S = (\"a\" &\"a\")* \"aa\" !.;")) {
      assert(!new Grammar(inverseRepeat(source, 2)).accepts("a"))
      compare(source, 2)
    }
  }

  private def referenceChain(length: Int): String = {
    "S = R0 !.;\n" + (0 until length).map { i =>
      s"R$i = " + (if (i + 1 == length) { "\"aa\"" } else { s"R${i + 1}" }) + ";\n"
    }.mkString
  }

  test("phase worklist preserves Python bytes for delayed references and cyclic closures") {
    val cases = Vector(
      referenceChain(300) -> 2,
      "S = (\"aa\")* !.;" -> 7,
      "S = &A A !.; A = \"aa\" B / \"\"; B = A;" -> 3
    )
    for ((source, width) <- cases) {
      PyDiff.assertSameAsPython(inverseRepeat(source, width), "-c",
        "import sys\nfrom phase_peg import inverse_repeat\nprint(inverse_repeat(sys.argv[1], int(sys.argv[2])), end='')",
        source, width.toString)
    }
  }

  test("phase returns propagate through a long reference chain") {
    val transformed = new Grammar(inverseRepeat(referenceChain(8000), 2))
    assert(transformed.accepts("a"))
    for (word <- Vector("", "b", "aa", "ab")) {
      assert(!transformed.accepts(word), word)
    }
  }

  test("sparse TM with two microsteps per character") {
    // The TM compiler (symbolic_tm2peg) is outside this port; Python produces the source grammar.
    val source = PyDiff.python("-c",
      "from symbolic_tm2peg import SymbolicTM, Transition\n" +
      "tm = SymbolicTM(1, ['p', 'q', 'r', 's', 'yes'], 'p', {'yes'}, [\n" +
      "  Transition('p', 'a', {}, 'q', {0: ('x', 'S')}),\n" +
      "  Transition('q', 'a', {}, 'r', {0: (None, 'R')}),\n" +
      "  Transition('r', 'a', {}, 's', {0: (None, 'L')}),\n" +
      "  Transition('s', 'a', {0: 'x'}, 'yes', {})], 'a')\n" +
      "print(tm.compile(), end='')")
    for (width <- Seq(2, 4)) {
      val transformed = new Grammar(inverseRepeat(source, width))
      for (n <- 0 until 6) {
        assertEquals(transformed.accepts("a" * n), n * width == 4)
      }
    }
  }

  test("invalid width and non-BMP literals are rejected") {
    // Python also rejected `True` and `1.5`; those are not representable as an Int here.
    for (width <- Seq(0, -1)) {
      intercept[IllegalArgumentException] { inverseRepeat("S = \"\";", width) }
    }
    val error = intercept[IllegalArgumentException] { inverseRepeat("S = \"😀\";", 2) }
    assert(error.getMessage.contains("BMP"))
  }

  test("phase examples are byte-identical to the Python goldens and to Python itself") {
    val examples = GeneratePhaseExamples.examples(PyDiff.pyDir)
    assertEquals(examples.map(_._1), Vector("phase_preserving_move_2.peg", "phase_preserving_move_4.peg",
      "phase_ordered_choice.peg", "phase_balanced.peg", "phase_repetition.peg", "phase_greedy.peg"))
    for ((filename, output) <- examples) {
      assertEquals(output, PyDiff.readGolden(s"generated/$filename"), filename)
    }
    val summaries = examples.map { case (filename, output) => s"$filename: ${GenerateScaffoldExamples.summary(output)}\n" }.mkString
    PyDiff.assertSameAsPython(summaries, "-c",
      "from pathlib import Path\nfrom phase_peg import inverse_repeat\n" +
      "d = Path('generated'); move = (d / 'sparse_preserving_move.peg').read_text()\n" +
      "ex = {'phase_preserving_move_2.peg': (move, 2), 'phase_preserving_move_4.peg': (move, 4),\n" +
      "  'phase_ordered_choice.peg': ('S = (\"a\" / \"aa\") \"bb\" !.;', 2),\n" +
      "  'phase_balanced.peg': ('S = A !.; A = \"a\" A \"b\" / \"\";', 3),\n" +
      "  'phase_repetition.peg': ('S = \"a\"* \"bb\" !.;', 2),\n" +
      "  'phase_greedy.peg': ('S = (\"a\" &\"a\")* \"aa\" !.;', 2)}\n" +
      "for f, (s, w) in ex.items():\n" +
      "  o = inverse_repeat(s, w); print(f'{f}: {len(o.splitlines())} rules, {len(o.encode())} bytes')")
  }

  test("CompactMemo stores failures, in-progress markers and positions in both row shapes") {
    val memo = new CompactMemo(40)
    assertEquals(memo.kind, "H")
    assertEquals(memo.get(7, 3), -1)
    memo.update(7, 3, -2)
    assertEquals(memo.get(7, 3), -2)
    memo.update(7, 3, 0)
    assertEquals(memo.get(7, 3), 0)
    for (position <- 0 to 20) { memo.update(7, position, position + 1) } // exceeds the sparse threshold
    for (position <- 0 to 20) { assertEquals(memo.get(7, position), position + 1) }
    assertEquals(memo.get(7, 30), -1)
    memo.update(7, 30, -2)
    assertEquals(memo.get(7, 30), -2)
    assertEquals(new CompactMemo(70000).kind, "Q")
  }
}
