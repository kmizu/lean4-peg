package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import CompactScaffoldPeg.compact
import TempDir.withTempDir

/** Inlining must preserve the recognized language and match the Python output (port of `test_compact_scaffold_peg.py`). */
class CompactScaffoldPegSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  private def write(path: Path, text: String): Unit = Files.write(path, text.getBytes(StandardCharsets.UTF_8))

  private def readText(path: Path): String = new String(Files.readAllBytes(path), StandardCharsets.UTF_8)

  private def words(limit: Int): Vector[String] = Words.upTo("ab", limit).toVector

  /** Run the Python script on the same source and check output bytes and statistics agree. */
  private def assertSameAsPython(before: Path, after: Path, shortNames: Boolean, inlinePrivate: Boolean, stats: CompactScaffoldPeg.CompactStats): Unit = {
    val pythonAfter = after.resolveSibling(after.getFileName.toString + ".py")
    val flags = (if (shortNames) { Seq("--short-names") } else { Nil }) ++ (if (inlinePrivate) { Seq("--inline-private") } else { Nil })
    val printed = PyDiff.python(("compact_scaffold_peg.py" +: before.toString +: pythonAfter.toString +: flags)*)
    assertEquals(readText(after), readText(pythonAfter), flags)
    assertEquals(stats.toJson + "\n", printed, flags)
  }

  test("private branches keep ordered choice and predicates") {
    val source =
      """S = E_0 !.;
        |E_0 = E_1 / E_2;
        |E_1 = E_3 E_4;
        |E_2 = E_5 E_6;
        |E_3 = &"a";
        |E_4 = "ab" / "a";
        |E_5 = !E_3;
        |E_6 = "b" / "E_999";
        |E_7 = "unused";
        |""".stripMargin
    withTempDir("pal-compact") { folder =>
      val before = folder.resolve("before.peg")
      val after = folder.resolve("after.peg")
      write(before, source)
      val stats = compact(before, after)
      val output = readText(after)
      assertEquals(stats.fused, 1L)
      assertEquals(stats.afterRules, 5L)
      assertSameAsPython(before, after, false, false, stats)
      val a = new Grammar(source)
      val b = new Grammar(output)
      for (word <- words(5) ++ Seq("E_999", "unused")) {
        assertEquals(a.accepts(word), b.accepts(word), word)
      }
      val shortStats = compact(before, after, shortNames = true)
      assertSameAsPython(before, after, true, false, shortStats)
      val shorter = new Grammar(readText(after))
      for (word <- words(5) ++ Seq("E_999", "unused")) {
        assertEquals(a.accepts(word), shorter.accepts(word), word)
      }
      val inlinedStats = compact(before, after, shortNames = true, inlinePrivate = true)
      assert(inlinedStats.afterRules < 5L)
      assertSameAsPython(before, after, true, true, inlinedStats)
      val inlined = new Grammar(readText(after))
      for (word <- words(5) ++ Seq("E_999", "unused")) {
        assertEquals(a.accepts(word), inlined.accepts(word), word)
      }
    }
  }

  test("shared branch is preserved") {
    val source =
      """S = E_0 / E_1;
        |E_0 = E_1 / E_2;
        |E_1 = E_3 E_4;
        |E_2 = E_5 E_6;
        |E_3 = "a";
        |E_4 = "b";
        |E_5 = "b";
        |E_6 = "a";
        |""".stripMargin
    withTempDir("pal-compact") { folder =>
      val before = folder.resolve("before.peg")
      val after = folder.resolve("after.peg")
      write(before, source)
      val stats = compact(before, after)
      assertEquals(stats.fused, 0L)
      assertEquals(readText(after), source)
      assertSameAsPython(before, after, false, false, stats)
    }
  }

  test("deep private chains preserve recursive rule boundaries") {
    val source = "S = B_0 !.;\nB_0 = \"a\" B_0 / E_0;\n" +
      (0 until 1000).map(n => s"E_$n = E_${n + 1};\n").mkString +
      "E_1000 = \"b\" / \"\";\n"
    withTempDir("pal-compact") { folder =>
      val before = folder.resolve("before.peg")
      val after = folder.resolve("after.peg")
      write(before, source)
      val stats = compact(before, after, inlinePrivate = true)
      assert(stats.afterRules < 100L)
      assert(stats.afterRules > 2L)
      assertSameAsPython(before, after, false, true, stats)
      val grammar = new Grammar(readText(after))
      for (word <- Seq("", "a", "aaaa", "b", "aaab", "ba", "abb", "c")) {
        val expected = word.reverse.dropWhile(_ == 'b').reverse.dropWhile(_ == 'a').reverse.dropWhile(_ == 'a').isEmpty &&
          word.count(_ == 'b') <= 1
        assertEquals(grammar.accepts(word), expected, word)
      }
    }
  }

  test("inlining keeps sequence scope under prefix and repetition") {
    for (operator <- Seq("!", "&", "repeat"); alias <- Seq(false, true)) {
      val body = if (operator == "repeat") { "E_0* !." } else { operator + "E_0 .* !." }
      val source = if (alias) {
        s"S = $body;\nE_0 = E_1;\nE_1 = \"a\" \"b\";\n"
      } else {
        s"S = $body;\nE_0 = \"a\" \"b\";\n"
      }
      withTempDir("pal-compact") { folder =>
        val before = folder.resolve("before.peg")
        val after = folder.resolve("after.peg")
        write(before, source)
        val stats = compact(before, after, inlinePrivate = true)
        assertSameAsPython(before, after, false, true, stats)
        val original = new Grammar(source)
        val inlined = new Grammar(readText(after))
        for (word <- words(5)) {
          assertEquals(original.accepts(word), inlined.accepts(word), (operator, word))
        }
      }
    }
  }

  test("generated/midpoint.peg is rejected exactly like the Python script (non-scaffold wrapper rules)") {
    val source = PyDiff.pyDir.resolve("generated/midpoint.peg")
    withTempDir("pal-compact") { folder =>
      val error = intercept[IllegalArgumentException] { compact(source, folder.resolve("after.peg")) }
      assertEquals(error.getMessage, "expected a scaffold-generated rule name")
      val python = intercept[IllegalStateException] {
        PyDiff.python("compact_scaffold_peg.py", source.toString, folder.resolve("after.py.peg").toString)
      }
      assert(python.getMessage.contains("ValueError: expected a scaffold-generated rule name"))
    }
  }

  /** `generated/midpoint.peg` without its H/HalfCeil/HalfFloor wrapper, S rewired to the HalfCeil pointer rule. */
  private def midpointScaffoldRules(): String = {
    val lines = PyDiff.readGolden("generated/midpoint.peg").linesIterator.toVector
    val halfCeil = "HalfCeil = !\\. / (P_[0-9]+);".r
    val pointer = lines.collectFirst { case halfCeil(name) => name }.getOrElse(fail("HalfCeil rule missing"))
    (s"S = $pointer (\"a\" / \"b\")* !.;" +: lines.slice(1, lines.length - 3)).mkString("", "\n", "\n")
  }

  test("the midpoint grammars compact byte-identically to the Python script under every flag") {
    withTempDir("pal-compact") { folder =>
      val projected = folder.resolve("midpoint-projected.peg")
      write(projected, midpointScaffoldRules())
      val full = folder.resolve("midpoint-full.peg")
      write(full, MidpointPeg.build()._2.compile())
      for (source <- Seq(projected, full); shortNames <- Seq(false, true); inlinePrivate <- Seq(false, true)) {
        val after = folder.resolve(s"${source.getFileName}-$shortNames-$inlinePrivate.out")
        val stats = compact(source, after, shortNames = shortNames, inlinePrivate = inlinePrivate)
        assert(stats.beforeRules > 9000L, stats)
        assertSameAsPython(source, after, shortNames, inlinePrivate, stats)
        assert(new Grammar(readText(after)).accepts("ab"))
      }
    }
  }

  test("the command line accepts the Python script's arguments") {
    withTempDir("pal-compact") { folder =>
      val before = folder.resolve("before.peg")
      val after = folder.resolve("after.peg")
      write(before, "S = E_0 !.;\nE_0 = \"a\";\n")
      val printed = TestUtil.captureStdout {
        CompactScaffoldPeg.main(Array("--inline-private", before.toString, after.toString))
      }
      assertEquals(readText(after), "S = \"a\" !.;\n")
      assertEquals(printed, compact(before, folder.resolve("again.peg"), inlinePrivate = true).toJson + "\n")
      intercept[IllegalArgumentException] { compact(before, before) }
    }
  }
}
