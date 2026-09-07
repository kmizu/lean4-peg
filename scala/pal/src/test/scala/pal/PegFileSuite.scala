package pal

import java.nio.charset.StandardCharsets
import java.nio.file.Files

import GenerateScaffoldExamples.markedPalindrome

/** Port of `test_peg_file.py`. */
class PegFileSuite extends munit.FunSuite {

  test("concrete emitted rules match without loading unvisited rules") {
    val source = markedPalindrome().compile() + "Unused = !\"\";\n"
    val directory = Files.createTempDirectory("pal-peg-file")
    val path = directory.resolve("emitted.peg")
    try {
      Files.write(path, source.getBytes(StandardCharsets.UTF_8))
      val eager = new Grammar(source)
      val lazyGrammar = new FileGrammar(path)
      try {
        assertEquals(lazyGrammar.rules.size, 0)
        for (word <- Words.upTo("ab#", 4)) {
          assertEquals(lazyGrammar.accepts(word), eager.accepts(word), word)
        }
        assert(!lazyGrammar.rules.contains("Unused"))
        assert(lazyGrammar.rules.size > 0)
        assertEquals(lazyGrammar.ruleCount, eager.rules.size)
      } finally {
        lazyGrammar.close()
      }
      // After close (unmapped), unloaded rules are refused instead of read from released memory;
      // loaded ones stay usable and close is idempotent.
      intercept[IllegalStateException] { lazyGrammar.rules("Unused") }
      assert(lazyGrammar.accepts("a#a"))
      lazyGrammar.close()
    } finally {
      Files.deleteIfExists(path)
      Files.deleteIfExists(directory)
    }
  }
}
