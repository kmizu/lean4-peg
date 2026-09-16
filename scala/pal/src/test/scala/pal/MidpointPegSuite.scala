package pal

import java.nio.charset.StandardCharsets
import java.nio.file.Files

import MidpointPeg.{build, grammar}
import TempDir.withTempDir

/** Check exact returned positions, not just acceptance of a suffix consumer (port of `test_midpoint_peg.py`). */
class MidpointPegSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  test("FIFO focus names exact middle node through rotations") {
    val (circuit, machine) = build()
    val nodes = scala.collection.mutable.ArrayBuffer(machine.initialNode())
    val fault = circuit.labelIds(("circuit.fault", 0))
    for (n <- 1 to 1024) {
      val node = machine.step(nodes.last, "ab".charAt(n % 2)).get
      nodes += node
      assert(node.pointers("half").exists(_ eq nodes(n / 2)), n)
      assert(node.pointers("upper_half").exists(_ eq nodes((n + 1) / 2)), n)
      assert(!node.labels(fault), n)
    }
  }

  test("emitted PEG returns half of arbitrary binary suffixes") {
    val source = grammar()
    val midpoint = new Grammar(source, start = "H")
    val lower = new Grammar(source, start = "HalfFloor")
    for (word <- Words.upTo("ab", 6)) {
      val n = word.length
      assertEquals(midpoint.parsePrefix(word), Some((n + 1) / 2), word)
      assertEquals(lower.parsePrefix(word), Some(n / 2), word)
    }
    // Odd lengths and queue/power boundaries are essential; power-of-two
    // palindrome grammars do not establish this midpoint contract.
    for (n <- Seq(15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257)) {
      val word = ("abbaba" * (n / 6 + 1)).substring(0, n)
      assertEquals(midpoint.parsePrefix(word, compact = true), Some((n + 1) / 2), n)
      assertEquals(lower.parsePrefix(word, compact = true), Some(n / 2), n)
    }
    val withPrefix = new Grammar(source + "\nProbe = \"ab\" H;\n", start = "Probe")
    for (n <- 0 until 8) {
      assertEquals(withPrefix.parsePrefix("ab" + "a" * n), Some(2 + (n + 1) / 2))
    }
    assert(new Grammar(source).accepts("ab")) // S is deliberately not PAL.
  }

  test("the grammar regenerates generated/midpoint.peg byte for byte") {
    assertEquals(grammar(), PyDiff.readGolden("generated/midpoint.peg"))
  }

  test("main writes the grammar and prints the same summary as the Python script") {
    withTempDir("pal-midpoint") { directory =>
      val scalaTarget = directory.resolve("scala.peg")
      val pythonTarget = directory.resolve("python.peg")
      val printed = TestUtil.captureStdout { MidpointPeg.main(Array(scalaTarget.toString)) }
      val expected = PyDiff.python("midpoint_peg.py", pythonTarget.toString)
      assertEquals(printed.replace(scalaTarget.toString, pythonTarget.toString), expected)
      assertEquals(new String(Files.readAllBytes(scalaTarget), StandardCharsets.UTF_8),
                   new String(Files.readAllBytes(pythonTarget), StandardCharsets.UTF_8))
    }
  }
}
