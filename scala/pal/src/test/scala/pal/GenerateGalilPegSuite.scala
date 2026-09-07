package pal

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

class GenerateGalilPegSuite extends munit.FunSuite {
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(900, "s")

  private def inDirectory(body: Path => Unit): Unit = {
    val parent = Path.of("target").toAbsolutePath
    Files.createDirectories(parent)
    val directory = Files.createTempDirectory(parent, "galil-generator-")
    try { body(directory) }
    finally {
      val paths = Files.walk(directory)
      try { paths.iterator().asScala.toVector.sortBy(_.getNameCount).reverse.foreach(Files.delete) }
      finally { paths.close() }
    }
  }

  test("CLI parses experimental fixed clocks, raw mode, monitors, expanded output and matches") {
    val options = GenerateGalilPeg.parseArgs(Array("candidate.peg", "--quantum", "1", "--match-delay", "2",
      "--budget", "4", "--raw-instructions", "--omit-invariant-monitors", "--expanded-only", "--match", "", "abba"))
    assertEquals(options, GenerateGalilPeg.Options(Path.of("candidate.peg"), 1, 2, 4,
      rawInstructions = true, omitInvariantMonitors = true, expandedOnly = true, matches = Some(Vector("", "abba"))))
    assertEquals(GenerateGalilPeg.parseArgs(Array("candidate.peg")), GenerateGalilPeg.Options(Path.of("candidate.peg")))
    intercept[IllegalArgumentException](GenerateGalilPeg.parseArgs(Array.empty))
    intercept[IllegalArgumentException](GenerateGalilPeg.parseArgs(Array("candidate.peg", "--quantum")))
    intercept[IllegalArgumentException](GenerateGalilPeg.parseArgs(Array("candidate.peg", "--unknown")))
  }

  test("streaming emitter writes complete UTF-8 rules and removes partial file") {
    inDirectory { directory =>
      val (_, _, machine) = TestScaffoldCircuitProgram.fixture()
      val target = directory.resolve("small.peg")
      val emitted = GenerateGalilPeg.emitExpanded(machine, target)
      val source = Files.readString(target, UTF_8)
      assertEquals(source, machine.compile())
      assertEquals(emitted.rules, source.linesIterator.size.toLong)
      assertEquals(emitted.bytes, source.getBytes(UTF_8).length.toLong)
      assert(!Files.exists(directory.resolve("small.peg.partial")))
      PyDiff.assertSameAsPython(source, "-c", "from test_scaffold_circuit_program import fixture; print(''.join(r+'\\n' for r in fixture()[2].iter_rules()), end='')")
    }
  }

  test("full fixed-arrival generator: expanded and inverse-repeated PEGs match Python byte for byte") {
    inDirectory { directory =>
      val scalaOutput = directory.resolve("scala.peg")
      val pythonOutput = directory.resolve("python.peg")
      val outputs = GenerateGalilPeg.generate(GenerateGalilPeg.Options(scalaOutput, quantum = 1, matchDelay = 2,
        budget = 2, rawInstructions = true, omitInvariantMonitors = true), _ => ())
      assertEquals(outputs.size, 2)
      PyDiff.python("generate_galil_peg.py", pythonOutput.toString, "--quantum", "1", "--match-delay", "2",
        "--budget", "2", "--raw-instructions", "--omit-invariant-monitors")
      val pairs = Vector(outputs.head.path -> directory.resolve("python.expanded.peg"), scalaOutput -> pythonOutput)
      for ((actual, expected) <- pairs) {
        // Stream both files: this checks every byte, not only lengths or digests.
        assertEquals(Files.mismatch(actual, expected), -1L, actual.getFileName.toString)
      }
    }
  }
}
