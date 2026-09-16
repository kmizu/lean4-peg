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

  test("full fixed-arrival generator: expanded PEG matches Python byte for byte") {
    inDirectory { directory =>
      val scalaOutput = directory.resolve("scala.expanded.peg")
      val pythonOutput = directory.resolve("python.expanded.peg")
      val outputs = GenerateGalilPeg.generate(GenerateGalilPeg.Options(scalaOutput, quantum = 1, matchDelay = 2,
        budget = 2, rawInstructions = true, omitInvariantMonitors = true, expandedOnly = true), _ => ())
      assertEquals(outputs.size, 1)
      PyDiff.python("generate_galil_peg.py", pythonOutput.toString, "--quantum", "1", "--match-delay", "2",
        "--budget", "2", "--raw-instructions", "--omit-invariant-monitors", "--expanded-only")
      // Stream both 50 MB artifacts: this checks every byte, not only lengths or digests.
      assertEquals(Files.mismatch(scalaOutput, pythonOutput), -1L, scalaOutput.getFileName.toString)
    }
  }

  test("generator inverse emitter matches unchanged Python on a bounded scaffold artifact") {
    inDirectory { directory =>
      val (_, _, machine) = TestScaffoldCircuitProgram.fixture()
      val expanded = directory.resolve("bounded.expanded.peg")
      val scalaOutput = directory.resolve("scala.peg")
      val pythonOutput = directory.resolve("python.peg")
      GenerateGalilPeg.emitExpanded(machine, expanded)
      val emitted = GenerateGalilPeg.emitInverse(expanded, scalaOutput, budget = 2)
      val scalaSource = Files.readString(scalaOutput, UTF_8)
      assertEquals(emitted.path, scalaOutput)
      assertEquals(emitted.rules, scalaSource.linesIterator.size.toLong)
      assertEquals(emitted.bytes, Files.size(scalaOutput))
      // Raise only the test process's recursion resource limit: the unchanged
      // Python oracle registers this AST recursively, while Scala tests likewise
      // use an explicit 512 MiB thread stack in sbt. Its script and algorithm stay unchanged.
      PyDiff.python("-c",
        "import sys; sys.setrecursionlimit(100000); from pathlib import Path; from phase_peg import inverse_repeat; " +
          "source, output = map(Path, __import__('sys').argv[1:]); output.write_text(inverse_repeat(source.read_text(), 2))",
        expanded.toString, pythonOutput.toString)
      assertEquals(Files.mismatch(scalaOutput, pythonOutput), -1L, scalaOutput.getFileName.toString)
    }
  }
}
