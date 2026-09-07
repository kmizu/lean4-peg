package pal

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.util.concurrent.TimeUnit
import scala.collection.immutable.VectorMap
import scala.collection.mutable
import GenerateOnlinePeg.{Backend, Source, generate}

class GenerateOnlinePegSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  private def report(): GenerateOnlinePeg.Report = mutable.LinkedHashMap.empty[String, Any]
  private val quiet: String => Unit = _ => ()
  private def backend(signature: String = "version-one"): Backend = Backend(
    signature = () => signature,
    build = (_, _) => Source(ScaffoldEventBufferSuite.sourceFixture(), "ready", "event"),
    pack = (wrapper, service, lazyRound) => {
      assertEquals(service, GalilClock.derive(64).service)
      ScaffoldEventBuffer.packService(wrapper, 3, lazyRound)
    })

  test("wrapper checkpoint reuses exact source and rejects stale source") {
    TempDir.withTempDir("online-cache-") { directory =>
      val output = directory.resolve("result.peg")
      val cache = directory.resolve("source.sca")
      val first = report()
      generate(output, 64, first, wrapperCache = Some(cache), wrapperOnly = true, backend = backend(), progress = quiet)
      assert(Files.exists(cache))
      assert(!Files.exists(output))
      assertEquals(first("emitted"), false)
      val cached = backend().copy(build = (_, _) => throw new AssertionError("must load cache"))
      generate(output, 64, report(), wrapperCache = Some(cache), wrapperOnly = true, backend = cached, progress = quiet)
      interceptMessage[IllegalArgumentException]("FIFO artifact differs from this source; use --rebuild-wrapper or another path") {
        generate(output, 64, report(), wrapperCache = Some(cache), wrapperOnly = true,
          backend = cached.copy(signature = () => "version-two"), progress = quiet)
      }
      generate(output, 64, report(), wrapperCache = Some(cache), wrapperOnly = true, rebuildWrapper = true,
        backend = backend("version-two"), progress = quiet)
      assertEquals(ScaffoldArtifact.read(cache)._2,
        VectorMap[String, Any]("signature" -> "version-two", "quantum" -> 64, "shared_cells" -> false))
    }
  }

  test("source signature changes with Scala source bytes and rejects the stale cache") {
    TempDir.withTempDir("scala-provenance-") { directory =>
      val source = GenerateScaffoldExamples.locateDirectory(Array.empty)
        .resolve("../../scala/pal/src/main/scala/pal").normalize()
      val stream = Files.list(source)
      try { stream.forEach(path => Files.copy(path, directory.resolve(path.getFileName))) } finally { stream.close() }
      val first = GenerateOnlinePeg.sourceSignature(directory)
      val cache = directory.resolve("source.sca")
      generate(directory.resolve("unused.peg"), 64, report(), wrapperCache = Some(cache), wrapperOnly = true,
        backend = backend(first), progress = quiet)
      val target = directory.resolve("GenerateOnlinePeg.scala")
      Files.writeString(target, Files.readString(target, UTF_8) + "\n", UTF_8)
      val changed = GenerateOnlinePeg.sourceSignature(directory)
      assertNotEquals(changed, first)
      interceptMessage[IllegalArgumentException]("FIFO artifact differs from this source; use --rebuild-wrapper or another path") {
        generate(directory.resolve("unused.peg"), 64, report(), wrapperCache = Some(cache), wrapperOnly = true,
          backend = backend(changed), progress = quiet)
      }
    }
  }

  for (lazyRound <- Vector(false, true)) {
    test(s"ordinary emission and FIFO checkpoint match Python bytes, lazy=$lazyRound") {
      TempDir.withTempDir("online-emission-") { directory =>
        val output = directory.resolve("result.peg")
        val cache = directory.resolve("source.sca")
        val result = report()
        generate(output, 64, result, wrapperCache = Some(cache), lazyRound = lazyRound, backend = backend(), progress = quiet)
        assertEquals(result("emitted"), true)
        assertEquals(result("bytes"), Files.size(output))
        assertEquals(result("rules"), Files.readString(output).linesIterator.size.toLong)
        assertEquals(result("raw_input_matches"), "not run")
        assert(!Files.exists(directory.resolve("result.peg.partial")))
        val lazyArgument = if (lazyRound) { "True" } else { "False" }
        val script = s"""from contextlib import redirect_stdout
          |from io import StringIO
          |from pathlib import Path
          |from tempfile import TemporaryDirectory
          |from unittest.mock import patch
          |import generate_online_peg as g
          |from test_generate_online_peg import Ports
          |from test_scaffold_event_buffer import source_fixture
          |from scaffold_event_buffer import pack_service
          |with TemporaryDirectory() as d:
          | output = Path(d) / 'result.peg'
          | with redirect_stdout(StringIO()), patch.object(g, 'source_signature', return_value='version-one'), patch.object(g, 'build_online', return_value=(Ports(), source_fixture())), patch.object(g, 'pack_service', side_effect=lambda w, s, lazy=False: pack_service(w, 3, lazy=lazy)):
          |  g.generate(output, 64, {}, lazy_round=$lazyArgument)
          | print(output.read_text(), end='')
          |""".stripMargin
        PyDiff.assertSameAsPython(Files.readString(output, UTF_8), "-c", script)
        val grammar = new Grammar(Files.readString(output, UTF_8))
        for (word <- Words.upTo("ab", 4)) { assertEquals(grammar.accepts(word.reverse), word.isEmpty || word.last == 'a', word) }
        // Read the Scala-produced checkpoint in Python: metadata and equations
        // remain interoperable even before packing an input round.
        val cacheScript = s"""from scaffold_artifact import read
          |from pathlib import Path
          |m, metadata = read(Path(${PyFormat.jsonString(cache.toString)}))
          |assert metadata == dict(signature='version-one', quantum=64, shared_cells=False)
          |print(m.compile(), end='')
          |""".stripMargin
        PyDiff.assertSameAsPython(ScaffoldArtifact.read(cache)._1.compile(), "-c", cacheScript)
      }
    }
  }

  test("compact and indented reports preserve Python numeric and string formatting") {
    val value = VectorMap[String, Any]("seconds" -> 1.25, "stage" -> "灯里\nready", "emitted" -> false,
      "timing" -> VectorMap("quantum" -> 64, "values" -> Vector(1, 2)), "missing" -> None)
    val script = "import json\nx=dict(seconds=1.25, stage='灯里\\nready', emitted=False, timing=dict(quantum=64, values=[1,2]), missing=None)\n"
    PyDiff.assertSameAsPython(GenerateOnlinePeg.reportJson(value) + "\n", "-c", script + "print(json.dumps(x))")
    PyDiff.assertSameAsPython(GenerateOnlinePeg.reportPretty(value) + "\n", "-c", script + "print(json.dumps(x, indent=2))")
  }

  test("CLI validates resource and checkpoint options without accepting recognition budgets") {
    val options = GenerateOnlinePeg.parseArgs(Array("out.peg", "--quantum", "32", "--memory-mib", "4096", "--report", "report.json",
      "--shared-instruction-cells", "--wrapper-cache", "source.sca", "--wrapper-only", "--rebuild-wrapper", "--lazy-round"))
    assertEquals(options, GenerateOnlinePeg.Options(Path.of("out.peg"), 32, 4096, Some(Path.of("report.json")),
      true, Some(Path.of("source.sca")), true, true, true))
    for (args <- Vector(Array("out", "--memory-mib", "0"), Array("out", "--wrapper-only"), Array("out", "--quantum", "0"),
      Array("out", "--budget", "100"), Array("out", "--quantum"))) {
      intercept[IllegalArgumentException] { GenerateOnlinePeg.parseArgs(args) }
    }
  }

  test("CLI loads a compatible checkpoint and writes an indented report including elapsed time") {
    TempDir.withTempDir("online-cli-") { directory =>
      val output = directory.resolve("result.peg")
      val cache = directory.resolve("source.sca")
      val reportPath = directory.resolve("report.json")
      generate(output, 64, report(), wrapperCache = Some(cache), wrapperOnly = true,
        backend = backend(GenerateOnlinePeg.sourceSignature()), progress = quiet)
      val stdout = new java.io.ByteArrayOutputStream()
      Console.withOut(stdout) {
        GenerateOnlinePeg.main(Array(output.toString, "--wrapper-cache", cache.toString, "--wrapper-only", "--report", reportPath.toString))
      }
      val written = Files.readString(reportPath, UTF_8)
      assert(written.startsWith("{\n  \"timing\": {"))
      assert(written.contains("\"seconds\": "))
      assert(written.contains("\"peak_rss_kib\": "))
      assert(written.contains("\"emitted\": false"))
      assert(stdout.toString(UTF_8).contains("load finite FIFO artifact"))
      assert(!Files.exists(output))
    }
  }

  test("SIGTERM writes an interrupted report without replacing an existing output") {
    TempDir.withTempDir("online-sigterm-") { directory =>
      val output = directory.resolve("result.peg")
      val reportPath = directory.resolve("report.json")
      val log = directory.resolve("stdout.log")
      Files.writeString(output, "existing output\n", UTF_8)
      val java = Path.of(System.getProperty("java.home"), "bin", "java").toString
      val process = new ProcessBuilder(java, "-Xmx512m", "-cp", System.getProperty("java.class.path"),
        "pal.GenerateOnlinePeg", output.toString, "--memory-mib", "512", "--report", reportPath.toString)
        .redirectErrorStream(true).redirectOutput(log.toFile).start()
      val deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(30)
      while (process.isAlive && System.nanoTime() < deadline &&
          (!Files.exists(log) || !Files.readString(log, UTF_8).contains("online source"))) {
        Thread.sleep(25)
      }
      assert(process.isAlive, if (Files.exists(log)) { Files.readString(log, UTF_8) } else { "subprocess exited before SIGTERM" })
      process.destroy()
      assert(process.waitFor(30, TimeUnit.SECONDS), "SIGTERM subprocess did not stop")
      assertEquals(process.exitValue(), 143)
      val written = Files.readString(reportPath, UTF_8)
      assert(written.contains("\"status\": \"compilation interrupted\""))
      assert(written.contains("\"emitted\": false"))
      assert(written.contains("\"seconds\": "))
      assertEquals(Files.readString(output, UTF_8), "existing output\n")
    }
  }
}
