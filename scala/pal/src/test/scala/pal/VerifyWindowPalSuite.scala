package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.nio.file.attribute.PosixFilePermissions

import VerifyWindowPal.*

/** （Python 版: `test_verify_window_pal.py`、全 5 ケース移植。Python は `Popen` を
  * Mock で差し替えるが、ここでは同じ報告行を吐く偽 runner スクリプトを置く。）
  */
class VerifyWindowPalSuite extends munit.FunSuite {

  private val directory = FunFixture[Path](
    setup = _ => {
      val root = Files.createTempDirectory("verify-window-pal")
      Files.writeString(root.resolve("input.peg"), "S <- !.\n")
      Files.writeString(root.resolve("run.json"), "{\"status\":\"passed\",\"checked\":999}\n")
      root
    },
    teardown = root => {
      Files.walk(root).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))
    }
  )

  private def grammarOf(root: Path): Path = root.resolve("input.peg")
  private def runnerOf(root: Path): Path = root.resolve("runner")
  private def logOf(root: Path): Path = root.resolve("run.log")
  private def manifestOf(root: Path): Path = root.resolve("run.json")

  /** A runner that ignores its arguments, prints `reports` and exits with `code`. */
  private def installRunner(root: Path, reports: String, code: Int = 0): Unit = {
    val reportsFile = root.resolve("reports.txt")
    Files.writeString(reportsFile, reports, StandardCharsets.UTF_8)
    val script = s"#!/bin/sh\ncat '${reportsFile}'\nexit $code\n"
    Files.writeString(runnerOf(root), script)
    Files.setPosixFilePermissions(runnerOf(root), PosixFilePermissions.fromString("rwxr-xr-x"))
  }

  private def runReports(root: Path, reports: String, code: Int = 0): Manifest = {
    installRunner(root, reports, code)
    verify(grammarOf(root), runnerOf(root), Vector("", "ab"), logOf(root), 1, report = _ => ())
  }

  private def report(root: Path): Map[String, String] = {
    // The manifest is flat JSON written by `dumps(indent=2)`; read it back field by field.
    val text = Files.readString(manifestOf(root))
    val entry = "\\s*\"([^\"]+)\": (.*?),?\\n".r
    entry.findAllMatchIn(text).map(m => m.group(1) -> m.group(2)).toMap
  }

  private def str(value: Json): String = value match {
    case Json.Str(s) => s
    case other => other.toString
  }

  directory.test("success requires all unchanged inputs") { root =>
    val result = runReports(root, "match\t\"\"\ttrue\tcharacters=0\trepeat=1\n" +
      "match\t\"ab\"\tfalse\tcharacters=2\trepeat=1\n")
    assertEquals((str(result("status")), result("checked")), ("passed", Json.Int(2)))
    assertEquals(str(result("sha256")).length, 64)
    assertEquals(result("returncode"), Json.Int(0))
    assert(!result.contains("current_word"))
    assertEquals(report(root)("status"), "\"passed\"")
  }

  directory.test("counterexample replaces old success") { root =>
    val error = intercept[AssertionError] {
      runReports(root, "match\t\"\"\ttrue\tcharacters=0\trepeat=1\n" +
        "match\t\"ab\"\ttrue\tcharacters=2\trepeat=1\n")
    }
    assertEquals(error.getMessage,
      "{'word': 'ab', 'expected': False, 'report': 'match\\t\"ab\"\\ttrue\\tcharacters=2\\trepeat=1'}")
    val result = report(root)
    assertEquals((result("status"), result("checked"), result("current_word")), ("\"failed\"", "1", "\"ab\""))
    assert(Files.readString(logOf(root)).contains("\"ab\""))
    assert(result("error").startsWith("\"AssertionError: {'word': 'ab'"), result("error"))
  }

  directory.test("truncated or repeated input reports fail") { root =>
    for (reports <- Vector("", "match\t\"\"\ttrue\tcharacters=0\trepeat=2\n")) {
      val error = intercept[Throwable](runReports(root, reports))
      assert(error.isInstanceOf[RuntimeException] || error.isInstanceOf[AssertionError], error.toString)
      assertEquals(report(root)("status"), "\"failed\"", reports)
    }
    // json.dumps escapes the backslash of the repr'd tab and the quotes of the report
    assertEquals(report(root)("error"), "\"AssertionError: {'word': '', 'expected': True, 'report': 'match\\\\t\\\"\\\"\\\\ttrue\\\\tcharacters=0\\\\trepeat=2'}\"")
    intercept[RuntimeException](runReports(root, ""))
    assertEquals(report(root)("error"), "\"RuntimeError: runner exited with 0; checked 0/2\"")
  }

  directory.test("launch failure replaces old success") { root =>
    val error = intercept[PyError] {
      verify(grammarOf(root), runnerOf(root), Vector(""), logOf(root), 0, report = _ => ())
    }
    assertEquals(error.pyName, "FileNotFoundError")
    val result = report(root)
    assertEquals(result("status"), "\"failed\"")
    assert(result("error").contains("No such file or directory"), result("error"))
    assert(result("error").contains("runner"), result("error"))
    assert(!result.contains("returncode"))
  }

  directory.test("output collision does not overwrite grammar") { root =>
    val before = Files.readAllBytes(grammarOf(root))
    intercept[IllegalArgumentException] {
      verify(grammarOf(root), runnerOf(root), Vector(""), grammarOf(root), 0, report = _ => ())
    }
    assertEquals(Files.readAllBytes(grammarOf(root)).toVector, before.toVector)
  }

  // ---- beyond the Python tests

  directory.test("the manifest and stdout agree with the Python script on the same fake runner") { root =>
    installRunner(root, "loaded\tgrammar\nmatch\t\"\"\ttrue\tcharacters=0\trepeat=1\n" +
      "match\t\"ab\"\tfalse\tcharacters=2\trepeat=1\n")
    val printed = new StringBuilder
    verify(grammarOf(root), runnerOf(root), Vector("", "ab"), logOf(root), 1, report = line => printed.append(line).append('\n'))
    val scalaManifest = Files.readString(manifestOf(root))
    val scalaLog = Files.readString(logOf(root))
    val expectedStdout = PyDiff.python("-c",
      s"""from pathlib import Path
         |from verify_window_pal import verify
         |verify(Path(${PyFormat.strRepr(grammarOf(root).toString)}), Path(${PyFormat.strRepr(runnerOf(root).toString)}),
         |       ["", "ab"], Path(${PyFormat.strRepr(logOf(root).toString)}), 1)
         |""".stripMargin)
    val pythonManifest = Files.readString(manifestOf(root))
    val seconds = "\"seconds\": [0-9.e+-]+".r
    def normalise(s: String): String = seconds.replaceAllIn(s, "\"seconds\": T")
    assertEquals(normalise(scalaManifest), normalise(pythonManifest))
    assertEquals(normalise(printed.toString), normalise(expectedStdout))
    assertEquals(scalaLog, Files.readString(logOf(root)))

    // the same for a failing run: the recorded error text must match Python's
    installRunner(root, "match\t\"\"\ttrue\tcharacters=0\trepeat=1\nmatch\t\"ab\"\ttrue\tcharacters=2\trepeat=1\n")
    intercept[AssertionError] {
      verify(grammarOf(root), runnerOf(root), Vector("", "ab"), logOf(root), 1, report = _ => ())
    }
    val scalaFailure = Files.readString(manifestOf(root))
    PyDiff.python("-c",
      s"""from pathlib import Path
         |from verify_window_pal import verify
         |try:
         |    verify(Path(${PyFormat.strRepr(grammarOf(root).toString)}), Path(${PyFormat.strRepr(runnerOf(root).toString)}),
         |           ["", "ab"], Path(${PyFormat.strRepr(logOf(root).toString)}), 1)
         |except AssertionError:
         |    pass
         |""".stripMargin)
    assertEquals(normalise(scalaFailure), normalise(Files.readString(manifestOf(root))))
  }

  test("words(n) equals the Python word list") {
    for (maxLength <- Vector(0, 1, 5)) {
      val expected = PyDiff.python("-c",
        s"""import itertools
          |words = ["".join(chars) for n in range($maxLength + 1) for chars in itertools.product("ab", repeat=n)]
          |words += ["abbba", "abbbba", "ababa", "abaaba", "abbaabba", "abbaabab",
          |          "abbbbbbbbbbba", "abbbbbbbbbbab", "a" * 17, "a" * 33,
          |          ("a" * 8 + "b") * 2 + "a" * 8, "ab" * 9,
          |          "abba" * 8, "abba" * 7 + "abab", "#", "a!a", "a.a", "abcba"]
          |print("\\n".join(dict.fromkeys(words)))
          |""".stripMargin)
      assertEquals(words(maxLength).mkString("\n") + "\n", expected, maxLength)
    }
  }

  test("dumps reproduces json.dumps with and without indent") {
    val fields = Vector("status" -> Json.Str("running"), "checked" -> Json.Int(0), "seconds" -> Json.Num(0.5), "ok" -> Json.Bool(true))
    assertEquals(dumps(fields), "{\"status\": \"running\", \"checked\": 0, \"seconds\": 0.5, \"ok\": true}")
    assertEquals(dumps(fields, Some(2)), "{\n  \"status\": \"running\",\n  \"checked\": 0,\n  \"seconds\": 0.5,\n  \"ok\": true\n}")
    assertEquals(dumps(Vector.empty, Some(2)), "{}")
  }

  test("jsonLoadsString decodes JSON string literals like json.loads") {
    assertEquals(jsonLoadsString("\"ab\""), Some("ab"))
    assertEquals(jsonLoadsString("\"a\\tb\\u0041\""), Some("a\tbA"))
    assertEquals(jsonLoadsString("5"), None)
    intercept[PyError](jsonLoadsString("\"unterminated"))
    intercept[PyError](jsonLoadsString(""))
  }

  test("parseArgs mirrors the argparse front end") {
    assertEquals(parseArgs(Vector("g.peg", "--runner", "r", "--log", "l")),
      Right(Config(Path.of("g.peg"), Path.of("r"), 5, Path.of("l"))))
    assertEquals(parseArgs(Vector("--runner=r", "--max-length", "3", "--log=l", "g.peg")),
      Right(Config(Path.of("g.peg"), Path.of("r"), 3, Path.of("l"))))
    assertEquals(parseArgs(Vector("g.peg", "--runner", "r", "--log", "l", "--max-length", "13")),
      Left("the exhaustive test range must be between 0 and 12"))
    assertEquals(parseArgs(Vector("g.peg")), Left("the following arguments are required: --runner, --log"))
    assert(parseArgs(Vector("g.peg", "--runner", "r", "--log", "l", "--max-length", "x")).isLeft)
  }

  test("withSuffix behaves like Path.with_suffix") {
    assertEquals(withSuffix(Path.of("/x/run.log"), ".json"), Path.of("/x/run.json"))
    assertEquals(withSuffix(Path.of("/x/run"), ".json"), Path.of("/x/run.json"))
  }
}
