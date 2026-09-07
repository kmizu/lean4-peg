package pal

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, IOException}
import java.nio.charset.StandardCharsets
import java.nio.file.{AccessDeniedException, Files, NoSuchFileException, Path}
import java.security.MessageDigest
import java.util.concurrent.TimeUnit
import scala.collection.immutable.VectorMap
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** Check a concrete ordinary PEG on unchanged binary words with Rust.
  * （Python 版: `docs/palindromes-in-peg/verify_window_pal.py`）
  *
  * The runner receives words directly, without --repeat or a work protocol.
  * The complete runner output and a compact verification manifest are retained.
  * The manifest status is running, passed, or failed; only passed is evidence of
  * a completed check. Failures retain the checked count and offending report.
  *
  * Python 版は例外の型名とメッセージを manifest の `error` に残す。移植では対応する
  * Scala 例外を投げ、`error` 欄には Python と同じ名前・文面（`ValueError`,
  * `AssertionError: {'word': ...}`, `RuntimeError`, `FileNotFoundError` など）を書く。
  */
object VerifyWindowPal {

  // ------------------------------------------------------------------ manifest JSON

  /** The JSON values a manifest holds (all flat). */
  sealed trait Json
  object Json {
    final case class Str(value: String) extends Json
    final case class Int(value: Long) extends Json
    final case class Num(value: Double) extends Json
    final case class Bool(value: Boolean) extends Json
  }

  private def jsonValue(value: Json): String = value match {
    case Json.Str(s)  => PyFormat.jsonString(s, ensureAscii = true) // json.dumps' default
    case Json.Int(n)  => n.toString
    case Json.Num(d)  => PyFormat.floatRepr(d)
    case Json.Bool(b) => if (b) "true" else "false"
  }

  /** `json.dumps(dict, indent=2)` when `indent` is given, else the compact one-line form. */
  def dumps(fields: Iterable[(String, Json)], indent: Option[Int] = None): String = {
    val entries = fields.map { case (k, v) => PyFormat.jsonString(k, ensureAscii = true) + ": " + jsonValue(v) }
    indent match {
      case Some(width) if entries.nonEmpty =>
        val pad = " " * width
        entries.mkString("{\n" + pad, ",\n" + pad, "\n}")
      case _ => entries.mkString("{", ", ", "}")
    }
  }

  /** The manifest written next to the log; keeps insertion order like a Python dict. */
  type Manifest = VectorMap[String, Json]

  // ------------------------------------------------------------------ words

  /** The word list of `main`: all binary words up to `maxLength`, then hand-picked
    * extras; duplicates removed keeping the first occurrence.
    */
  def words(maxLength: Int): Vector[String] = {
    val exhaustive = (0 to maxLength).flatMap(n => Twoway.product("ab", n))
    val extras = Vector("abbba", "abbbba", "ababa", "abaaba", "abbaabba", "abbaabab",
      "abbbbbbbbbbba", "abbbbbbbbbbab", "a" * 17, "a" * 33,
      ("a" * 8 + "b") * 2 + "a" * 8, "ab" * 9,
      "abba" * 8, "abba" * 7 + "abab", "#", "a!a", "a.a", "abcba")
    (exhaustive ++ extras).distinct.toVector
  }

  // ------------------------------------------------------------------ Python-style errors

  /** A failure whose `error` line must read like Python's `f"{type(e).__name__}: {e}"`. */
  final class PyError(val pyName: String, message: String) extends RuntimeException(message)

  private def valueError(message: String): Nothing = throw new IllegalArgumentException(message)

  /** Python's `OSError` subclasses and texts for the file operations the script performs
    * (`str(e)` is `[Errno N] <strerror>: '<path>'`).
    */
  private def osError(error: IOException, path: Path): PyError = {
    val shown = PyFormat.strRepr(path.toString)
    error match {
      case _: NoSuchFileException => new PyError("FileNotFoundError", s"[Errno 2] No such file or directory: $shown")
      case _: AccessDeniedException => new PyError("PermissionError", s"[Errno 13] Permission denied: $shown")
      case _ if Files.isDirectory(path) => // the JDK's message is the OS strerror in the current locale
        new PyError("IsADirectoryError", s"[Errno 21] Is a directory: $shown")
      case e => new PyError("OSError", Option(e.getMessage).getOrElse(""))
    }
  }

  /** Run a file operation on `path`, translating an `IOException` into Python's error. */
  private def onFile[A](path: Path)(body: => A): A = {
    try { body } catch { case e: IOException => throw osError(e, path) }
  }

  /** `f"{type(error).__name__}: {error}"` for the exceptions this module raises. */
  def describe(error: Throwable): String = {
    val name = error match {
      case e: PyError                  => e.pyName
      case _: IllegalArgumentException => "ValueError" // NumberFormatException も含む
      case _: AssertionError           => "AssertionError"
      case _: NoSuchElementException   => "KeyError"
      case _: IndexOutOfBoundsException => "IndexError"
      case _: IOException              => "OSError"
      case _: RuntimeException         => "RuntimeError"
      case e                           => e.getClass.getSimpleName
    }
    s"$name: ${Option(error.getMessage).getOrElse("")}"
  }

  /** `str(AssertionError(dict(word=..., expected=..., report=...)))`: the dict's repr. */
  private def mismatchMessage(word: String, expected: Boolean, report: String): String = {
    s"{'word': ${PyFormat.strRepr(word)}, 'expected': ${if (expected) "True" else "False"}, 'report': ${PyFormat.strRepr(report)}}"
  }

  // ------------------------------------------------------------------ runner output

  /** Python's `str.rstrip()` (whitespace only). */
  private def rstrip(s: String): String = {
    var end = s.length
    while (end > 0 && Character.isWhitespace(s.charAt(end - 1))) { end -= 1 }
    s.substring(0, end)
  }

  /** `json.loads(text)` for the word field: `Some(string)` for a JSON string literal,
    * `None` for any other well-formed value (which then simply differs from the word).
    * Malformed text raises like `json.JSONDecodeError`.
    */
  def jsonLoadsString(text: String): Option[String] = {
    val t = text.trim
    if (!t.startsWith("\"")) {
      if (t.isEmpty) { throw new PyError("JSONDecodeError", "Expecting value: line 1 column 1 (char 0)") }
      return None
    }
    val sb = new StringBuilder
    var i = 1
    var closed = false
    while (!closed) {
      if (i >= t.length) { throw new PyError("JSONDecodeError", s"Unterminated string starting at: line 1 column 1 (char 0)") }
      val c = t.charAt(i)
      if (c == '"') { closed = true; i += 1 }
      else if (c == '\\') {
        if (i + 1 >= t.length) { throw new PyError("JSONDecodeError", s"Unterminated string starting at: line 1 column 1 (char 0)") }
        t.charAt(i + 1) match {
          case '"'  => sb.append('"')
          case '\\' => sb.append('\\')
          case '/'  => sb.append('/')
          case 'b'  => sb.append('\b')
          case 'f'  => sb.append('\f')
          case 'n'  => sb.append('\n')
          case 'r'  => sb.append('\r')
          case 't'  => sb.append('\t')
          case 'u' =>
            if (i + 5 >= t.length) { throw new PyError("JSONDecodeError", s"Invalid \\uXXXX escape: line 1 column ${i + 1} (char $i)") }
            sb.append(Integer.parseInt(t.substring(i + 2, i + 6), 16).toChar)
            i += 4
          case _ => throw new PyError("JSONDecodeError", s"Invalid \\escape: line 1 column ${i + 1} (char $i)")
        }
        i += 2
      } else if (c < 0x20) {
        throw new PyError("JSONDecodeError", s"Invalid control character at: line 1 column ${i + 1} (char $i)")
      } else { sb.append(c); i += 1 }
    }
    if (i != t.length) { throw new PyError("JSONDecodeError", s"Extra data: line 1 column ${i + 1} (char $i)") }
    Some(sb.toString)
  }

  /** `dict(field.split("=", 1) for field in fields)`. */
  private def details(fields: Seq[String]): Map[String, String] = {
    fields.zipWithIndex.map { case (field, i) =>
      field.indexOf('=') match {
        case -1 => valueError(s"dictionary update sequence element #$i has length 1; 2 is required")
        case at => field.substring(0, at) -> field.substring(at + 1)
      }
    }.toMap
  }

  /** `int(text)`: Python accepts surrounding whitespace, `+`/`-` and underscores. */
  private def pyInt(text: String): Int = {
    try { text.trim.replace("_", "").toInt }
    catch { case _: NumberFormatException => valueError(s"invalid literal for int() with base 10: ${PyFormat.strRepr(text)}") }
  }

  /** Check one `match` report line against the word it must describe. */
  private def checkReport(line: String, word: String): Unit = {
    val fields = rstrip(line).split("\t", -1).toVector
    if (fields.length < 3) { throw new IndexOutOfBoundsException("list index out of range") }
    val actual = fields(2) == "true"
    val expected = word.forall(c => c == 'a' || c == 'b') && word == word.reverse
    val info = details(fields.drop(3))
    val bad = !(fields(2) == "true" || fields(2) == "false") ||
      !jsonLoadsString(fields(1)).contains(word) ||
      actual != expected ||
      pyInt(info.getOrElse("characters", throw new NoSuchElementException("'characters'"))) != word.length ||
      info.getOrElse("repeat", throw new NoSuchElementException("'repeat'")) != "1"
    if (bad) { throw new AssertionError(mismatchMessage(word, expected, rstrip(line))) }
  }

  /** Read one line including its terminator, translating `\r\n` and `\r` to `\n`
    * (Python's universal newlines); `None` at end of stream.
    */
  private def readLine(reader: BufferedReader): Option[String] = {
    val sb = new StringBuilder
    var ch = reader.read()
    while (ch != -1) {
      if (ch == '\n') { return Some(sb.append('\n').toString) }
      if (ch == '\r') {
        reader.mark(1)
        val next = reader.read()
        if (next != '\n' && next != -1) { reader.reset() }
        return Some(sb.append('\n').toString)
      }
      sb.append(ch.toChar)
      ch = reader.read()
    }
    if (sb.isEmpty) None else Some(sb.toString)
  }

  private def sha256Hex(path: Path): String = {
    val digest = MessageDigest.getInstance("SHA-256")
    digest.update(Files.readAllBytes(path))
    digest.digest().map(b => f"$b%02x").mkString
  }

  private def launch(runner: Path, grammar: Path, words: Seq[String]): Process = {
    val command = (runner.toString +: grammar.toString +: words).asJava
    try {
      new ProcessBuilder(command).redirectErrorStream(true).start()
    } catch {
      case _: IOException if !Files.exists(runner) =>
        throw new PyError("FileNotFoundError", s"[Errno 2] No such file or directory: ${PyFormat.strRepr(runner.toString)}")
    }
  }

  // ------------------------------------------------------------------ verify

  /** Run `runner grammar words...`, log its output, and write the manifest.  `report`
    * receives what the Python script prints to stdout.  Raises on any failure after
    * recording it in the manifest, exactly like the Python version.
    */
  def verify(grammar: Path, runner: Path, words: Seq[String], logPath: Path, maxLength: Int,
      report: String => Unit = line => Console.out.println(line)): Manifest = {
    val manifestPath = withSuffix(logPath, ".json")
    val paths = Vector(grammar, runner, logPath, manifestPath).map(_.toAbsolutePath.normalize)
    if (paths.distinct.size != paths.size) {
      valueError("grammar, runner, log and manifest must use distinct paths")
    }
    val started = System.nanoTime()
    var checked = 0
    var process: Process = null
    val manifest = mutable.LinkedHashMap[String, Json](
      "status" -> Json.Str("running"), "grammar" -> Json.Str(grammar.toString), "checked" -> Json.Int(0),
      "total" -> Json.Int(words.size), "exhaustive_max_length" -> Json.Int(maxLength),
      "input_transform" -> Json.Str("none"), "log" -> Json.Str(logPath.toString))

    def save(): Unit = {
      manifest("checked") = Json.Int(checked)
      manifest("seconds") = Json.Num((System.nanoTime() - started) / 1e9)
      onFile(manifestPath) { Files.writeString(manifestPath, dumps(manifest, Some(2)) + "\n", StandardCharsets.UTF_8) }
      ()
    }

    def handleLine(log: BufferedWriter, line: String): Unit = {
      log.write(line)
      log.flush()
      if (line.startsWith("loaded\t")) { report(rstrip(line)) }
      if (line.startsWith("match\t")) {
        manifest("last_report") = Json.Str(rstrip(line))
        if (checked >= words.size) { valueError("runner reported more matches than requested") }
        val word = words(checked)
        manifest("current_word") = Json.Str(word)
        checkReport(line, word)
        checked += 1
        if (checked % 16 == 0 || checked == words.size) { report(s"checked $checked/${words.size} unchanged inputs") }
      }
    }

    // Invalidate an earlier success before hashing, launching, or parsing output.
    save()
    try {
      val log = onFile(logPath)(Files.newBufferedWriter(logPath, StandardCharsets.UTF_8))
      try {
        onFile(grammar) {
          manifest("sha256") = Json.Str(sha256Hex(grammar))
          manifest("bytes") = Json.Int(Files.size(grammar))
        }
        save()
        process = launch(runner, grammar, words)
        val reader = new BufferedReader(new InputStreamReader(process.getInputStream, StandardCharsets.UTF_8))
        var line = readLine(reader)
        while (line.isDefined) {
          handleLine(log, line.get)
          line = readLine(reader)
        }
      } finally {
        log.close()
      }
      val code = process.waitFor()
      if (code != 0 || checked != words.size) {
        throw new RuntimeException(s"runner exited with $code; checked $checked/${words.size}")
      }
      manifest("status") = Json.Str("passed")
      manifest.remove("current_word")
      manifest.remove("last_report")
    } catch {
      case error: Throwable =>
        manifest("status") = Json.Str("failed")
        manifest("error") = Json.Str(describe(error))
        throw error
    } finally {
      try {
        if (process != null) {
          if (process.isAlive) {
            process.destroy()
            if (!process.waitFor(5, TimeUnit.SECONDS)) {
              process.destroyForcibly()
              process.waitFor()
            }
          }
          manifest("returncode") = Json.Int(process.exitValue())
          process.getInputStream.close()
        }
      } finally {
        save()
      }
    }
    report(dumps(manifest))
    VectorMap.from(manifest)
  }

  /** `Path.with_suffix`: replace the final suffix (or append one). */
  def withSuffix(path: Path, suffix: String): Path = {
    val name = path.getFileName.toString
    val dot = name.lastIndexOf('.')
    val stem = if (dot > 0) name.substring(0, dot) else name
    path.resolveSibling(stem + suffix)
  }

  // ------------------------------------------------------------------ CLI

  final case class Config(grammar: Path, runner: Path, maxLength: Int, log: Path)

  /** The argparse front end: `grammar --runner R [--max-length N] --log L`. */
  def parseArgs(args: Seq[String]): Either[String, Config] = {
    var grammar: Option[String] = None
    var runner: Option[String] = None
    var log: Option[String] = None
    var maxLength = 5
    var error: Option[String] = None
    var rest = args.toList
    while (rest.nonEmpty && error.isEmpty) {
      rest match {
        case "--runner" :: v :: tail => runner = Some(v); rest = tail
        case "--log" :: v :: tail => log = Some(v); rest = tail
        case "--max-length" :: v :: tail =>
          rest = tail
          v.toIntOption match {
            case Some(n) => maxLength = n
            case None => error = Some(s"argument --max-length: invalid int value: ${PyFormat.strRepr(v)}")
          }
        case opt :: tail if opt.startsWith("--") && opt.contains('=') =>
          val at = opt.indexOf('=')
          rest = opt.substring(0, at) :: opt.substring(at + 1) :: tail
        case opt :: _ if opt.startsWith("--") =>
          error = Some(s"unrecognized arguments: $opt")
        case positional :: tail =>
          if (grammar.isDefined) { error = Some(s"unrecognized arguments: $positional") }
          grammar = Some(positional); rest = tail
        case Nil => ()
      }
    }
    val missing = Vector(("grammar", grammar), ("--runner", runner), ("--log", log)).collect {
      case (name, None) => name
    }
    error match {
      case Some(message) => Left(message)
      case None if missing.nonEmpty => Left(s"the following arguments are required: ${missing.mkString(", ")}")
      case None if maxLength < 0 || maxLength > 12 => Left("the exhaustive test range must be between 0 and 12")
      case None => Right(Config(Path.of(grammar.get), Path.of(runner.get), maxLength, Path.of(log.get)))
    }
  }

  def main(args: Array[String]): Unit = {
    parseArgs(args.toSeq) match {
      case Left(message) =>
        Console.err.println("usage: verify_window_pal grammar --runner RUNNER [--max-length MAX_LENGTH] --log LOG")
        Console.err.println(s"verify_window_pal: error: $message")
        sys.exit(2)
      case Right(config) =>
        verify(config.grammar, config.runner, words(config.maxLength), config.log, config.maxLength)
        ()
    }
  }
}
