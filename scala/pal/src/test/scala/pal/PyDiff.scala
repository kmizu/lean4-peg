package pal

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** Python 版（docs/palindromes-in-peg）との差分テスト基盤。
  *
  * Python 版は移植の基準として残してある。出力を持つモジュールは、この object で
  * Python を実行し、Scala 版の出力とバイト一致することを検査する。
  */
object PyDiff {

  /** docs/palindromes-in-peg の絶対パス。sbt は scala/ を cwd にして fork するので、
    * そこから上へ辿る。
    */
  val pyDir: Path = {
    val here = Paths.get("").toAbsolutePath
    Iterator
      .iterate(here)(_.getParent)
      .takeWhile(_ != null)
      .map(_.resolve("docs/palindromes-in-peg"))
      .find(Files.isDirectory(_))
      .getOrElse(throw new IllegalStateException(s"docs/palindromes-in-peg not found above $here"))
  }

  /** `python3 args...` を pyDir で実行して stdout を返す。非ゼロ終了は例外。 */
  def python(args: String*): String = {
    val process = new ProcessBuilder(("python3" +: args).asJava)
      .directory(pyDir.toFile)
      .redirectErrorStream(false)
      .start()
    // Drain both pipes concurrently: a large Python traceback can fill stderr
    // while stdout stays open, deadlocking a sequential read of the two pipes.
    val errorRead = new java.util.concurrent.FutureTask[String](
      () => new String(process.getErrorStream.readAllBytes(), "UTF-8"))
    val errorThread = new Thread(errorRead, "pal-python-stderr")
    errorThread.setDaemon(true)
    errorThread.start()
    val out = new String(process.getInputStream.readAllBytes(), "UTF-8")
    val err = errorRead.get()
    val code = process.waitFor()
    if (code != 0) {
      throw new IllegalStateException(s"python3 ${args.mkString(" ")} exited $code\n$err")
    }
    out
  }

  /** ファイルを UTF-8 文字列として読む（ゴールデン比較用）。 */
  def readGolden(relative: String): String = {
    new String(Files.readAllBytes(pyDir.resolve(relative)), "UTF-8")
  }

  /** Scala 側の文字列が Python スクリプトの stdout と完全一致することを検査する。 */
  def assertSameAsPython(actual: String, script: String, args: String*): Unit = {
    val expected = python((script +: args)*)
    if (actual != expected) {
      throw new AssertionError(firstDifference(actual, expected, s"$script ${args.mkString(" ")}"))
    }
  }

  /** 2 つの文字列の最初の不一致を行番号付きで説明する。 */
  def firstDifference(actual: String, expected: String, label: String): String = {
    val a = actual.linesIterator.toVector
    val e = expected.linesIterator.toVector
    val line = a.zip(e).indexWhere { case (x, y) => x != y }
    if (line >= 0) {
      s"$label: line ${line + 1} differs\n  scala : ${a(line)}\n  python: ${e(line)}"
    } else {
      s"$label: line counts differ (scala ${a.size}, python ${e.size})"
    }
  }
}
