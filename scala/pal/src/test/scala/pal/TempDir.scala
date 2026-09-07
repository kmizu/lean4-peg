package pal

import java.nio.file.{Files, Path}
import scala.jdk.StreamConverters.*

/** Python `tempfile.TemporaryDirectory()` for tests. */
object TempDir {

  def withTempDir[A](prefix: String)(body: Path => A): A = {
    val directory = Files.createTempDirectory(prefix)
    try {
      body(directory)
    } finally {
      Files.walk(directory).toScala(Vector).sortBy(_.getNameCount)(using Ordering.Int.reverse).foreach(Files.deleteIfExists(_))
    }
  }
}
