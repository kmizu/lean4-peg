package pal

import java.io.{ByteArrayOutputStream, PrintStream}

/** テスト用の小道具。 */
object TestUtil {

  /** `println` の出力を文字列として捕まえる（`__main__` デモの差分テスト用）。 */
  def captureStdout(body: => Unit): String = {
    val buffer = new ByteArrayOutputStream
    val stream = new PrintStream(buffer, true, "UTF-8")
    Console.withOut(stream) {
      body
    }
    stream.flush()
    new String(buffer.toByteArray, "UTF-8")
  }
}
