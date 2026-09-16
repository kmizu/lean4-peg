package pal

/** External work-trace generator for testing the emitted matcher PEG.
  *
  * This is a test protocol, never the final PAL input transformation. Each
  * source instruction uses at most one queue pop, followed by three work units.
  * The finite broadcast visits one queue at a time under the same schedule.
  *
  * Port of `gs_match_trace.py`.
  */
object GsMatchTrace {

  def trace(prefix: String, text: String, program: Option[Program] = None): String = {
    if (prefix.isEmpty || (prefix + text).exists(char => char != 'a' && char != 'b')) {
      throw new IllegalArgumentException("nonempty binary prefix and binary text required")
    }
    val table = program.getOrElse(GsMatchHeads.compileMatcher())
    val observer = new StreamingMatcher(prefix.reverse, Some(table))
    // One push and three work units per queue, followed by the broadcast exit.
    val broadcast = 4 * (1 + GsHeadLiveness.analyzeReaders(table).registers) + 1
    val parts = new StringBuilder
    prefix.foreach { char =>
      parts += char
      parts ++= "." * 5
    }
    parts += '!'
    parts ++= "." * (4 * observer.drain())
    text.foreach { char =>
      observer.append(char)
      parts += char
      parts ++= "." * (broadcast + 4 * observer.drain())
    }
    parts.result()
  }
}
