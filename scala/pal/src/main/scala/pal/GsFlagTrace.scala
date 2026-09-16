package pal

/** External loading/work traces for testing the finite mirror-flag worker.
  *
  * Port of `gs_flag_trace.py`.
  */
object GsFlagTrace {

  /** The loading trace of `word` with the interval marker `|` before position
    * `lower`, then `!` and one work unit per physical transition of the flag
    * worker (`4 * steps + 1`).
    */
  def trace(word: String, lower: Int, program: Option[Program] = None, dual: Boolean = false): String = {
    if (word.exists(char => char != 'a' && char != 'b') || !(0 <= lower && lower <= word.length)) {
      throw new IllegalArgumentException("binary word and valid lower endpoint required")
    }
    val steps = if (dual) {
      val observer = new DualFlagVM(word, lower, word.length, program.orElse(Some(GsDualFlags.compileDualFlags())))
      observer.run()
      observer.steps
    } else {
      val observer = new FlagVM(word, lower, word.length, program.orElse(Some(GsFlagHeads.compileFlags())))
      observer.run()
      observer.steps
    }
    val parts = new StringBuilder
    word.zipWithIndex.foreach { case (char, index) =>
      if (index == lower) {
        parts += '|'
      }
      parts += char
      parts ++= "." * 4
    }
    if (lower == word.length) {
      parts += '|'
    }
    // One GS instruction plus at most three queue work units, then halt.
    parts += '!'
    parts ++= "." * (4 * steps + 1)
    parts.result()
  }
}
