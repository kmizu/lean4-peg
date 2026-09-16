package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

/** Regenerate finite-phase plain PEG examples, without modifying their inputs.
  *
  * Port of `generate_phase_examples.py`. `main` takes an optional
  * `docs/palindromes-in-peg` directory argument (see `GenerateScaffoldExamples.locateDirectory`).
  */
object GeneratePhaseExamples {

  /** `(filename, generated text)` for every example, in the Python dictionary's order. */
  def examples(directory: Path): Vector[(String, String)] = {
    val move = new String(Files.readAllBytes(directory.resolve("generated").resolve("sparse_preserving_move.peg")), StandardCharsets.UTF_8)
    val sources = Vector(
      "phase_preserving_move_2.peg" -> (move, 2),
      "phase_preserving_move_4.peg" -> (move, 4),
      "phase_ordered_choice.peg" -> ("S = (\"a\" / \"aa\") \"bb\" !.;", 2),
      "phase_balanced.peg" -> ("S = A !.; A = \"a\" A \"b\" / \"\";", 3),
      "phase_repetition.peg" -> ("S = \"a\"* \"bb\" !.;", 2),
      "phase_greedy.peg" -> ("S = (\"a\" &\"a\")* \"aa\" !.;", 2)
    )
    sources.map { case (filename, (source, width)) => filename -> PhasePeg.inverseRepeat(source, width) }
  }

  def main(args: Array[String]): Unit = {
    val directory = GenerateScaffoldExamples.locateDirectory(args)
    for ((filename, output) <- examples(directory)) {
      Files.write(directory.resolve("generated").resolve(filename), output.getBytes(StandardCharsets.UTF_8))
      println(s"$filename: ${GenerateScaffoldExamples.summary(output)}")
    }
  }
}
