package pal

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption}

/** Superseded fixed-arrival experiment; not the current PAL translation.
  *
  * Use the online FIFO/whole-round pipeline for the current construction. This
  * generator reproduces earlier experiments and their failures. Its fixed-work
  * constants are experimental, not a claim of correctness for PAL.
  * `--expanded-only` retains the intermediate PEG with each letter repeated
  * `budget` times; the default applies inverse repetition to unchanged strings.
  */
object GenerateGalilPeg {
  final case class Options(output: Path, quantum: Int = 64, matchDelay: Int = 256, budget: Int = 2048,
                           rawInstructions: Boolean = false, omitInvariantMonitors: Boolean = false,
                           expandedOnly: Boolean = false, matches: Option[Vector[String]] = None)
  final case class Emitted(path: Path, rules: Long, bytes: Long)

  private def withSuffix(path: Path, suffix: String): Path = {
    val name = path.getFileName.toString
    val dot = name.lastIndexOf('.')
    path.resolveSibling((if (dot > 0) { name.substring(0, dot) } else { name }) + suffix)
  }

  /** Emit incrementally and replace only the completed intermediate artifact. */
  def emitExpanded(machine: Scaffold, output: Path): Emitted = {
    val temporary = output.resolveSibling(output.getFileName.toString + ".partial")
    val writer = Files.newBufferedWriter(temporary, UTF_8)
    var count = 0L
    try {
      machine.iterRules().foreach { rule =>
        writer.write(rule)
        writer.write("\n")
        count += 1
      }
    } finally { writer.close() }
    Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING)
    Emitted(output, count, Files.size(output))
  }

  def generate(options: Options, report: String => Unit = println): Vector[Emitted] = {
    val intermediate = if (options.expandedOnly) { options.output } else { withSuffix(options.output, ".expanded.peg") }
    val expanded = {
      val (_, machine) = Expr.share {
        ScaffoldCircuitGalil.build(options.quantum, options.matchDelay, options.budget,
          coarse = !options.rawInstructions, checkInvariants = !options.omitInvariantMonitors)
      }
      report(s"built ${machine.labels.size} labels, ${machine.pointers.size} pointers")
      emitExpanded(machine, intermediate)
    }
    report(s"emitted ${expanded.path}: ${expanded.rules} rules, ${expanded.bytes} bytes")
    val emitted = if (options.expandedOnly) { Vector(expanded) } else {
      val source = PhasePeg.inverseRepeat(Files.readString(intermediate, UTF_8), options.budget)
      Files.writeString(options.output, source, UTF_8)
      val result = Emitted(options.output, source.linesIterator.size.toLong, source.getBytes(UTF_8).length.toLong)
      report(s"emitted ${result.path}: ${result.rules} rules, ${result.bytes} bytes")
      Vector(expanded, result)
    }
    options.matches.foreach { words =>
      val grammar = new FileGrammar(options.output)
      var mismatches = 0
      try {
        for (word <- words) {
          if (word.exists(c => c != 'a' && c != 'b')) {
            throw new IllegalArgumentException("match examples must be binary strings over a,b")
          }
          val supplied = if (options.expandedOnly) { word.flatMap(c => c.toString * options.budget) } else { word }
          val actual = grammar.accepts(supplied, compact = true)
          val expected = word == word.reverse
          def bool(value: Boolean): String = if (value) { "True" } else { "False" }
          report(s"'$word': PEG=${bool(actual)}, palindrome=${bool(expected)}")
          if (actual != expected) { mismatches += 1 }
        }
      } finally { grammar.close() }
      if (mismatches != 0) { throw new IllegalStateException(s"$mismatches candidate mismatches") }
    }
    emitted
  }

  def parseArgs(args: Array[String]): Options = {
    var output: Option[Path] = None
    var quantum = 64
    var matchDelay = 256
    var budget = 2048
    var raw = false
    var omit = false
    var expanded = false
    var matches: Option[Vector[String]] = None
    var i = 0
    def integer(flag: String): Int = {
      i += 1
      if (i >= args.length) { throw new IllegalArgumentException(s"$flag requires an integer") }
      args(i).toInt
    }
    while (i < args.length) {
      args(i) match {
        case "--quantum" => quantum = integer("--quantum")
        case "--match-delay" => matchDelay = integer("--match-delay")
        case "--budget" => budget = integer("--budget")
        case "--raw-instructions" => raw = true
        case "--omit-invariant-monitors" => omit = true
        case "--expanded-only" => expanded = true
        case "--match" =>
          val words = Vector.newBuilder[String]
          while (i + 1 < args.length && !args(i + 1).startsWith("--")) {
            i += 1
            words += args(i)
          }
          matches = Some(words.result())
        case value if !value.startsWith("-") && output.isEmpty => output = Some(Path.of(value))
        case value => throw new IllegalArgumentException(s"unrecognized argument: $value")
      }
      i += 1
    }
    Options(output.getOrElse(throw new IllegalArgumentException("output path required")), quantum, matchDelay, budget, raw, omit, expanded, matches)
  }

  def main(args: Array[String]): Unit = {
    val started = System.nanoTime()
    generate(parseArgs(args))
    println(f"finished in ${(System.nanoTime() - started) / 1e9}%.1fs")
  }
}
