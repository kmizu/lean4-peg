package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.immutable.VectorMap

/** Emit the complete windowed PAL source as an ordinary binary PEG. */
object GenerateWindowPal {
  final case class Options(output: Path, checkpoint: Option[Path] = None, resume: Option[Path] = None,
                           skipOptimize: Boolean = true)

  private val metadata: VectorMap[String, Any] = VectorMap(
    "kind" -> "window-pal", "k" -> GsBatchClock.DEFAULT_BATCH.k,
    "matching" -> GsBatchClock.DEFAULT_BATCH.matching, "flags" -> GsBatchClock.DEFAULT_BATCH.flags)

  def parse(args: Array[String]): Options = {
    var output: Option[Path] = None
    var checkpoint: Option[Path] = None
    var resume: Option[Path] = None
    var rewriting: Option[Boolean] = None
    var index = 0
    while (index < args.length) {
      args(index) match {
        case "--checkpoint" | "--resume" if index + 1 >= args.length =>
          throw new IllegalArgumentException(args(index) + " requires a path")
        case "--checkpoint" => checkpoint = Some(Path.of(args(index + 1))); index += 2
        case "--resume" => resume = Some(Path.of(args(index + 1))); index += 2
        case "--optimize" =>
          if (rewriting.contains(true)) { throw new IllegalArgumentException("--optimize conflicts with --skip-optimize") }
          rewriting = Some(false)
          index += 1
        case "--skip-optimize" =>
          if (rewriting.contains(false)) { throw new IllegalArgumentException("--skip-optimize conflicts with --optimize") }
          rewriting = Some(true)
          index += 1
        case option if option.startsWith("-") => throw new IllegalArgumentException("unknown option: " + option)
        case path if output.isEmpty => output = Some(Path.of(path)); index += 1
        case path => throw new IllegalArgumentException("unexpected argument: " + path)
      }
    }
    Options(output.getOrElse(throw new IllegalArgumentException("output path is required")), checkpoint, resume,
      rewriting.getOrElse(true))
  }

  private def elapsed(started: Long): Double = (System.nanoTime() - started).toDouble / 1000000000.0
  private def jsonString(value: String): String = "\"" + value.flatMap {
    case '\\' => "\\\\"
    case '"' => "\\\""
    case '\n' => "\\n"
    case '\r' => "\\r"
    case '\t' => "\\t"
    case c => c.toString
  } + "\""
  private def report(fields: (String, Any)*): Unit = {
    println(fields.map { case (key, value) =>
      val rendered = value match {
        case text: String => jsonString(text)
        case path: Path => jsonString(path.toString)
        case other => other.toString
      }
      jsonString(key) + ": " + rendered
    }.mkString("{", ", ", "}"))
  }

  def run(options: Options, sourceBuilder: () => Scaffold = () => Expr.share { ScaffoldWindowPal.build()._3 }): Unit = {
    val started = System.nanoTime()
    val machine0 = options.resume match {
      case Some(path) =>
        val (machine, savedMetadata) = ScaffoldArtifact.read(path)
        if (savedMetadata != metadata) {
          throw new IllegalArgumentException("checkpoint is not the complete default window PAL source")
        }
        machine
      case None => sourceBuilder()
    }
    report("phase" -> "built", "seconds" -> elapsed(started),
      "labels" -> machine0.labels.size, "pointers" -> machine0.pointers.size)
    options.checkpoint.foreach { path =>
      val nodes = ScaffoldArtifact.write(machine0, path, metadata)
      report("phase" -> "checkpointed", "file" -> path, "nodes" -> nodes, "seconds" -> elapsed(started))
    }
    val machine = if (options.skipOptimize) { machine0 } else {
      val (optimized, stats) = ScaffoldOptimize.optimize(machine0)
      report("phase" -> "optimized", "seconds" -> elapsed(started),
        "rounds" -> stats.rounds, "constant_labels" -> stats.constantLabels,
        "null_pointers" -> stats.nullPointers, "labels_removed" -> stats.labelsRemoved,
        "pointers_removed" -> stats.pointersRemoved)
      optimized
    }
    val writer = Files.newBufferedWriter(options.output, StandardCharsets.UTF_8)
    var count = 0
    try {
      machine.iterRules().foreach { rule => writer.write(rule); writer.newLine(); count += 1 }
    } finally {
      writer.close()
    }
    report("phase" -> "emitted", "file" -> options.output, "rules" -> count,
      "bytes" -> Files.size(options.output), "seconds" -> elapsed(started),
      "matching" -> GsBatchClock.DEFAULT_BATCH.matching, "flags" -> GsBatchClock.DEFAULT_BATCH.flags)
  }

  def main(args: Array[String]): Unit = run(parse(args))
}
