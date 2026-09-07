package pal

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption}
import java.security.MessageDigest
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference
import scala.collection.immutable.VectorMap
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** Generate the FIFO/whole-round PAL candidate on original input.
  * No recognition budget, input expansion or word-length cap is accepted.
  * The output is replaced only after all ordinary PEG rules have been emitted.
  * Correctness remains subject to TRANSLATION_STRATEGY.md's source contracts.
  *
  * Port of `generate_online_peg.py`. The `.sca` representation remains
  * interoperable through [[ScaffoldArtifact]], but automatic generator-cache
  * reuse is language-specific because its signature covers Scala sources.
  */
object GenerateOnlinePeg {
  type Report = mutable.LinkedHashMap[String, Any]
  final case class Source(machine: Scaffold, ready: String, event: String)

  /** Construction hooks permit a tiny independent source in differential tests. */
  final case class Backend(
      signature: () => String = () => sourceSignature(),
      build: (Int, Boolean) => Source = (quantum, shared) => {
        val (circuit, machine) = ScaffoldCircuitGalil.buildOnline(quantum, sharedCells = shared)
        Source(machine, circuit.labelIds(("online.ready", 0)), circuit.labelIds(("online.event", 0)))
      },
      pack: (Scaffold, Int, Boolean) => Scaffold = (wrapper, service, lazyRound) =>
        ScaffoldEventBuffer.packService(wrapper, service, lazyRound)
  )

  def sourceSignature(sourceRoot: Path = scalaSourceDirectory()): String = {
    val digest = MessageDigest.getInstance("SHA-256")
    digest.update("lean4-peg/generate-online-peg/scala/v1\u0000".getBytes(UTF_8))
    val stream = Files.list(sourceRoot)
    val paths = try { stream.iterator().asScala.filter(_.getFileName.toString.endsWith(".scala")).toVector
      .sortBy(_.getFileName.toString) } finally { stream.close() }
    for (path <- paths) {
      digest.update(path.getFileName.toString.getBytes(UTF_8))
      digest.update(0.toByte)
      digest.update(Files.readAllBytes(path))
      digest.update(0.toByte)
    }
    digest.digest().map(byte => f"${byte & 0xff}%02x").mkString
  }

  private def scalaSourceDirectory(): Path = {
    val pythonRoot = GenerateScaffoldExamples.locateDirectory(Array.empty)
    val sourceRoot = pythonRoot.resolve("../../scala/pal/src/main/scala/pal").normalize()
    if (!Files.isDirectory(sourceRoot)) {
      throw new IllegalStateException(s"Scala source directory unavailable for cache provenance: $sourceRoot")
    }
    sourceRoot
  }

  private def timingFields(timing: GalilClock.Timing): VectorMap[String, Any] = {
    VectorMap("quantum" -> timing.quantum, "stage_factor" -> timing.stageFactor,
      "match_delay" -> timing.matchDelay, "move_slope" -> timing.moveSlope,
      "interval_overhead" -> timing.intervalOverhead, "predictability" -> timing.predictability)
  }

  /** Python's compact json.dumps formatting, preserving insertion order. */
  def reportJson(value: Any): String = value match {
    case entries: collection.Map[?, ?] => entries.iterator.map { case (key, item) =>
      PyFormat.jsonString(key.toString, ensureAscii = true) + ": " + reportJson(item)
    }.mkString("{", ", ", "}")
    case values: Seq[?] => values.map(reportJson).mkString("[", ", ", "]")
    case text: String => PyFormat.jsonString(text, ensureAscii = true)
    case value: Boolean => if (value) { "true" } else { "false" }
    case value: Int => value.toString
    case value: Long => value.toString
    case value: Double => PyFormat.floatRepr(value)
    case None => "null"
    case other => throw new IllegalArgumentException(s"unsupported report value: $other")
  }

  def reportPretty(value: Any, depth: Int = 0): String = {
    def collection(open: String, close: String, entries: Vector[String]): String = {
      if (entries.isEmpty) { open + close } else {
        open + "\n" + entries.map("  " * (depth + 1) + _).mkString(",\n") + "\n" + "  " * depth + close
      }
    }
    value match {
      case entries: scala.collection.Map[?, ?] =>
        collection("{", "}", entries.iterator.map { case (key, item) =>
          PyFormat.jsonString(key.toString, ensureAscii = true) + ": " + reportPretty(item, depth + 1)
        }.toVector)
      case entries: Seq[?] => collection("[", "]", entries.map(reportPretty(_, depth + 1)).toVector)
      case scalar => reportJson(scalar)
    }
  }

  def generate(output: Path, quantum: Int, report: Report, sharedCells: Boolean = false,
               wrapperCache: Option[Path] = None, wrapperOnly: Boolean = false,
               rebuildWrapper: Boolean = false, lazyRound: Boolean = false,
               backend: Backend = Backend(), progress: String => Unit = println): Unit = {
    val timing = GalilClock.derive(quantum)
    report("timing") = timingFields(timing)
    report("service") = timing.service
    report("slots") = timing.service + 1
    report("shared_cells") = sharedCells
    report("lazy_round") = lazyRound
    val fingerprint = VectorMap[String, Any]("signature" -> backend.signature(), "quantum" -> quantum, "shared_cells" -> sharedCells)
    def stage(name: String): Unit = { report("stage") = name; progress(reportJson(report)) }
    val wrapper = if (wrapperCache.exists(Files.exists(_)) && !rebuildWrapper) {
      stage("load finite FIFO artifact")
      val (cached, metadata) = ScaffoldArtifact.read(wrapperCache.get)
      if (metadata != fingerprint) {
        throw new IllegalArgumentException("FIFO artifact differs from this source; use --rebuild-wrapper or another path")
      }
      cached
    } else {
      stage("online source")
      val source = Expr.share { backend.build(quantum, sharedCells) }
      report("source") = VectorMap("labels" -> source.machine.labels.size, "pointers" -> source.machine.pointers.size)
      stage("finite FIFO wrapper")
      val (_, buffered) = Expr.share {
        ScaffoldEventBuffer.bufferSource(source.machine, source.ready, source.event, source.machine.accepting)
      }
      wrapperCache.foreach { path =>
        stage("save finite FIFO artifact")
        report("artifact_nodes") = ScaffoldArtifact.write(buffered, path, fingerprint)
      }
      buffered
    }
    report("wrapper") = VectorMap("labels" -> wrapper.labels.size, "pointers" -> wrapper.pointers.size)
    if (wrapperOnly) {
      report("stage") = "finite FIFO artifact saved"
      report("artifact") = wrapperCache.fold("None")(_.toString)
      report("emitted") = false
    } else {
      stage("whole input round")
      val packed = Expr.share { backend.pack(wrapper, timing.service, lazyRound) }
      report("packed") = VectorMap("labels" -> packed.labels.size, "pointers" -> packed.pointers.size)
      stage("ordinary PEG emission")
      val temporary = output.resolveSibling(output.getFileName.toString + ".partial")
      val stream = Files.newBufferedWriter(temporary, UTF_8)
      var count = 0L
      try {
        for (rule <- packed.iterRules()) { stream.write(rule); stream.write("\n"); count += 1 }
      } finally { stream.close() }
      Files.move(temporary, output, StandardCopyOption.REPLACE_EXISTING)
      report("stage") = "emitted"
      report("rules") = count
      report("bytes") = Files.size(output)
      report("output") = output.toString
      report("emitted") = true
      report("raw_input_matches") = "not run"
    }
  }

  final case class Options(output: Path, quantum: Int = 64, memoryMib: Int = 16384,
                           report: Option[Path] = None, sharedCells: Boolean = false,
                           wrapperCache: Option[Path] = None, wrapperOnly: Boolean = false,
                           rebuildWrapper: Boolean = false, lazyRound: Boolean = false)

  def parseArgs(args: Array[String]): Options = {
    var output: Option[Path] = None
    var quantum = 64
    var memoryMib = 16384
    var report: Option[Path] = None
    var shared = false
    var cache: Option[Path] = None
    var only = false
    var rebuild = false
    var lazyRound = false
    var index = 0
    def argument(flag: String): String = {
      index += 1
      if (index >= args.length) { throw new IllegalArgumentException(s"$flag requires a value") }
      args(index)
    }
    while (index < args.length) {
      args(index) match {
        case "--quantum" => quantum = argument("--quantum").toInt
        case "--memory-mib" => memoryMib = argument("--memory-mib").toInt
        case "--report" => report = Some(Path.of(argument("--report")))
        case "--shared-instruction-cells" => shared = true
        case "--wrapper-cache" => cache = Some(Path.of(argument("--wrapper-cache")))
        case "--wrapper-only" => only = true
        case "--rebuild-wrapper" => rebuild = true
        case "--lazy-round" => lazyRound = true
        case value if !value.startsWith("-") && output.isEmpty => output = Some(Path.of(value))
        case value => throw new IllegalArgumentException(s"unrecognized argument: $value")
      }
      index += 1
    }
    if (memoryMib < 1) { throw new IllegalArgumentException("positive compilation memory limit required") }
    if (only && cache.isEmpty) { throw new IllegalArgumentException("--wrapper-only requires --wrapper-cache") }
    GalilClock.derive(quantum)
    Options(output.getOrElse(throw new IllegalArgumentException("output path required")), quantum, memoryMib, report,
      shared, cache, only, rebuild, lazyRound)
  }

  /** The JVM reserves its heap at startup: enforce --memory-mib by requiring
    * a JVM -Xmx at or below it. This caps heap, rather than Python's RLIMIT_AS.
    */
  def main(args: Array[String]): Unit = {
    if (args.contains("--help") || args.contains("-h")) {
      println("Usage: GenerateOnlinePeg OUTPUT [--quantum N] [--memory-mib N] [--report PATH]\n" +
        "  [--shared-instruction-cells] [--wrapper-cache PATH] [--wrapper-only]\n" +
        "  [--rebuild-wrapper] [--lazy-round]\n" +
        "Generate ordinary PEG rules on original input. --memory-mib requires a JVM -Xmx at or below the given MiB; it limits heap, not virtual address space.")
      return
    }
    val options = parseArgs(args)
    if (Runtime.getRuntime.maxMemory() > options.memoryMib.toLong * 1024 * 1024) {
      throw new IllegalArgumentException(s"start the JVM with -Xmx${options.memoryMib}m or less to enforce --memory-mib")
    }
    val report = mutable.LinkedHashMap.empty[String, Any]
    val started = System.nanoTime()
    val finalized = new AtomicBoolean(false)
    val published = new AtomicReference[VectorMap[String, Any]](VectorMap.empty)
    val reportLock = new Object()
    def finishReport(interrupted: Boolean): Unit = reportLock.synchronized {
      if (finalized.compareAndSet(false, true)) {
        var snapshot = if (interrupted) { published.get() } else { VectorMap.from(report) }
        if (interrupted) { snapshot = snapshot.updated("status", "compilation interrupted").updated("emitted", false) }
        snapshot = snapshot.updated("seconds", (System.nanoTime() - started) / 1e9)
        val status = Path.of("/proc/self/status")
        val peak = if (Files.isReadable(status)) {
          Files.readAllLines(status).asScala.find(_.startsWith("VmHWM:")).map(_.trim.split("\\s+")(1).toLong).getOrElse(0L)
        } else { None }
        snapshot = snapshot.updated("peak_rss_kib", peak)
        options.report.foreach(path => Files.writeString(path, reportPretty(snapshot) + "\n", UTF_8))
        println(reportJson(snapshot))
      }
    }
    // A normal JVM SIGTERM keeps its platform exit status (typically 143), but
    // this hook still publishes an interruption report from an immutable stage
    // snapshot. No internal signal API or concurrent mutable-map iteration.
    val shutdownHook = new Thread(() => finishReport(interrupted = true), "generate-online-peg-report")
    Runtime.getRuntime.addShutdownHook(shutdownHook)
    var exitCode = 0
    try {
      generate(options.output, options.quantum, report, options.sharedCells, options.wrapperCache,
        options.wrapperOnly, options.rebuildWrapper, options.lazyRound, progress = line => {
          published.set(VectorMap.from(report))
          println(line)
        })
    } catch {
      case _: OutOfMemoryError =>
        report("status") = "compilation memory limit exceeded"
        report("emitted") = false
        exitCode = 1
      case _: InterruptedException =>
        report("status") = "compilation interrupted"
        report("emitted") = false
        Thread.currentThread().interrupt()
        exitCode = 130
    } finally {
      finishReport(interrupted = false)
      try { Runtime.getRuntime.removeShutdownHook(shutdownHook) }
      catch { case _: IllegalStateException => () }
    }
    if (exitCode != 0) { sys.exit(exitCode) }
  }
}
