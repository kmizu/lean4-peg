package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import scala.collection.immutable.VectorMap

import FppFinite.*
import FppFinite.Instruction.*

/** The checked-in finite controller tables `docs/palindromes-in-peg/generated/<name>-controller.json`.
  *
  * Python 側にはこれらを書き出すスクリプトは残っていない（対話的に `json.dump` された）。
  * ここでは各表を「純粋関数 → 文字列」として再構成し、`main` がファイルに書く。テストは
  * ゴールデンとのバイト一致を検査する（`ControllerArtifactsSuite`）。
  *
  * 注意: `fpp_reuse.make_reusable` は Python の `set` を反復するので、その部分の状態番号と
  * 分岐表のキー順はゴールデンが書かれた時の `PYTHONHASHSEED` に依存する。dp-search 系の
  * 4 表は同じ順序（`SEARCH_BODY_ORDER`）、move-center は別の順序（`MOVE_CENTER_BODY_ORDER`）で
  * 書かれている。ここではその順序を明示的に渡して同じバイト列を再現する。したがって
  * ゴールデンの規範的な生成器は Python ではなくこの object である。既定順序
  * （`FppReuse.defaultBodySymbols`）で組んだ制御器がゴールデンと同じ挙動をすることは
  * `ControllerArtifactsSuite` が実行トレース（歩数・ヘッド位置・全テープ内容）で確認する。
  */
object ControllerArtifacts {

  val CONTRACT: String = "Finite research component; see FPP_CALLING_CONVENTION.md for input, " +
    "readiness, cancellation and scheduling boundaries. Not a PAL recognizer."

  /** Historical order of `set(("a","b","s","#")) | {"$","_","0","1"}` embedded in
    * `dp-search`, `dp-search-reusable`, `chain-monitor` and `chain-monitor-reusable`.
    *
    * Verified (2026-09-07): it is exactly the iteration order under `PYTHONHASHSEED=0`, i.e. with hash
    * randomisation disabled; no seed in 1..3999 gives it. With it, all four tables are reproduced
    * byte for byte.
    */
  val SEARCH_BODY_ORDER: Seq[String] = Seq("#", "s", "b", "0", "_", "a", "1", "$")

  /** Historical order of the same set embedded in `move-center-controller.json`.
    *
    * No `PYTHONHASHSEED` in 0..3999 iterates the set this way (checked 2026-09-07); the file was
    * written by an unrecorded process. The order is kept only to reproduce that file byte for
    * byte; `ControllerArtifactsSuite` shows the default order builds a behaviourally identical
    * controller.
    */
  val MOVE_CENTER_BODY_ORDER: Seq[String] = Seq("s", "1", "$", "#", "_", "a", "b", "0")

  val TAPE_NAMES: Vector[String] = Vector("A", "B", "C", "S", "T", "BACK", "FRONT")

  // ---------------------------------------------------------------- encoding

  def instructionJson(row: Instruction): Json = row match {
    case Halt => Json.arr(Json.Str("halt"))
    case Emit(next) => Json.arr(Json.Str("emit"), Json.Num(next))
    case Move(tape, direction, next) => Json.arr(Json.Str("move"), Json.Num(tape), Json.Num(direction), Json.Num(next))
    case Write(tape, symbol, next) => Json.arr(Json.Str("write"), Json.Num(tape), Json.Str(symbol), Json.Num(next))
    case Read(tape, choices) =>
      Json.arr(Json.Str("read"), Json.Num(tape), Json.Obj(choices.toVector.map { case (k, v) => k -> Json.Num(v) }))
  }

  def codeJson(p: Program): Json = Json.Arr(p.instructions.map(instructionJson))

  private def stateKeyed(entries: Iterable[(Int, Int)]): Json =
    Json.Obj(entries.toVector.map { case (q, k) => q.toString -> Json.Num(k) })

  private def text(obj: Json.Obj): String = Json.dumps(obj) + "\n"

  def fppOffline(): String = {
    val p = buildProgram("ab#")
    text(Json.obj(
      "kind" -> Json.Str("offline-fpp-controller"),
      "alphabet" -> Json.strings(p.alphabet),
      "tapes" -> Json.strings(TAPE_NAMES),
      "start" -> Json.Num(p.start),
      "code" -> codeJson(p),
      "note" -> Json.Str("Offline preloaded inputs; emit reports A position externally. " +
        "Not a PAL PEG or real-time recognizer.")))
  }

  def fppMarked(): String = {
    val p = FppSubroutine.buildMarkedProgram("ab")
    text(Json.obj(
      "kind" -> Json.Str("fpp-marked-controller"),
      "ntapes" -> Json.Num(p.ntapes),
      "alphabet" -> Json.strings(p.alphabet),
      "source_alphabet" -> Json.strings(p.sourceAlphabet),
      "start" -> Json.Num(p.start),
      "code" -> codeJson(p),
      "contract" -> Json.Str("Fresh work tapes; source ^word$ on tape 7, heads at 0. " +
        "Offline only; not PAL PEG. Result ^bits$ on tape 8.")))
  }

  def dpPlace(): String = {
    val p = DpFinite.buildDpProgram("abs")
    text(Json.obj(
      "kind" -> Json.Str("dp-place-controller"),
      "ntapes" -> Json.Num(p.ntapes),
      "alphabet" -> Json.strings(p.alphabet),
      "source_alphabet" -> Json.strings(p.sourceAlphabet),
      "start" -> Json.Num(p.start),
      "code" -> codeJson(p),
      "contract" -> Json.Str("Fresh work tapes; source ^word$ on tape 7, heads at 0. Offline only; " +
        "not PAL PEG. Unary ^1^lower$ on tape 10; result unary on tape 11."),
      "found" -> Json.Num(p.found.get)))
  }

  private def header(p: Program): Vector[(String, Json)] = Vector(
    "alphabet" -> Json.strings(p.alphabet),
    "ntapes" -> Json.Num(p.ntapes),
    "source_alphabet" -> Json.strings(p.sourceAlphabet),
    "start" -> Json.Num(p.start),
    "found" -> Json.Num(p.found.get),
    "missed" -> Json.Num(p.missed.get),
    "code" -> codeJson(p))

  private def chainLabels(p: Program): Vector[(String, Json)] = Vector(
    "ready" -> Json.ints(p.ready.toVector.sorted),
    "confirmed_ready" -> Json.ints(p.confirmedReady.toVector.sorted),
    "outcomes" -> Json.Obj(p.outcomes.toVector.map { case (q, name) => q.toString -> Json.Str(name) }))

  private def cancellationLabels(p: Program): Vector[(String, Json)] = Vector(
    "cleanup" -> Json.Num(p.cleanup.get),
    "scratch" -> Json.ints(p.scratch),
    "cancel_entries" -> stateKeyed(p.cancelEntries),
    "scalar_tapes" -> Json.ints(p.scalarTapes.get),
    "distance" -> Json.Num(p.distance.get))

  def dpSearch(): String = {
    val p = DpSearchFinite.buildSearchProgram("abs", Some(SEARCH_BODY_ORDER))
    text(Json.Obj(header(p) :+ ("contract" -> Json.Str(
      "Offline dp(C,r): WINDOW ^prefix suffix$ with center-tagged last prefix cell and head there; " +
        "LOWER ^1^r$ at origin; all other tapes blank at origin. Success marks four semiperiod " +
        "positions and returns unary h; no real-time scheduler."))))
  }

  def dpSearchReusable(): String = {
    val p = DpSearchReuse.makeCancellable(DpSearchFinite.buildSearchProgram("abs", Some(SEARCH_BODY_ORDER)))
    text(Json.Obj(header(p) ++ cancellationLabels(p) :+ ("contract" -> Json.Str(CONTRACT))))
  }

  def chainMonitor(): String = {
    val p = ChainFinite.buildChainProgram("abs", Some(SEARCH_BODY_ORDER))
    text(Json.Obj(header(p) ++ chainLabels(p) :+ ("scalar_tapes" -> Json.ints(p.scalarTapes.get))
      :+ ("contract" -> Json.Str(CONTRACT))))
  }

  def chainMonitorReusable(): String = {
    val p = DpSearchReuse.makeCancellable(ChainFinite.buildChainProgram("abs", Some(SEARCH_BODY_ORDER)))
    text(Json.Obj(header(p) ++ chainLabels(p) ++ cancellationLabels(p) :+ ("contract" -> Json.Str(CONTRACT))))
  }

  def moveCenter(): String = {
    val p = MoveCenterFinite.buildMoveCenterProgram("abs", Some(MOVE_CENTER_BODY_ORDER))
    text(Json.obj(
      "alphabet" -> Json.strings(p.alphabet),
      "source_alphabet" -> Json.strings(p.sourceAlphabet),
      "ntapes" -> Json.Num(p.ntapes),
      "code" -> codeJson(p),
      "start" -> Json.Num(p.start),
      "finished" -> Json.Num(p.finished.get),
      "contract" -> Json.Str("Local longest odd palindrome suffix center; WINDOW begins at marked " +
        "right boundary; scratch blank on entry and return; no cancellation or main1 replay.")))
  }

  /** Artifact name (without `-controller.json`) -> generator. */
  val all: VectorMap[String, () => String] = VectorMap(
    "fpp-offline" -> (() => fppOffline()),
    "fpp-marked" -> (() => fppMarked()),
    "dp-place" -> (() => dpPlace()),
    "dp-search" -> (() => dpSearch()),
    "dp-search-reusable" -> (() => dpSearchReusable()),
    "chain-monitor" -> (() => chainMonitor()),
    "chain-monitor-reusable" -> (() => chainMonitorReusable()),
    "move-center" -> (() => moveCenter()))

  /** `docs/palindromes-in-peg/generated`, found by walking up from the working directory
    * (sbt runs with `scala/` as cwd; the same discovery as the test-side `PyDiff.pyDir`).
    */
  def defaultOutputDir: Path = {
    val here = Paths.get("").toAbsolutePath
    Iterator
      .iterate(here)(_.getParent)
      .takeWhile(_ != null)
      .map(_.resolve("docs/palindromes-in-peg/generated"))
      .find(Files.isDirectory(_))
      .getOrElse(throw new IllegalStateException(s"docs/palindromes-in-peg/generated not found above $here"))
  }

  /** `ControllerArtifacts [outputDir] [name...]`: write the tables (default: all, into `defaultOutputDir`). */
  def main(args: Array[String]): Unit = {
    val dir = args.headOption.map(Paths.get(_)).getOrElse(defaultOutputDir)
    val names = if (args.length > 1) { args.drop(1).toSeq } else { all.keys.toSeq }
    for (name <- names) {
      val generate = all.getOrElse(name, throw new IllegalArgumentException(s"unknown artifact $name"))
      val target = dir.resolve(s"$name-controller.json")
      Files.write(target, generate().getBytes(StandardCharsets.UTF_8))
      println(s"wrote $target")
    }
  }

  // ---------------------------------------------------------------- decoding

  private def int(json: Json): Int = json match {
    case Json.Num(n) => n.toInt
    case other => throw new IllegalArgumentException(s"expected a number, got $other")
  }

  private def str(json: Json): String = json match {
    case Json.Str(s) => s
    case other => throw new IllegalArgumentException(s"expected a string, got $other")
  }

  private def ints(json: Json): Vector[Int] = json match {
    case Json.Arr(items) => items.map(int)
    case other => throw new IllegalArgumentException(s"expected an array, got $other")
  }

  private def strings(json: Json): Vector[String] = json match {
    case Json.Arr(items) => items.map(str)
    case other => throw new IllegalArgumentException(s"expected an array, got $other")
  }

  def instructionFromJson(json: Json): Instruction = json match {
    case Json.Arr(Vector(Json.Str("halt"))) => Halt
    case Json.Arr(Vector(Json.Str("emit"), next)) => Emit(int(next))
    case Json.Arr(Vector(Json.Str("move"), tape, direction, next)) => Move(int(tape), int(direction), int(next))
    case Json.Arr(Vector(Json.Str("write"), tape, symbol, next)) => Write(int(tape), str(symbol), int(next))
    case Json.Arr(Vector(Json.Str("read"), tape, Json.Obj(fields))) =>
      Read(int(tape), VectorMap.from(fields.map { case (k, v) => k -> int(v) }))
    case other => throw new IllegalArgumentException(s"not an instruction: $other")
  }

  /** Rebuild a `Program` from a saved table, setting every label the file carries. */
  def load(obj: Json.Obj): Program = {
    val ntapes = obj.get("ntapes").map(int).getOrElse(7)
    val p = new Program(strings(obj("alphabet")), ntapes)
    p.code ++= (obj("code") match {
      case Json.Arr(rows) => rows.map(row => Some(instructionFromJson(row)))
      case other => throw new IllegalArgumentException(s"expected code array, got $other")
    })
    p.start = int(obj("start"))
    obj.get("source_alphabet").foreach(v => p.sourceAlphabet = strings(v))
    obj.get("found").foreach(v => p.found = Some(int(v)))
    obj.get("missed").foreach(v => p.missed = Some(int(v)))
    obj.get("cleanup").foreach(v => p.cleanup = Some(int(v)))
    obj.get("finished").foreach(v => p.finished = Some(int(v)))
    obj.get("distance").foreach(v => p.distance = Some(int(v)))
    obj.get("scratch").foreach(v => p.scratch = ints(v))
    obj.get("scalar_tapes").foreach(v => p.scalarTapes = Some(ints(v)))
    obj.get("ready").foreach(v => p.ready = ints(v).toSet)
    obj.get("confirmed_ready").foreach(v => p.confirmedReady = ints(v).toSet)
    obj.get("cancel_entries").foreach {
      case Json.Obj(fields) => fields.foreach { case (q, k) => p.cancelEntries(q.toInt) = int(k) }
      case other => throw new IllegalArgumentException(s"expected cancel_entries object, got $other")
    }
    obj.get("outcomes").foreach {
      case Json.Obj(fields) => fields.foreach { case (q, name) => p.outcomes(q.toInt) = str(name) }
      case other => throw new IllegalArgumentException(s"expected outcomes object, got $other")
    }
    p
  }

  def load(text: String): Program = Json.parse(text) match {
    case obj: Json.Obj => load(obj)
    case other => throw new IllegalArgumentException(s"expected a JSON object, got ${other.getClass.getSimpleName}")
  }
}
