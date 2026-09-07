package pal

import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, StandardOpenOption}
import scala.collection.mutable

/** Match a large, concrete PEG file without parsing every unused rule first.
  *
  * The file contains one complete ordinary PEG production per line, as emitted by
  * our converters. Only loading is lazy: rule bodies are parsed from those bytes
  * and executed by the same PEG evaluator. No machine simulator or PAL predicate
  * is involved in matching.
  *
  * Port of `peg_file.py`.
  */

/** Rule table that parses a production from the mapped file on first `apply`.
  *
  * Like the Python `dict` subclass with `__missing__`: `apply(name)` loads and
  * caches, while `get`, `contains`, `size` and iteration see only the rules
  * loaded so far.
  */
final class RuleMap(data: ByteBuffer, offsets: Map[String, Int]) extends mutable.AbstractMap[String, PegAst] {
  private val loaded = mutable.LinkedHashMap.empty[String, PegAst]

  override def default(name: String): PegAst = {
    val start = offsets.getOrElse(name, throw new NoSuchElementException(name))
    var end = start
    while (end < data.limit() && data.get(end) != '\n'.toByte) { end += 1 }
    val bytes = new Array[Byte](end - start)
    data.duplicate().position(start).get(bytes)
    val rules = Grammar.parseRules(new String(bytes, StandardCharsets.UTF_8), name)
    if (rules.size != 1) { throw new IllegalArgumentException("one complete PEG production per line required") }
    val result = rules(name)
    loaded(name) = result
    result
  }

  def get(name: String): Option[PegAst] = loaded.get(name)

  def iterator: Iterator[(String, PegAst)] = loaded.iterator

  def addOne(entry: (String, PegAst)): this.type = { loaded += entry; this }

  def subtractOne(name: String): this.type = { loaded -= name; this }

  override def size: Int = loaded.size
}

/** A grammar backed by a memory-mapped one-production-per-line file. */
final class FileGrammar private (opened: FileGrammar.Opened, start: String)
    extends Grammar(opened.rules, start)
    with AutoCloseable {

  def this(path: Path, start: String = "S") = this(FileGrammar.open(path, start), start)

  /** Number of productions indexed in the file (not the number loaded). */
  val ruleCount: Int = opened.ruleCount

  def close(): Unit = opened.channel.close()
}

object FileGrammar {
  private[pal] final class Opened(val channel: FileChannel, val rules: RuleMap, val ruleCount: Int)

  private val HEAD = "([A-Za-z_][A-Za-z_0-9]*)\\s*=".r

  private def isAsciiSpace(byte: Byte): Boolean = {
    byte == ' ' || byte == '\t' || byte == '\n' || byte == '\r' || byte == 0x0b || byte == 0x0c
  }

  /** Map the file and index the byte offset of every production head. */
  private[pal] def open(path: Path, start: String): Opened = {
    val channel = FileChannel.open(path, StandardOpenOption.READ)
    try {
      val size = channel.size()
      if (size > Int.MaxValue) { throw new IllegalArgumentException("PEG file larger than 2 GiB is not supported") }
      val data = channel.map(FileChannel.MapMode.READ_ONLY, 0, size)
      val offsets = index(data, size.toInt)
      if (!offsets.contains(start)) { throw new IllegalArgumentException(s"unknown start rule: $start") }
      new Opened(channel, new RuleMap(data, offsets), offsets.size)
    } catch {
      case error: Throwable =>
        channel.close()
        throw error
    }
  }

  private def index(data: ByteBuffer, length: Int): Map[String, Int] = {
    val offsets = mutable.LinkedHashMap.empty[String, Int]
    var position = 0
    while (position < length) {
      var end = position
      while (end < length && data.get(end) != '\n'.toByte) { end += 1 }
      if (end < length) { end += 1 }
      var first = position
      while (first < end && isAsciiSpace(data.get(first))) { first += 1 }
      if (first < end) {
        val head = headOf(data, first, end)
        val name = HEAD.findPrefixMatchOf(head).map(_.group(1))
          .getOrElse(throw new IllegalArgumentException("one complete PEG production per line required"))
        if (offsets.contains(name)) { throw new IllegalArgumentException("duplicate rule") }
        offsets(name) = position
      }
      position = end
    }
    offsets.toMap
  }

  /** The line's leading bytes as ASCII, enough to match the production head. */
  private def headOf(data: ByteBuffer, first: Int, end: Int): String = {
    val bytes = new Array[Byte](end - first)
    data.duplicate().position(first).get(bytes)
    new String(bytes, StandardCharsets.ISO_8859_1)
  }
}
