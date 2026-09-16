package pal

import java.nio.file.Path
import java.util.Arrays

import GrammarTools.{ByteLines, StringIndex}

/** Closure check of a plain PEG file: every referenced rule is defined.
  * （Python 版: `docs/palindromes-in-peg/analysis/grammar_closure.py`。フラットな
  * `pal` パッケージに置く。）
  *
  * The file is streamed as bytes (Latin-1 here, one char per byte), never loaded whole.
  * A rule line is one containing `" = "`; string literals and character classes are
  * blanked before names are collected so their contents are not taken as rule names.
  * Python keeps two sets (`defined`, `referenced`); here one name table carries a flag
  * per name, so the 13.2M names of the real grammar are stored once.
  */
object GrammarClosure {

  private val ident = "[A-Za-z_][A-Za-z0-9_]*".r
  private val literalOrClass = "\"[^\"]*\"|\\[[^\\]]*\\]".r

  /** What the script computes before printing: the counts, and the offending names
    * (sorted, as `sorted(missing)`).
    */
  final case class Report(rules: Int, defined: Int, referenced: Int, missing: Vector[String], unused: Vector[String]) {

    /** The two lines the Python script prints. */
    def text: String = {
      s"rules=$rules defined=$defined referenced=$referenced MISSING=${missing.size} unused_defs=${unused.size}\n" +
        s"missing sample: ${PyFormat.listRepr(missing.take(10).map(PyFormat.bytesRepr))}\n"
    }
  }

  private val DEFINED: Byte = 1
  private val REFERENCED: Byte = 2

  /** Accumulates `defined` / `referenced` as flags on one name table. */
  private final class Collector {
    private val index = new StringIndex()
    private var flags = new Array[Byte](1 << 16)
    private var rules = 0

    private def mark(name: String, flag: Byte): Unit = {
      val id = index.intern(name)
      if (id >= flags.length) { flags = Arrays.copyOf(flags, math.max(id + 1, flags.length + (flags.length >> 2))) }
      flags(id) = (flags(id) | flag).toByte
    }

    def line(line: String): Unit = {
      val split = line.indexOf(" = ")
      if (split >= 0) {
        mark(line.substring(0, split).trim, DEFINED)
        rules += 1
        // strip string literals and char classes so their contents are not taken as names
        val body = literalOrClass.replaceAllIn(line.substring(split + 3), " ")
        ident.findAllIn(body).foreach(name => mark(name, REFERENCED))
      }
    }

    def report: Report = {
      var defined = 0
      var referenced = 0
      val missing = Vector.newBuilder[String]
      val unused = Vector.newBuilder[String]
      var id = 0
      while (id < index.size) {
        val f = flags(id)
        if ((f & DEFINED) != 0) { defined += 1 }
        if ((f & REFERENCED) != 0) { referenced += 1 }
        if (f == REFERENCED) { missing += index.name(id) }
        if (f == DEFINED && index.name(id) != "S") { unused += index.name(id) }
        id += 1
      }
      Report(rules, defined, referenced, missing.result().sorted, unused.result().sorted)
    }
  }

  def analyze(lines: Iterator[String]): Report = {
    val collector = new Collector
    lines.foreach(collector.line)
    collector.report
  }

  /** Streams the file line by line (`for line in open(path, 'rb')`). */
  def analyzeFile(path: Path): Report = {
    val collector = new Collector
    ByteLines.foreach(path)(collector.line)
    collector.report
  }

  def main(args: Array[String]): Unit = {
    print(analyzeFile(Path.of(args(0))).text)
  }
}
