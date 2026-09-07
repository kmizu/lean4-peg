package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.mutable

/** Closure check of a plain PEG file: every referenced rule is defined.
  * （Python 版: `docs/palindromes-in-peg/analysis/grammar_closure.py`。フラットな
  * `pal` パッケージに置く。）
  *
  * The file is read as bytes (Latin-1 here, one char per byte).  A rule line is one
  * containing `" = "`; string literals and character classes are blanked before names
  * are collected so their contents are not taken as rule names.
  */
object GrammarClosure {

  private val ident = "[A-Za-z_][A-Za-z0-9_]*".r
  private val literalOrClass = "\"[^\"]*\"|\\[[^\\]]*\\]".r

  /** What the script computes before printing. */
  final case class Report(rules: Int, defined: Set[String], referenced: Set[String]) {
    def missing: Set[String] = referenced -- defined
    def unusedDefs: Set[String] = defined -- referenced - "S"

    /** The two lines the Python script prints. */
    def text: String = {
      s"rules=$rules defined=${defined.size} referenced=${referenced.size} MISSING=${missing.size} unused_defs=${unusedDefs.size}\n" +
        s"missing sample: ${PyFormat.listRepr(missing.toVector.sorted.take(10).map(PyFormat.bytesRepr))}\n"
    }
  }

  /** Python's `bytes.strip()` on ASCII whitespace. */
  private def stripAscii(s: String): String = s.trim

  def analyze(lines: Iterator[String]): Report = {
    val defined = mutable.Set.empty[String]
    val referenced = mutable.Set.empty[String]
    var nrules = 0
    lines.foreach { line =>
      val split = line.indexOf(" = ")
      if (split >= 0) {
        val name = line.substring(0, split)
        val body = line.substring(split + 3)
        defined += stripAscii(name)
        nrules += 1
        val cleaned = literalOrClass.replaceAllIn(body, " ")
        referenced ++= ident.findAllIn(cleaned)
      }
    }
    Report(nrules, defined.toSet, referenced.toSet)
  }

  def analyzeFile(path: Path): Report = {
    val text = new String(Files.readAllBytes(path), StandardCharsets.ISO_8859_1)
    analyze(text.split('\n').iterator) // Python iterates a binary file on '\n' only
  }

  def main(args: Array[String]): Unit = {
    print(analyzeFile(Path.of(args(0))).text)
  }
}
