package pal

import scala.collection.mutable

/** 最小限の JSON 値と、Python の `json.dumps(obj, indent=2)` とバイト一致する整形器。
  *
  * 依存を増やさないための自前実装。controller 表の再生成（`ControllerArtifacts`）と、
  * テストが checked-in の表を読み込んで実行するための構文解析だけを扱う。
  * オブジェクトのキー順は挿入順（Python の dict と同じ）。
  */
sealed trait Json

object Json {
  final case class Str(value: String) extends Json
  final case class Num(value: Long) extends Json
  final case class Bool(value: Boolean) extends Json
  case object Null extends Json
  final case class Arr(items: Vector[Json]) extends Json
  /** キー順を保つオブジェクト。 */
  final case class Obj(fields: Vector[(String, Json)]) extends Json {
    def apply(key: String): Json = fields.collectFirst { case (k, v) if k == key => v }
      .getOrElse(throw new NoSuchElementException(s"missing JSON key: $key"))
    def get(key: String): Option[Json] = fields.collectFirst { case (k, v) if k == key => v }
    def has(key: String): Boolean = fields.exists(_._1 == key)
  }

  def obj(fields: (String, Json)*): Obj = Obj(fields.toVector)
  def arr(items: Json*): Arr = Arr(items.toVector)
  def ints(values: Iterable[Int]): Arr = Arr(values.iterator.map(v => Num(v.toLong)).toVector)
  def strings(values: Iterable[String]): Arr = Arr(values.iterator.map(Str.apply).toVector)

  /** `json.dumps(value, indent=2)` と同じ文字列（末尾改行なし）。 */
  def dumps(value: Json): String = {
    val out = new StringBuilder
    write(out, value, 0)
    out.toString
  }

  private def write(out: StringBuilder, value: Json, depth: Int): Unit = {
    value match {
      case Str(s) => writeString(out, s)
      case Num(n) => out.append(n)
      case Bool(b) => out.append(if (b) "true" else "false")
      case Null => out.append("null")
      case Arr(items) =>
        if (items.isEmpty) {
          out.append("[]")
        } else {
          out.append("[")
          var first = true
          for (item <- items) {
            if (!first) { out.append(",") }
            first = false
            newline(out, depth + 1)
            write(out, item, depth + 1)
          }
          newline(out, depth)
          out.append("]")
        }
      case Obj(fields) =>
        if (fields.isEmpty) {
          out.append("{}")
        } else {
          out.append("{")
          var first = true
          for ((k, v) <- fields) {
            if (!first) { out.append(",") }
            first = false
            newline(out, depth + 1)
            writeString(out, k)
            out.append(": ")
            write(out, v, depth + 1)
          }
          newline(out, depth)
          out.append("}")
        }
    }
  }

  private def newline(out: StringBuilder, depth: Int): Unit = {
    out.append("\n")
    var i = 0
    while (i < depth) {
      out.append("  ")
      i += 1
    }
  }

  /** Python の既定 `ensure_ascii=True` と同じエスケープ。 */
  private def writeString(out: StringBuilder, s: String): Unit = {
    out.append('"')
    for (c <- s) {
      c match {
        case '"' => out.append("\\\"")
        case '\\' => out.append("\\\\")
        case '\n' => out.append("\\n")
        case '\r' => out.append("\\r")
        case '\t' => out.append("\\t")
        case '\b' => out.append("\\b")
        case '\f' => out.append("\\f")
        case _ if c < 0x20 || c > 0x7e => out.append(f"\\u${c.toInt}%04x")
        case _ => out.append(c)
      }
    }
    out.append('"')
  }

  /** 素朴な再帰下降の構文解析器（テストがゴールデン表を読むためのもの）。 */
  def parse(text: String): Json = {
    val parser = new Parser(text)
    val value = parser.value()
    parser.skipSpace()
    if (!parser.atEnd) { throw new IllegalArgumentException(s"trailing JSON at ${parser.pos}") }
    value
  }

  private final class Parser(text: String) {
    var pos: Int = 0

    def atEnd: Boolean = pos >= text.length

    def skipSpace(): Unit = {
      while (!atEnd && Character.isWhitespace(text.charAt(pos))) { pos += 1 }
    }

    private def expect(c: Char): Unit = {
      skipSpace()
      if (atEnd || text.charAt(pos) != c) {
        throw new IllegalArgumentException(s"expected '$c' at $pos")
      }
      pos += 1
    }

    def value(): Json = {
      skipSpace()
      if (atEnd) { throw new IllegalArgumentException("unexpected end of JSON") }
      text.charAt(pos) match {
        case '{' => obj()
        case '[' => arr()
        case '"' => Str(string())
        case 't' => literal("true", Bool(true))
        case 'f' => literal("false", Bool(false))
        case 'n' => literal("null", Null)
        case _ => number()
      }
    }

    private def literal(word: String, result: Json): Json = {
      if (!text.startsWith(word, pos)) { throw new IllegalArgumentException(s"bad literal at $pos") }
      pos += word.length
      result
    }

    private def number(): Json = {
      val start = pos
      if (text.charAt(pos) == '-') { pos += 1 }
      while (!atEnd && Character.isDigit(text.charAt(pos))) { pos += 1 }
      if (start == pos) { throw new IllegalArgumentException(s"bad JSON value at $pos") }
      Num(text.substring(start, pos).toLong)
    }

    private def string(): String = {
      expect('"')
      val out = new StringBuilder
      while (text.charAt(pos) != '"') {
        val c = text.charAt(pos)
        if (c == '\\') {
          val e = text.charAt(pos + 1)
          pos += 2
          e match {
            case '"' => out.append('"')
            case '\\' => out.append('\\')
            case '/' => out.append('/')
            case 'n' => out.append('\n')
            case 'r' => out.append('\r')
            case 't' => out.append('\t')
            case 'b' => out.append('\b')
            case 'f' => out.append('\f')
            case 'u' =>
              out.append(Integer.parseInt(text.substring(pos, pos + 4), 16).toChar)
              pos += 4
            case other => throw new IllegalArgumentException(s"bad escape \\$other")
          }
        } else {
          out.append(c)
          pos += 1
        }
      }
      pos += 1
      out.toString
    }

    private def arr(): Json = {
      expect('[')
      val items = mutable.ArrayBuffer.empty[Json]
      skipSpace()
      if (text.charAt(pos) == ']') {
        pos += 1
      } else {
        var more = true
        while (more) {
          items += value()
          skipSpace()
          if (text.charAt(pos) == ',') { pos += 1 } else { expect(']'); more = false }
        }
      }
      Arr(items.toVector)
    }

    private def obj(): Json = {
      expect('{')
      val fields = mutable.ArrayBuffer.empty[(String, Json)]
      skipSpace()
      if (text.charAt(pos) == '}') {
        pos += 1
      } else {
        var more = true
        while (more) {
          skipSpace()
          val key = string()
          expect(':')
          fields += ((key, value()))
          skipSpace()
          if (text.charAt(pos) == ',') { pos += 1 } else { expect('}'); more = false }
        }
      }
      Obj(fields.toVector)
    }
  }
}
