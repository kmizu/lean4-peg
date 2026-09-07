package pal

import java.math.{BigDecimal => JBigDecimal, RoundingMode}

/** Python の文字列整形（`f'{x:.2f}'`, `repr`, `json.dumps` の float）の再現。 */
object PyFormat {

  /** `format(x, '.<digits>f')`。Python は 2 進の正確な値を丸める（同点は偶数へ）。 */
  def fixed(x: Double, digits: Int): String = {
    new JBigDecimal(x).setScale(digits, RoundingMode.HALF_EVEN).toPlainString
  }

  /** `repr(x)` / `json.dumps(x)` for a float（最短往復桁、Python の指数表記規則）。 */
  def floatRepr(x: Double): String = {
    if (x.isNaN) { return "nan" }
    if (x.isInfinite) { return if (x > 0) "inf" else "-inf" }
    if (x == 0.0) { return if (1.0 / x < 0) "-0.0" else "0.0" }
    val sign = if (x < 0) "-" else ""
    val text = java.lang.Double.toString(math.abs(x))
    val (mantissa, exponent) = text.indexOf('E') match {
      case -1 => (text, 0)
      case i  => (text.substring(0, i), text.substring(i + 1).toInt)
    }
    val dot = mantissa.indexOf('.')
    val intPart = mantissa.substring(0, dot)
    val fracPart = mantissa.substring(dot + 1)
    val raw = intPart + fracPart
    val leading = raw.indexWhere(_ != '0')
    val digits = raw.substring(leading).reverse.dropWhile(_ == '0').reverse
    val decpt = intPart.length - leading + exponent
    val body =
      if (decpt <= -4 || decpt > 16) {
        val exp = decpt - 1
        val rest = if (digits.length > 1) "." + digits.substring(1) else ""
        val expSign = if (exp < 0) "-" else "+"
        f"${digits.charAt(0)}${rest}e$expSign${math.abs(exp)}%02d"
      } else if (decpt <= 0) {
        "0." + ("0" * (-decpt)) + digits
      } else if (decpt >= digits.length) {
        digits + ("0" * (decpt - digits.length)) + ".0"
      } else {
        digits.substring(0, decpt) + "." + digits.substring(decpt)
      }
    sign + body
  }

  /** `repr(s)` for a str（引用符の選択と基本エスケープ）。 */
  def strRepr(s: String): String = {
    val quote = if (s.contains('\'') && !s.contains('"')) '"' else '\''
    val sb = new StringBuilder
    sb.append(quote)
    s.foreach { c =>
      if (c == quote || c == '\\') { sb.append('\\').append(c) }
      else if (c == '\n') { sb.append("\\n") }
      else if (c == '\r') { sb.append("\\r") }
      else if (c == '\t') { sb.append("\\t") }
      else if (c < 0x20 || c == 0x7f) { sb.append(f"\\x${c.toInt}%02x") }
      else { sb.append(c) }
    }
    sb.append(quote)
    sb.toString
  }

  /** `repr(b)` for bytes given as a Latin-1 string（1 文字 = 1 バイト）。 */
  def bytesRepr(s: String): String = {
    val quote = if (s.contains('\'') && !s.contains('"')) '"' else '\''
    val sb = new StringBuilder
    sb.append('b').append(quote)
    s.foreach { c =>
      if (c == quote || c == '\\') { sb.append('\\').append(c) }
      else if (c == '\n') { sb.append("\\n") }
      else if (c == '\r') { sb.append("\\r") }
      else if (c == '\t') { sb.append("\\t") }
      else if (c < 0x20 || c >= 0x7f) { sb.append(f"\\x${c.toInt}%02x") }
      else { sb.append(c) }
    }
    sb.append(quote)
    sb.toString
  }

  /** `repr(list)` given the reprs of the elements. */
  def listRepr(items: Seq[String]): String = items.mkString("[", ", ", "]")

  /** `repr(list_of_int)`。 */
  def intListRepr(items: Seq[Int]): String = listRepr(items.map(_.toString))

  /** `json.dumps(s)` for a str（`ensure_ascii=False`）。 */
  def jsonString(s: String): String = {
    val sb = new StringBuilder
    sb.append('"')
    s.foreach {
      case '"'  => sb.append("\\\"")
      case '\\' => sb.append("\\\\")
      case '\n' => sb.append("\\n")
      case '\r' => sb.append("\\r")
      case '\t' => sb.append("\\t")
      case '\b' => sb.append("\\b")
      case '\f' => sb.append("\\f")
      case c if c < 0x20 => sb.append(f"\\u${c.toInt}%04x")
      case c => sb.append(c)
    }
    sb.append('"')
    sb.toString
  }
}
