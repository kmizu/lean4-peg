package pal

import java.io.BufferedOutputStream
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, NoSuchFileException, Path, Paths, StandardOpenOption}
import java.util.regex.{Matcher, Pattern}
import scala.collection.mutable

/** Inline private expressions in a concrete scaffold-generated PEG.
  *
  * This is ordinary nonterminal inlining plus reachability. It neither executes
  * the source algorithm nor recognizes palindrome words. Rule bodies remain PEG
  * expressions, and input symbols are unchanged. The file format is the emitted
  * one-production-per-line S/B_n/P_n/E_n format.
  *
  * The default fuses private branch wrappers. --inline-private also substitutes
  * single-use E rules, grouping where needed and limiting substitution depth. Recursive
  * label/pointer boundaries and shared expressions remain ordinary nonterminals.
  *
  * Port of `compact_scaffold_peg.py`. Like the original, the source file is
  * memory mapped and read production by production; rule bodies pass through
  * a small LRU cache and the output is streamed, so the whole grammar is never
  * held as one string. Bytes are handled as ISO-8859-1 text (one char per byte)
  * so that Java regexes see exactly the Python bytes patterns and the output is
  * byte-identical.
  *
  * Capability limits relative to the Python script: the source is mapped in
  * 1 GiB windows, allowing files larger than 2 GiB subject to available
  * address space and JVM resources (Python: one `mmap`), but one production
  * line must stay below 2 GiB; rule numbers
  * (`E_n` etc.) must be below 2^30 per group because the offset tables are
  * JVM arrays (Python has no corresponding fixed 2^30 cap). Both are far beyond
  * the 672 MB / ten-million-rule grammars this tool exists for.
  */
object CompactScaffoldPeg {

  /** The Python `compact()` statistics dictionary. */
  final case class CompactStats(
      beforeRules: Long,
      afterRules: Long,
      fused: Long,
      beforeBytes: Long,
      afterBytes: Long,
      inlinePrivate: Boolean
  ) {
    /** Python `json.dumps(stats)`. */
    def toJson: String = {
      s"""{"before_rules": $beforeRules, "after_rules": $afterRules, "fused": $fused, """ +
        s""""before_bytes": $beforeBytes, "after_bytes": $afterBytes, "inline_private": $inlinePrivate}"""
    }
  }

  val GROUPS: Vector[String] = Vector("S", "B", "P", "E")
  private val MISSING = -1L
  private val ISO = StandardCharsets.ISO_8859_1
  private val RADIX = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

  // UNIX_LINES: only '\n' ends a line, so `.` matches every other byte, as in Python's bytes regexes.
  private val TOKENS = Pattern.compile("\"(?:\\\\.|[^\"\\\\])*\"|(?<ref>[A-Za-z_][A-Za-z_0-9]*)", Pattern.UNIX_LINES)
  private val PAIR = Pattern.compile("(E_[0-9]+) (E_[0-9]+)")
  private val CHOICE = Pattern.compile("(E_[0-9]+) / (E_[0-9]+)")
  private val NEGATIVE = Pattern.compile("!(E_[0-9]+)")
  private val ATOM = Pattern.compile("(?:[!&]\\s*)*(?:\"(?:\\\\.|[^\"\\\\])*\"|[A-Za-z_][A-Za-z_0-9]*|\\.)", Pattern.UNIX_LINES)
  private val GROUP_TOKENS = Pattern.compile("\"(?:\\\\.|[^\"\\\\])*\"|[()/]", Pattern.UNIX_LINES)

  private def reject(message: String): Nothing = throw new IllegalArgumentException(message)

  /** Encode a rule name as `(index << 2) | group`; `S` is 0.
    *
    * Rule numbers of 2^30 and above are rejected (Python accepts any integer);
    * the per-group offset tables are JVM arrays indexed by the number.
    */
  def identifier(name: String): Long = {
    if (name == "S") {
      0L
    } else {
      val digits = name.substring(math.min(2, name.length))
      if (name.length < 3 || GROUPS.indexOf(name.substring(0, 1)) < 1 || name.charAt(1) != '_' ||
          !digits.forall(c => c >= '0' && c <= '9')) {
        reject("expected a scaffold-generated rule name")
      }
      val index = try { java.lang.Long.parseLong(digits) } catch { case _: NumberFormatException => reject("rule index too large") }
      if (index >= (1L << 30)) { reject("rule index too large") }
      (index << 2) | GROUPS.indexOf(name.substring(0, 1)).toLong
    }
  }

  /** The base-62 short name of a rule (`S`, or the lower-cased group letter and digits). */
  def shortened(name: String): String = {
    val code = identifier(name)
    if (code == 0L) {
      "S"
    } else {
      var value = code >> 2
      val digits = new StringBuilder
      var more = true
      while (more) {
        digits.append(RADIX.charAt((value % RADIX.length).toInt))
        value /= RADIX.length
        more = value != 0
      }
      GROUPS((code & 3).toInt).toLowerCase + digits.reverse.toString
    }
  }

  /** Rule codes referenced from `body` (string literals are skipped). */
  def references(body: String): Iterator[Long] = {
    new Iterator[Long] {
      private val matcher = TOKENS.matcher(body)
      private var pending: Long = -1L
      private def advance(): Unit = {
        while (pending < 0 && matcher.find()) {
          val name = matcher.group("ref")
          if (name != null) { pending = identifier(name) }
        }
      }
      def hasNext: Boolean = {
        advance()
        pending >= 0
      }
      def next(): Long = {
        advance()
        if (pending < 0) { throw new NoSuchElementException("no more references") }
        val result = pending
        pending = -1L
        result
      }
    }
  }

  private def isSpace(c: Char): Boolean = c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\u000b' || c == '\f'

  private def rstrip(text: String): String = {
    var end = text.length
    while (end > 0 && isSpace(text.charAt(end - 1))) { end -= 1 }
    text.substring(0, end)
  }

  private def lstrip(text: String): String = {
    var start = 0
    while (start < text.length && isSpace(text.charAt(start))) { start += 1 }
    text.substring(start)
  }

  /** Whether substituting `body` between `before` and `after` needs parentheses. */
  def needsGroup(body: String, before: String, after: String): Boolean = {
    val prefix = rstrip(before)
    if (prefix.endsWith("!") || prefix.endsWith("&") || lstrip(after).startsWith("*")) {
      true
    } else if (ATOM.matcher(body).matches()) {
      false
    } else {
      var depth = 0
      var topLevelChoice = false
      val matcher = GROUP_TOKENS.matcher(body)
      while (!topLevelChoice && matcher.find()) {
        matcher.group() match {
          case "(" => depth += 1
          case ")" => depth -= 1
          case "/" => if (depth == 0) { topLevelChoice = true }
          case _ => ()
        }
      }
      // Sequence associates freely in another sequence or a choice branch.
      // Existing parenthesized predicates retain their own grouping.
      topLevelChoice
    }
  }

  private def canonical(path: Path): Path = {
    try { path.toRealPath() } catch { case _: NoSuchFileException => path.toAbsolutePath.normalize() }
  }

  def compact(source: Path, target: Path, shortNames: Boolean = false, inlinePrivate: Boolean = false): CompactStats = {
    if (canonical(source) == canonical(target)) { reject("source and destination must be distinct files") }
    val channel = FileChannel.open(source, StandardOpenOption.READ)
    try {
      val compactor = new Compactor(new MappedFile(channel), inlinePrivate)
      val before = compactor.index()
      val live = compactor.reachable()
      val (after, fused) = compactor.emit(target, live, shortNames)
      CompactStats(before, after, fused, Files.size(source), Files.size(target), inlinePrivate)
    } finally {
      channel.close()
    }
  }

  /** A read-only file mapped in 1 GiB windows and addressed by `Long` positions.
    *
    * `java.nio` maps at most 2 GiB per buffer; several windows lift that limit
    * (Python's single `mmap` has none) while keeping the same page-cache-backed
    * random access to rule bodies.
    */
  private[pal] final class MappedFile(channel: FileChannel, private[pal] val windowShift: Int = 30) {
    require(windowShift >= 1 && windowShift <= 30, "mapped-file window shift must be between 1 and 30")
    private val WindowSize = 1L << windowShift
    val size: Long = channel.size()
    private val windows: Array[ByteBuffer] = (0L until size by WindowSize).map { offset =>
      channel.map(FileChannel.MapMode.READ_ONLY, offset, math.min(WindowSize, size - offset))
    }.toArray

    def get(position: Long): Byte = windows((position >> windowShift).toInt).get((position & (WindowSize - 1)).toInt)

    /** The bytes in `[from, until)` as ISO-8859-1 text (one char per byte). */
    def slice(from: Long, until: Long): String = {
      if (until - from > Int.MaxValue) { reject("production line larger than 2 GiB is not supported") }
      val bytes = new Array[Byte]((until - from).toInt)
      var position = from
      var copied = 0
      while (position < until) {
        val window = windows((position >> windowShift).toInt).duplicate()
        val offset = (position & (WindowSize - 1)).toInt
        val count = math.min(window.limit() - offset, (until - position).toInt)
        window.position(offset).get(bytes, copied, count)
        position += count
        copied += count
      }
      new String(bytes, ISO)
    }
  }

  /** A growable primitive `Long` array (Python `array("Q")`). */
  private final class LongVec {
    private var data = new Array[Long](16)
    var length = 0
    def apply(index: Int): Long = data(index)
    def update(index: Int, value: Long): Unit = { data(index) = value }
    def extend(count: Int, value: Long): Unit = {
      if (length + count > data.length) { data = java.util.Arrays.copyOf(data, math.max(data.length * 2, length + count)) }
      java.util.Arrays.fill(data, length, length + count, value)
      length += count
    }
  }

  /** A growable primitive `Int` array (Python `array("I")`). */
  private final class IntVec {
    private var data = new Array[Int](16)
    var length = 0
    def apply(index: Int): Int = data(index)
    def update(index: Int, value: Int): Unit = { data(index) = value }
    def extend(count: Int): Unit = {
      if (length + count > data.length) { data = java.util.Arrays.copyOf(data, math.max(data.length * 2, length + count)) }
      length += count
    }
  }

  /** A bounded least-recently-used cache (Python `functools.lru_cache`). */
  private final class Lru[K, V](maximum: Int) {
    private val cells = new java.util.LinkedHashMap[K, V](16, 0.75f, true) {
      override def removeEldestEntry(eldest: java.util.Map.Entry[K, V]): Boolean = size() > maximum
    }
    def getOrElseUpdate(key: K, compute: => V): V = {
      val cached = cells.get(key)
      if (cached != null) {
        cached
      } else {
        val value = compute
        cells.put(key, value)
        value
      }
    }
  }

  /** One expansion frame: a rule body being copied to the output, token by token. */
  private final class Frame(val text: String, val tokens: Matcher, var cursor: Int, val depth: Int, val closing: Boolean)

  /** The three passes over one mapped source file. */
  private final class Compactor(data: MappedFile, inlinePrivate: Boolean) {
    private val size: Long = data.size
    private val offsets: Vector[LongVec] = GROUPS.map(_ => new LongVec)
    private val uses: Vector[IntVec] = GROUPS.map(_ => new IntVec)
    private val bodies = new Lru[Long, String](8192)
    private val shortNames = new Lru[String, String](65536)

    private def slice(start: Long, end: Long): String = data.slice(start, end)

    /** Position of the next `'\n'` at or after `start`, else `size`. */
    private def lineEnd(start: Long): Long = {
      var end = start
      while (end < size && data.get(end) != '\n'.toByte) { end += 1 }
      end
    }

    /** Position of the first `" = "` at or after `start` and before `limit`, else -1. */
    private def separator(start: Long, limit: Long): Long = {
      var at = start
      var found = -1L
      while (found < 0 && at + 3 <= limit) {
        if (data.get(at) == ' '.toByte && data.get(at + 1) == '='.toByte && data.get(at + 2) == ' '.toByte) { found = at } else { at += 1 }
      }
      found
    }

    private def ensure(code: Long): (Int, Int) = {
      val group = (code & 3).toInt
      val index = (code >> 2).toInt
      val missing = index + 1 - offsets(group).length
      if (missing > 0) {
        offsets(group).extend(missing, MISSING)
        uses(group).extend(missing)
      }
      (group, index)
    }

    private def useCount(code: Long): Int = uses((code & 3).toInt)((code >> 2).toInt)

    /** Pass 1: record every production's offset and count references; returns the rule count. */
    def index(): Long = {
      var count = 0L
      var start = 0L
      while (start < size) {
        val end = lineEnd(start)
        // Python `line.rstrip(b"\r\n")`: CRLF sources are accepted.
        var stripped = end
        while (stripped > start && (data.get(stripped - 1) == '\r'.toByte || data.get(stripped - 1) == '\n'.toByte)) { stripped -= 1 }
        val sep = separator(start, stripped)
        if (sep < 0) { reject("one complete production per line is required") }
        val head = slice(start, sep)
        val body = slice(sep + 3, stripped)
        if (!body.endsWith(";")) { reject("one complete production per line is required") }
        val (group, index) = ensure(identifier(head))
        if (offsets(group)(index) != MISSING) { reject("duplicate production") }
        offsets(group)(index) = start
        for (ref <- references(body.substring(0, body.length - 1))) {
          val (a, b) = ensure(ref)
          uses(a)(b) = uses(a)(b) + 1
        }
        count += 1
        start = if (end < size) { end + 1 } else { end }
      }
      // Gaps in generated identifiers are permitted, but referenced gaps are not.
      val undefined = offsets(0).length == 0 || (0 until 4).exists { group =>
        (0 until offsets(group).length).exists(i => offsets(group)(i) == MISSING && uses(group)(i) != 0)
      }
      if (undefined) { reject("undefined production") }
      count
    }

    /** The body text of a production, without its trailing `;` (and `\r`). */
    def body(code: Long): String = {
      bodies.getOrElseUpdate(code, {
        val begin = offsets((code & 3).toInt)((code >> 2).toInt)
        val end = lineEnd(begin)
        val text = slice(separator(begin, size) + 3, end)
        // Python `.rstrip(b"\r;")`.
        var stop = text.length
        while (stop > 0 && (text.charAt(stop - 1) == '\r' || text.charAt(stop - 1) == ';')) { stop -= 1 }
        text.substring(0, stop)
      })
    }

    /** Fuse a private two-branch choice `E_a / E_b` whose branches are private guard/value pairs. */
    def rewritten(code: Long): String = {
      val original = body(code)
      val choice = CHOICE.matcher(original)
      if (!choice.matches()) {
        original
      } else {
        val children = Vector(identifier(choice.group(1)), identifier(choice.group(2)))
        if (children.exists(child => useCount(child) != 1)) {
          original
        } else {
          val pairs = children.map(child => PAIR.matcher(body(child)))
          if (pairs.exists(pair => !pair.matches())) {
            original
          } else {
            pairs.map { pair =>
              var guard = pair.group(1)
              val value = pair.group(2)
              val guardCode = identifier(guard)
              val guardBody = body(guardCode)
              if (useCount(guardCode) == 1 && NEGATIVE.matcher(guardBody).matches()) { guard = guardBody }
              guard + " " + value
            }.mkString(" / ")
          }
        }
      }
    }

    /** Whether `ref` is a single-use E rule that may be substituted at `depth`. */
    private def inlinable(ref: Long, depth: Int): Boolean = (ref & 3) == 3 && useCount(ref) == 1 && depth < 16

    /** The production with private single-use E rules substituted (when enabled). */
    def expanded(code: Long): String = {
      if (!inlinePrivate) {
        rewritten(code)
      } else {
        // Grouping preserves precedence below predicates and ordered
        // choices. Limit only substitution depth: deeper private rules remain
        // ordinary references and are reached by the closure below.
        val output = new java.lang.StringBuilder
        val start = rewritten(code)
        val frames = mutable.Stack(new Frame(start, TOKENS.matcher(start), 0, 0, false))
        while (frames.nonEmpty) {
          val frame = frames.pop()
          var descended = false
          while (!descended && frame.tokens.find()) {
            val name = frame.tokens.group("ref")
            if (name != null && inlinable(identifier(name), frame.depth)) {
              val (from, until) = (frame.tokens.start(), frame.tokens.end())
              output.append(frame.text, frame.cursor, from)
              val child = rewritten(identifier(name))
              val grouped = needsGroup(child, frame.text.substring(0, from), frame.text.substring(until))
              if (grouped) { output.append('(') }
              frame.cursor = until
              frames.push(frame)
              frames.push(new Frame(child, TOKENS.matcher(child), 0, frame.depth + 1, grouped))
              descended = true
            }
          }
          if (!descended) {
            output.append(frame.text, frame.cursor, frame.text.length)
            if (frame.closing) { output.append(')') }
          }
        }
        output.toString
      }
    }

    /** Pass 2: the productions reachable from `S` through expanded bodies. */
    def reachable(): Vector[Array[Boolean]] = {
      val live = offsets.map(group => new Array[Boolean](group.length))
      val work = mutable.Stack[Long](0L)
      while (work.nonEmpty) {
        val code = work.pop()
        val group = (code & 3).toInt
        val index = (code >> 2).toInt
        if (!live(group)(index)) {
          live(group)(index) = true
          references(expanded(code)).foreach(work.push)
        }
      }
      live
    }

    private def rename(text: String): String = {
      val out = new java.lang.StringBuilder
      val matcher = TOKENS.matcher(text)
      var cursor = 0
      while (matcher.find()) {
        out.append(text, cursor, matcher.start())
        val name = matcher.group("ref")
        out.append(if (name == null) { matcher.group() } else { shortNames.getOrElseUpdate(name, shortened(name)) })
        cursor = matcher.end()
      }
      out.append(text, cursor, text.length)
      out.toString
    }

    /** Pass 3: stream the live productions to `target`; returns (rules written, rules changed). */
    def emit(target: Path, live: Vector[Array[Boolean]], useShortNames: Boolean): (Long, Long) = {
      var after = 0L
      var fused = 0L
      val output = new BufferedOutputStream(Files.newOutputStream(target), 1 << 16)
      try {
        var start = 0L
        while (start < size) {
          val end = lineEnd(start)
          val sep = separator(start, end)
          var head = slice(start, if (sep < 0) { end } else { sep })
          val code = identifier(head)
          if (live((code & 3).toInt)((code >> 2).toInt)) {
            var result = expanded(code)
            if (result != body(code)) { fused += 1 }
            if (useShortNames) {
              head = shortNames.getOrElseUpdate(head, shortened(head))
              result = rename(result)
            }
            output.write((head + " = " + result + ";\n").getBytes(ISO))
            after += 1
          }
          start = if (end < size) { end + 1 } else { end }
        }
      } finally {
        output.close()
      }
      (after, fused)
    }
  }

  private def usage(): Nothing = {
    System.err.println("usage: CompactScaffoldPeg [--short-names] [--inline-private] SOURCE TARGET")
    System.err.println("  Same arguments and output as compact_scaffold_peg.py. Limits: one production")
    System.err.println("  line below 2 GiB and rule numbers below 2^30 per group (Python has no such caps).")
    sys.exit(2)
  }

  def main(args: Array[String]): Unit = {
    var shortNames = false
    var inlinePrivate = false
    val positional = mutable.ArrayBuffer.empty[String]
    for (arg <- args) {
      arg match {
        case "--short-names" => shortNames = true
        case "--inline-private" => inlinePrivate = true
        case flag if flag.startsWith("-") && flag != "-" => usage()
        case path => positional += path
      }
    }
    if (positional.length != 2) { usage() }
    val stats = compact(Paths.get(positional(0)), Paths.get(positional(1)), shortNames = shortNames, inlinePrivate = inlinePrivate)
    println(stats.toJson)
    Console.out.flush()
  }
}
