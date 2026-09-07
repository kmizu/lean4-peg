package pal

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Experimental inverse expansion for the plain PEG subset emitted by tm2peg.
  *
  * `inverseRepeat(G, k)` recognizes {w | G recognizes each character of w k times}.
  * The virtual offset inside a repeated character is a finite grammar parameter,
  * not runtime state. `E_i_j` succeeds exactly when E returns in phase j from i.
  * An ordered-choice fallback is guarded by failure of E in *every* return phase.
  *
  * This is an output-boundary construction, not a real-time scheduling proof.
  * Input is BMP scalar text. The parser deliberately supports only double-quoted
  * literals, '.', names, sequence, choice, predicates, grouping and '*'. Source
  * grammars must terminate (in particular no nullable repetition/left recursion).
  *
  * Port of `phase_peg.py`.
  */
object PhasePeg {

  /** The Python `EMPTY` singleton. */
  val EMPTY: PegAst = PegAst.Empty

  private val NAME = "[A-Za-z_][A-Za-z_0-9]*".r
  private val TOKEN = "[A-Za-z_][A-Za-z_0-9]*|[=;()/!&.*]".r

  private[pal] def isName(text: String): Boolean = NAME.matches(text)

  private def isBmpScalar(c: Char): Boolean = !Character.isSurrogate(c)

  /** Python `json.dumps(c, ensure_ascii=False)` for one character, with backspace spelled ``. */
  def literal(c: Char): String = {
    val escaped = c match {
      case '\b' => "\\u0008"
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case '\f' => "\\f"
      case control if control < 0x20 => f"\\u${control.toInt}%04x"
      case other => other.toString
    }
    "\"" + escaped + "\""
  }

  private[pal] def requireBmp(text: String, message: String): Unit = {
    if (text.exists(c => !isBmpScalar(c))) { throw new IllegalArgumentException(message) }
  }

  // ---------------------------------------------------------------------
  // Tokenizer (the first half of Python `Grammar.__init__`).
  // ---------------------------------------------------------------------

  private[pal] sealed trait Token
  private[pal] final case class Literal(value: String) extends Token
  private[pal] final case class Punct(text: String) extends Token

  private[pal] def tokenize(source: String): Vector[Token] = {
    val tokens = Vector.newBuilder[Token]
    val matcher = TOKEN.pattern.matcher(source)
    var cursor = 0
    while (cursor < source.length) {
      val c = source.charAt(cursor)
      if (Character.isWhitespace(c) || Character.isSpaceChar(c)) {
        cursor += 1
      } else if (c == '"') {
        val (value, end) = JsonString.decode(source, cursor)
        requireBmp(value, "BMP scalar literals required")
        tokens += Literal(value)
        cursor = end
      } else {
        matcher.region(cursor, source.length)
        if (!matcher.lookingAt()) { throw new IllegalArgumentException(s"unsupported PEG syntax at $cursor") }
        tokens += Punct(matcher.group())
        cursor = matcher.end()
      }
    }
    tokens.result()
  }

  /** Decodes one JSON string literal starting at `start` (Python `json.JSONDecoder.raw_decode`). */
  private object JsonString {
    def decode(source: String, start: Int): (String, Int) = {
      val out = new StringBuilder
      var cursor = start + 1
      var closed = false
      while (!closed) {
        if (cursor >= source.length) { throw new IllegalArgumentException("unterminated string literal") }
        val c = source.charAt(cursor)
        if (c == '"') {
          closed = true
          cursor += 1
        } else if (c == '\\') {
          cursor = escape(source, cursor, out)
        } else if (c < 0x20) {
          throw new IllegalArgumentException(s"invalid control character at $cursor")
        } else {
          out += c
          cursor += 1
        }
      }
      (out.toString, cursor)
    }

    private def escape(source: String, cursor: Int, out: StringBuilder): Int = {
      if (cursor + 1 >= source.length) { throw new IllegalArgumentException("unterminated string literal") }
      source.charAt(cursor + 1) match {
        case '"' => out += '"'; cursor + 2
        case '\\' => out += '\\'; cursor + 2
        case '/' => out += '/'; cursor + 2
        case 'b' => out += '\b'; cursor + 2
        case 'f' => out += '\f'; cursor + 2
        case 'n' => out += '\n'; cursor + 2
        case 'r' => out += '\r'; cursor + 2
        case 't' => out += '\t'; cursor + 2
        case 'u' =>
          if (cursor + 6 > source.length) { throw new IllegalArgumentException("invalid \\u escape") }
          val hex = source.substring(cursor + 2, cursor + 6)
          if (!hex.forall(h => Character.digit(h, 16) >= 0)) { throw new IllegalArgumentException("invalid \\u escape") }
          out += Integer.parseInt(hex, 16).toChar
          cursor + 6
        case other => throw new IllegalArgumentException(s"invalid escape \\$other")
      }
    }
  }

  // ---------------------------------------------------------------------
  // Inverse fixed-width expansion.
  // ---------------------------------------------------------------------

  /** Phase-return relation of every reachable node: `(i, j)` when the node can start in phase i and return in phase j. */
  private final class PhaseReturns(grammar: Grammar, width: Int) {
    import PegAst.*

    val nodes: Vector[PegAst] = {
      val ids = mutable.LinkedHashSet.empty[PegAst]
      def register(expr: PegAst): Unit = {
        if (ids.add(expr)) {
          expr match {
            case Ref(name) => register(grammar.rules(name))
            case Sequence(first, second) => register(first); register(second)
            case Choice(first, second) => register(first); register(second)
            case NotPredicate(inner) => register(inner)
            case AndPredicate(inner) => register(inner)
            case Star(inner) => register(inner)
            case Empty | AnyChar | Terminal(_) => ()
          }
        }
      }
      register(grammar.rules(grammar.start))
      ids.toVector
    }

    val ids: Map[PegAst, Int] = nodes.zipWithIndex.toMap

    private val diagonal: Set[(Int, Int)] = (0 until width).map(i => (i, i)).toSet

    val returns: Map[PegAst, mutable.Set[(Int, Int)]] = {
      val table = nodes.map(expr => expr -> mutable.HashSet.empty[(Int, Int)]).toMap
      var changed = true
      while (changed) {
        changed = false
        for (expr <- nodes) {
          val possible = possibleReturns(expr, table)
          if (!possible.subsetOf(table(expr))) {
            table(expr) ++= possible
            changed = true
          }
        }
      }
      table
    }

    private def compose(left: collection.Set[(Int, Int)], right: collection.Set[(Int, Int)]): Set[(Int, Int)] = {
      (for ((i, k) <- left; (middle, j) <- right if middle == k) yield (i, j)).toSet
    }

    private def possibleReturns(expr: PegAst, table: Map[PegAst, mutable.Set[(Int, Int)]]): Set[(Int, Int)] = {
      expr match {
        case Empty | NotPredicate(_) => diagonal
        case Terminal(_) | AnyChar => (0 until width).map(i => (i, (i + 1) % width)).toSet
        case Ref(name) => table(grammar.rules(name)).toSet
        case Choice(first, second) => table(first).toSet | table(second).toSet
        case Sequence(first, second) => compose(table(first), table(second))
        case AndPredicate(inner) => table(inner).map { case (i, _) => (i, i) }.toSet
        case Star(inner) => diagonal | compose(table(inner), table(expr))
      }
    }

    def can(expr: PegAst, i: Int, j: Int): Boolean = returns(expr).contains((i, j))

    def name(expr: PegAst, i: Int, j: Int): String = s"E_${ids(expr)}_${i}_$j"

    def success(expr: PegAst, i: Int): String = s"Y_${ids(expr)}_$i"
  }

  def inverseRepeat(source: String, width: Int, start: String = "S"): String = {
    if (width < 1) { throw new IllegalArgumentException("positive integer width required") }
    val grammar = new Grammar(source, start)
    // Prune impossible phase returns before rendering. Besides reducing size,
    // this keeps a failed E_i_i from masquerading as a nullable prefix in the
    // target grammar's conservative left-recursion check.
    val phases = new PhaseReturns(grammar, width)
    val fail = "!\"\""
    val lines = mutable.ArrayBuffer[String](s"S = ${phases.name(grammar.rules(grammar.start), 0, 0)} !.;")
    for (expr <- phases.nodes; i <- 0 until width) {
      val choices = (0 until width).filter(j => phases.can(expr, i, j)).map(j => "&" + phases.name(expr, i, j))
      lines += phases.success(expr, i) + " = " + (if (choices.isEmpty) { fail } else { choices.mkString(" / ") }) + ";"
      for (j <- 0 until width) {
        val alternatives = phaseAlternatives(grammar, phases, width, expr, i, j)
        lines += phases.name(expr, i, j) + " = " + (if (alternatives.isEmpty) { fail } else { alternatives.mkString(" / ") }) + ";"
      }
    }
    lines.mkString("", "\n", "\n")
  }

  /** The ordered alternatives of rule `E_expr_i_j`. */
  private def phaseAlternatives(grammar: Grammar, phases: PhaseReturns, width: Int, expr: PegAst, i: Int, j: Int): Seq[String] = {
    import PegAst.*
    if (!phases.can(expr, i, j)) {
      Nil
    } else {
      expr match {
        case Empty if i == j => Seq("\"\"")
        case Terminal(_) | AnyChar if j == (i + 1) % width =>
          val terminal = expr match {
            case Terminal(c) => literal(c)
            case _ => "."
          }
          Seq(if (i == width - 1) { terminal } else { s"&($terminal)" })
        case Ref(name) => Seq(phases.name(grammar.rules(name), i, j))
        case Sequence(first, second) =>
          (0 until width).filter(k => phases.can(first, i, k) && phases.can(second, k, j))
            .map(k => phases.name(first, i, k) + " " + phases.name(second, k, j))
        case Choice(first, second) =>
          val alternatives = mutable.ArrayBuffer.empty[String]
          if (phases.can(first, i, j)) { alternatives += phases.name(first, i, j) }
          if (phases.can(second, i, j)) {
            val otherPhase = phases.returns(first).exists { case (a, b) => a == i && b != j }
            val commitment = if (otherPhase) { "!" + phases.success(first, i) + " " } else { "" }
            alternatives += commitment + phases.name(second, i, j)
          }
          alternatives.toSeq
        case NotPredicate(inner) if i == j => Seq("!" + phases.success(inner, i))
        case AndPredicate(inner) if i == j => Seq("&" + phases.success(inner, i))
        case Star(inner) =>
          val steps = (0 until width).filter(k => phases.can(inner, i, k) && phases.can(expr, k, j))
            .map(k => phases.name(inner, i, k) + " " + phases.name(expr, k, j))
          if (i == j) { steps :+ ("!" + phases.success(inner, i)) } else { steps }
        case _ => Nil
      }
    }
  }
}

/** Parsed PEG expression. Structural equality (for `inverseRepeat`'s node
  * numbering) plus a unique `identity` (for the packrat memo, which the
  * Python original keyed by `id(expr)`).
  */
sealed abstract class PegAst extends Product with Serializable {
  val identity: Int = PegAst.counter.getAndIncrement()
}

object PegAst {
  private val counter = new AtomicInteger(0)

  case object Empty extends PegAst
  final case class Terminal(char: Char) extends PegAst
  case object AnyChar extends PegAst
  final case class Ref(name: String) extends PegAst
  final case class Sequence(first: PegAst, second: PegAst) extends PegAst
  final case class Choice(first: PegAst, second: PegAst) extends PegAst
  final case class NotPredicate(inner: PegAst) extends PegAst
  final case class AndPredicate(inner: PegAst) extends PegAst
  final case class Star(inner: PegAst) extends PegAst
}

/** Packrat memo keyed by (node identity, position). Values: -1 missing, -2 in progress, else stored. */
private[pal] trait Memo {
  def get(identity: Int, position: Int): Int
  def update(identity: Int, position: Int, value: Int): Unit
}

private[pal] final class HashMemo extends Memo {
  private val cells = mutable.HashMap.empty[(Int, Int), Int]
  def get(identity: Int, position: Int): Int = cells.getOrElse((identity, position), -1)
  def update(identity: Int, position: Int, value: Int): Unit = { cells((identity, position)) = value }
}

/** Sparse rows become integer arrays when packrat cells grow dense.
  *
  * Python stored dense rows as `array("H")` (16-bit) below 65533 input
  * characters and `array("Q")` (64-bit) otherwise; `kind` reports which.
  */
final class CompactMemo(length: Int) extends Memo {
  val width: Int = length + 1
  val kind: String = if (length < 65533) { "H" } else { "Q" }
  private val missing: Long = if (kind == "H") { 65535L } else { -1L } // "Q": 2**64 - 1 as an unsigned Long
  val threshold: Int = math.max(8, width / (if (kind == "H") { 32 } else { 8 }))

  private sealed trait Row
  private final class Sparse(val cells: mutable.HashMap[Int, Long]) extends Row
  private final class Dense(val cells: Array[Long]) extends Row

  private val rows = mutable.HashMap.empty[Int, Row]

  def get(identity: Int, position: Int): Int = get(identity, position, -1)

  def get(identity: Int, position: Int, default: Int): Int = {
    rows.get(identity) match {
      case None => default
      case Some(row) =>
        val value = row match {
          case sparse: Sparse => sparse.cells.getOrElse(position, missing)
          case dense: Dense => dense.cells(position)
        }
        if (value == missing) { -1 } else if (value == missing - 1) { -2 } else { value.toInt }
    }
  }

  def update(identity: Int, position: Int, value: Int): Unit = {
    val stored = if (value < 0) { missing + value + 1 } else { value.toLong }
    rows.get(identity) match {
      case Some(dense: Dense) => dense.cells(position) = stored
      case other =>
        val sparse = other match {
          case Some(existing: Sparse) => existing
          case _ =>
            val fresh = new Sparse(mutable.HashMap.empty)
            rows(identity) = fresh
            fresh
        }
        sparse.cells(position) = stored
        if (sparse.cells.size > threshold) {
          val dense = Array.fill(width)(missing)
          for ((index, cell) <- sparse.cells) { dense(index) = cell }
          rows(identity) = new Dense(dense)
        }
    }
  }
}

/** A plain PEG (the tm2peg output subset) with an explicit-continuation packrat evaluator.
  *
  * `rules` is insertion ordered for parsed sources; `FileGrammar` substitutes a
  * lazily loading map.
  */
class Grammar protected (val rules: collection.Map[String, PegAst], val start: String) {

  def this(source: String, start: String = "S") = this(Grammar.parseRules(source, start), start)

  def accepts(word: String, compact: Boolean = false): Boolean = parsePrefix(word, compact).contains(word.length)

  /** Return the start rule's end position, or `None` on failure.
    *
    * Pointer-like PEG rules deliberately leave a suffix. Exposing their result
    * lets construction experiments check that suffix, rather than only checking
    * whole-word acceptance.
    */
  def parsePrefix(word: String, compact: Boolean = false): Option[Int] = {
    PhasePeg.requireBmp(word, "BMP scalar input required")
    val memo: Memo = if (compact) { new CompactMemo(word.length) } else { new HashMemo }
    new PackratRun(this, word, memo).run()
  }
}

object Grammar {

  /** Parse `source` into an insertion-ordered rule table; `start` must be defined. */
  def parseRules(source: String, start: String): VectorMap[String, PegAst] = {
    val rules = new GrammarParser(PhasePeg.tokenize(source)).parseRules()
    if (rules.isEmpty) { throw new IllegalArgumentException("empty grammar") }
    if (!rules.contains(start)) { throw new IllegalArgumentException(s"unknown start rule: $start") }
    rules
  }
}

/** Recursive-descent parser over the token stream (Python `Grammar.choice/sequence/prefix`). */
private final class GrammarParser(tokens: Vector[PhasePeg.Token]) {
  import PhasePeg.{Literal, Punct, Token}
  import PegAst.*

  private var cursor = 0

  def parseRules(): VectorMap[String, PegAst] = {
    var rules = VectorMap.empty[String, PegAst]
    while (cursor < tokens.length) {
      val name = take() match {
        case Punct(text) if PhasePeg.isName(text) => text
        case _ => throw new IllegalArgumentException("rule name required")
      }
      if (rules.contains(name)) { throw new IllegalArgumentException("duplicate rule") }
      expect("=")
      val expr = choice()
      expect(";")
      rules = rules.updated(name, expr)
    }
    rules
  }

  private def peek(): Option[Token] = if (cursor < tokens.length) { Some(tokens(cursor)) } else { None }

  private def peekIs(text: String): Boolean = peek().contains(Punct(text))

  private def take(): Token = {
    val result = peek().getOrElse(throw new IllegalArgumentException("unexpected end of grammar"))
    cursor += 1
    result
  }

  private def expect(text: String): Unit = {
    if (take() != Punct(text)) { throw new IllegalArgumentException(s"expected $text") }
  }

  private def choice(): PegAst = {
    var result = sequence()
    while (peekIs("/")) {
      take()
      result = Choice(result, sequence())
    }
    result
  }

  private def sequence(): PegAst = {
    val items = mutable.ArrayBuffer.empty[PegAst]
    while (peek().isDefined && !peekIs("/") && !peekIs(")") && !peekIs(";")) {
      items += prefix()
    }
    if (items.isEmpty) { throw new IllegalArgumentException("use \"\" for an empty expression") }
    items.tail.foldLeft(items.head)((result, expr) => Sequence(result, expr))
  }

  private def prefix(): PegAst = {
    if (peekIs("!")) {
      take()
      NotPredicate(prefix())
    } else if (peekIs("&")) {
      take()
      AndPredicate(prefix())
    } else {
      var result = primary()
      while (peekIs("*")) {
        take()
        result = Star(result)
      }
      result
    }
  }

  private def primary(): PegAst = {
    take() match {
      case Punct("(") =>
        val result = choice()
        expect(")")
        result
      case Punct(".") => AnyChar
      case Literal(value) =>
        value.foldLeft(PhasePeg.EMPTY) { (result, c) =>
          val char = Terminal(c)
          if (result == PhasePeg.EMPTY) { char } else { Sequence(result, char) }
        }
      case Punct(text) if PhasePeg.isName(text) => Ref(text)
      case Punct(text) => throw new IllegalArgumentException(s"unexpected $text")
    }
  }
}

/** One packrat evaluation of the start rule over `word`.
  *
  * Explicit continuations avoid a host recursion cap on a valid generated
  * grammar. Memo keys use AST identity; rule bodies themselves are shared.
  */
private final class PackratRun(grammar: Grammar, word: String, memo: Memo) {
  import PegAst.*

  private sealed trait Frame
  private final case class Eval(expr: PegAst, position: Int) extends Frame
  private final case class Save(identity: Int, position: Int) extends Frame
  private final case class SeqK(second: PegAst) extends Frame
  private final case class ChoiceK(second: PegAst, position: Int) extends Frame
  private final case class PredicateK(positive: Boolean, position: Int) extends Frame
  private final case class RepeatK(inner: PegAst, position: Int) extends Frame

  def run(): Option[Int] = {
    val work = mutable.Stack[Frame](Eval(grammar.rules(grammar.start), 0))
    var out: Option[Int] = None
    while (work.nonEmpty) {
      work.pop() match {
        case Save(identity, position) => memo.update(identity, position, out.map(_ + 1).getOrElse(0))
        case SeqK(second) => out.foreach(end => work.push(Eval(second, end)))
        case ChoiceK(second, position) => if (out.isEmpty) { work.push(Eval(second, position)) }
        case PredicateK(positive, position) => out = if (out.isDefined == positive) { Some(position) } else { None }
        case RepeatK(inner, position) =>
          out match {
            case None => out = Some(position)
            case Some(end) if end == position => throw new IllegalArgumentException("nullable repetition")
            case Some(end) =>
              work.push(RepeatK(inner, end))
              work.push(Eval(inner, end))
          }
        case Eval(expr, position) =>
          val cached = memo.get(expr.identity, position)
          if (cached >= 0) {
            out = if (cached == 0) { None } else { Some(cached - 1) }
          } else {
            if (cached == -2) { throw new IllegalArgumentException("non-consuming recursion") }
            memo.update(expr.identity, position, -2)
            work.push(Save(expr.identity, position))
            out = evaluate(expr, position, work, out)
          }
      }
    }
    out
  }

  private def evaluate(expr: PegAst, position: Int, work: mutable.Stack[Frame], out: Option[Int]): Option[Int] = {
    expr match {
      case Empty => Some(position)
      case AnyChar => if (position < word.length) { Some(position + 1) } else { None }
      case Terminal(c) => if (position < word.length && word.charAt(position) == c) { Some(position + 1) } else { None }
      case Ref(name) => work.push(Eval(grammar.rules(name), position)); out
      case Sequence(first, second) => work.push(SeqK(second)); work.push(Eval(first, position)); out
      case Choice(first, second) => work.push(ChoiceK(second, position)); work.push(Eval(first, position)); out
      case NotPredicate(inner) => work.push(PredicateK(positive = false, position)); work.push(Eval(inner, position)); out
      case AndPredicate(inner) => work.push(PredicateK(positive = true, position)); work.push(Eval(inner, position)); out
      case Star(inner) => work.push(RepeatK(inner, position)); work.push(Eval(inner, position)); out
    }
  }
}
