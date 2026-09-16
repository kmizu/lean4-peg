package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable
import scala.util.hashing.MurmurHash3

/** Finite Boolean/pointer scaffold equations to ordinary PEG.
  *
  * Every label is a Boolean component. Transition expressions inspect the input
  * symbol and bounded paths from the previous root; they cannot inspect pointer
  * identity. Edges may target self, null, or a bounded old path. Conditional
  * expressions share grammar rules, without enumerating complete neighborhoods.
  * An explicit initial sentinel has supplied labels and all-null pointer fields.
  * The generated PEG recognizes the reversal of the scaffold's input language.
  * This is an output interface, not a lowering of scaffold_galil's Python code.
  *
  * Port of `symbolic_sca2peg.py`. The Python `Expr` was an untyped tuple
  * `(tag, *args)`; here it is a sealed ADT over the same fourteen tags.
  */

/** Immutable DAG node with a cached structural hash.
  *
  * The Python original was a tuple-like object with an attached hash so that
  * millions of construction expressions could be compared and interned cheaply.
  * The case classes below keep structural equality and pattern matching; the
  * base class supplies the cached hash and an identity shortcut in `equals`
  * (both suppress the case-class generated versions).
  */
sealed abstract class Expr extends Product with Serializable {

  /** The Python tuple tag: "const", "symbol", "self", ... */
  def tag: String

  /** The Python tuple arguments after the tag, in order (for serialization). */
  def args: Vector[Any]

  /** Cached structural hash; 0 means "not computed yet" (the `java.lang.String` idiom).
    *
    * A single word is published at once, so a concurrent reader can only ever
    * see 0 (and recompute the same value) or the finished hash - never a torn
    * pair of fields. A genuine hash of 0 is simply recomputed on each call.
    */
  private var hashCache: Int = 0

  final override def hashCode: Int = {
    var h = hashCache
    if (h == 0) {
      h = MurmurHash3.productHash(this)
      hashCache = h
    }
    h
  }

  final override def equals(other: Any): Boolean = {
    other match {
      case that: Expr =>
        (this eq that) || (hashCode == that.hashCode && sameStructure(that))
      case _ => false
    }
  }

  private def sameStructure(that: Expr): Boolean = {
    productPrefix == that.productPrefix &&
      productArity == that.productArity &&
      productIterator.sameElements(that.productIterator)
  }

  final override def toString: String = {
    if (args.isEmpty) { s"($tag,)" } else { (tag +: args).mkString("(", ", ", ")") }
  }
}

object Expr {
  final case class Const(value: Boolean) extends Expr {
    def tag: String = "const"
    def args: Vector[Any] = Vector(value)
  }

  final case class Symbol(char: Char) extends Expr {
    def tag: String = "symbol"
    def args: Vector[Any] = Vector(char)
  }

  case object Self extends Expr {
    def tag: String = "self"
    def args: Vector[Any] = Vector.empty
  }

  case object Null extends Expr {
    def tag: String = "null"
    def args: Vector[Any] = Vector.empty
  }

  /** Read a label of the node reached by a bounded pointer path from the old root. */
  final case class Old(path: Vector[String], label: String) extends Expr {
    def tag: String = "old"
    def args: Vector[Any] = Vector(path, label)
  }

  final case class Exists(path: Vector[String]) extends Expr {
    def tag: String = "exists"
    def args: Vector[Any] = Vector(path)
  }

  final case class Not(value: Expr) extends Expr {
    def tag: String = "not"
    def args: Vector[Any] = Vector(value)
  }

  final case class And(values: Vector[Expr]) extends Expr {
    def tag: String = "and"
    def args: Vector[Any] = values
  }

  final case class Or(values: Vector[Expr]) extends Expr {
    def tag: String = "or"
    def args: Vector[Any] = values
  }

  final case class Pointer(path: Vector[String]) extends Expr {
    def tag: String = "pointer"
    def args: Vector[Any] = Vector(path)
  }

  final case class Select(condition: Expr, yes: Expr, no: Expr) extends Expr {
    def tag: String = "select"
    def args: Vector[Any] = Vector(condition, yes, no)
  }

  /** Read a label through a computed old pointer; null reads are false. */
  final case class Read(target: Expr, label: String) extends Expr {
    def tag: String = "read"
    def args: Vector[Any] = Vector(target, label)
  }

  /** Follow one edge through a computed old pointer; null stays null. */
  final case class Edge(target: Expr, field: String) extends Expr {
    def tag: String = "edge"
    def args: Vector[Any] = Vector(target, field)
  }

  final case class Present(target: Expr) extends Expr {
    def tag: String = "present"
    def args: Vector[Any] = Vector(target)
  }

  val TRUE: Expr = Const(true)
  val FALSE: Expr = Const(false)
  val SELF: Expr = Self
  val NULL: Expr = Null

  // ---------------------------------------------------------------------
  // Hash-consing (Python `Expr._pool`, `share_expressions`, `clear_expression_cache`).
  // ---------------------------------------------------------------------

  private var pool: mutable.HashMap[Expr, Expr] = null

  /** Whether an interning index is currently active (Python `Expr._pool is not None`). */
  def sharing: Boolean = pool != null

  /** Return the canonical instance of `expr` while sharing is active, else `expr`. */
  def intern[E <: Expr](expr: E): E = {
    if (pool == null) { expr } else { pool.getOrElseUpdate(expr, expr).asInstanceOf[E] }
  }

  /** Hash-cons equal construction expressions within `body`; release the index on exit.
    *
    * Nested scopes reuse the enclosing index. Port of the `share_expressions()`
    * context manager.
    */
  def share[A](body: => A): A = {
    val previous = pool
    pool = if (previous == null) { mutable.HashMap.empty[Expr, Expr] } else { previous }
    try { body } finally { pool = previous }
  }

  /** Release only the optional interning index, retaining all live DAGs.
    *
    * Construction roots own their expression nodes directly. Clearing the
    * index between large instruction bursts permits unused temporary nodes to
    * die; it does not change any expression, source state, or PEG equation.
    */
  def clearExpressionCache(): Unit = {
    if (pool != null) { pool.clear() }
  }

  // ---------------------------------------------------------------------
  // Constructors (the Python module-level functions).
  // ---------------------------------------------------------------------

  def symbol(char: Char): Expr = intern(Symbol(char))

  def old(path: Seq[String], label: String): Expr = intern(Old(path.toVector, label))

  def exists(path: Seq[String]): Expr = intern(Exists(path.toVector))

  def negate(value: Expr): Expr = intern(Not(value))

  def both(values: Expr*): Expr = intern(And(values.toVector))

  def either(values: Expr*): Expr = intern(Or(values.toVector))

  def pointer(path: Seq[String]): Expr = intern(Pointer(path.toVector))

  def select(condition: Expr, yes: Expr, no: Expr): Expr = intern(Select(condition, yes, no))

  /** Read a label through a computed old pointer; null reads are false. */
  def read(target: Expr, label: String): Expr = intern(Read(target, label))

  /** Follow one edge through a computed old pointer; null stays null. */
  def edge(target: Expr, field: String): Expr = intern(Edge(target, field))

  def present(target: Expr): Expr = intern(Present(target))

  /** Rebuild an expression from its Python tuple shape `(tag, *args)`.
    *
    * Used by artifact readers; malformed shapes raise `IllegalArgumentException`
    * where the Python `Scaffold` validator would have rejected the tuple.
    */
  def make(tag: String, args: Seq[Any]): Expr = {
    def path(value: Any): Vector[String] = {
      value match {
        case fields: Iterable[?] => fields.toVector.map(_.asInstanceOf[String])
        case _ => throw new IllegalArgumentException("finite tuple expression required")
      }
    }
    def child(value: Any): Expr = {
      value match {
        case expr: Expr => expr
        case _ => throw new IllegalArgumentException("finite tuple expression required")
      }
    }
    def string(value: Any): String = {
      value match {
        case text: String => text
        case _ => throw new IllegalArgumentException("invalid expression or Boolean/pointer type mismatch")
      }
    }
    val built: Expr = (tag, args.toVector) match {
      case ("const", Vector(value: Boolean)) => Const(value)
      case ("symbol", Vector(char: Char)) => Symbol(char)
      case ("symbol", Vector(text: String)) if text.length == 1 => Symbol(text.charAt(0))
      case ("self", Vector()) => Self
      case ("null", Vector()) => Null
      case ("old", Vector(p, label)) => Old(path(p), string(label))
      case ("exists", Vector(p)) => Exists(path(p))
      case ("not", Vector(value)) => Not(child(value))
      case ("and", values) => And(values.map(child))
      case ("or", values) => Or(values.map(child))
      case ("pointer", Vector(p)) => Pointer(path(p))
      case ("select", Vector(condition, yes, no)) => Select(child(condition), child(yes), child(no))
      case ("read", Vector(target, label)) => Read(child(target), string(label))
      case ("edge", Vector(target, field)) => Edge(child(target), string(field))
      case ("present", Vector(target)) => Present(child(target))
      case _ => throw new IllegalArgumentException("invalid expression or Boolean/pointer type mismatch")
    }
    intern(built)
  }
}

/** One scaffold node: Boolean labels and pointer fields (null pointers are `None`).
  *
  * Fields are mutable because `SELF` evaluates to the node under construction
  * before its own fields are known (a self edge is a cycle).
  */
final class Node(
    var labels: VectorMap[String, Boolean],
    var pointers: VectorMap[String, Option[Node]]
) {
  override def toString: String = s"Node(labels=$labels, pointers=${pointers.keys.mkString("[", ", ", "]")})"
}

/** A finite scaffold machine: initial labels, label equations, pointer equations.
  *
  * All maps are insertion ordered (rule numbering follows declaration order);
  * pass a `VectorMap`, `LinkedHashMap` or a sequence of pairs, never a large
  * unordered `Map`.
  */
final class Scaffold(
    initialFields: Iterable[(String, Boolean)],
    labelFields: Iterable[(String, Expr)],
    pointerFields: Iterable[(String, Expr)],
    val accepting: String,
    val alphabet: String = "ab"
) {
  val initial: VectorMap[String, Boolean] = VectorMap.from(initialFields)
  val labels: VectorMap[String, Expr] = VectorMap.from(labelFields)
  val pointers: VectorMap[String, Expr] = VectorMap.from(pointerFields)

  if (initial.keySet != labels.keySet) {
    throw new IllegalArgumentException("initial Boolean values must cover exactly the label fields")
  }
  if (!labels.contains(accepting)) {
    throw new IllegalArgumentException("unknown acceptance label")
  }
  if (alphabet.isEmpty || alphabet.distinct.length != alphabet.length || alphabet.exists(Character.isSurrogate)) {
    throw new IllegalArgumentException("distinct BMP scalar input characters required")
  }
  locally {
    // Construction scratch, not part of the machine: the Python original
    // cleared its `_validated` sets after construction for the same reason.
    val validator = new ScaffoldValidator(this)
    for (expr <- labels.values) { validator.validate(expr, isPointer = false) }
    for (expr <- pointers.values) { validator.validate(expr, isPointer = true) }
  }

  def run(word: String): Boolean = {
    evaluate(word) match {
      case Some(root) => root.labels(accepting)
      case None => false
    }
  }

  def initialNode(): Node = {
    new Node(initial, pointers.map { case (key, _) => key -> None })
  }

  /** Return the last scaffold node for independent state-level verification. */
  def evaluate(word: String): Option[Node] = {
    var root: Option[Node] = Some(initialNode())
    val chars = word.iterator
    while (root.isDefined && chars.hasNext) {
      root = step(root.get, chars.next())
    }
    root
  }

  def step(root: Node, char: Char): Option[Node] = {
    if (alphabet.indexOf(char.toInt) < 0) {
      None
    } else {
      val created = new Node(VectorMap.empty, VectorMap.empty)
      val evaluator = new ScaffoldEvaluator(root, created, char)
      created.labels = labels.map { case (key, expr) => key -> evaluator.evalBoolean(expr) }
      created.pointers = pointers.map { case (key, expr) => key -> evaluator.evalPointer(expr) }
      Some(created)
    }
  }

  def compile(): String = iterRules().mkString("", "\n", "\n")

  /** Emit the same finite PEG without retaining its whole text in memory. */
  def iterRules(): Iterator[String] = new ScaffoldRenderer(this).rules
}

/** Type checks the label (Boolean) and pointer equations of a scaffold.
  *
  * Three expectation kinds mirror the Python validator: "boolean", "pointer"
  * and "old" (a pointer expression that must not mention the new self).
  */
private final class ScaffoldValidator(scaffold: Scaffold) {
  import Expr.*

  private sealed trait Expected
  private case object Boolean extends Expected
  private case object PointerKind extends Expected
  private case object OldKind extends Expected

  private val validated: Map[Expected, java.util.Set[Expr]] = Map(
    Boolean -> newIdentitySet(),
    PointerKind -> newIdentitySet(),
    OldKind -> newIdentitySet()
  )

  private def newIdentitySet(): java.util.Set[Expr] = {
    java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Expr, java.lang.Boolean]())
  }

  private def reject(message: String): Nothing = throw new IllegalArgumentException(message)

  private def checkPath(path: Vector[String]): Unit = {
    if (path.exists(field => !scaffold.pointers.contains(field))) { reject("unknown pointer field in path") }
  }

  def validate(expr: Expr, isPointer: Boolean): Unit = {
    val work = mutable.Stack[(Expr, Expected)]((expr, if (isPointer) { PointerKind } else { Boolean }))
    while (work.nonEmpty) {
      val (current, expected) = work.pop()
      val seen = validated(expected)
      if (!seen.contains(current)) {
        val children = expected match {
          case OldKind => oldChildren(current)
          case PointerKind => pointerChildren(current)
          case Boolean => booleanChildren(current)
        }
        seen.add(current)
        work.pushAll(children)
      }
    }
  }

  private def mismatch(): Nothing = reject("invalid expression or Boolean/pointer type mismatch")

  private def oldChildren(current: Expr): Seq[(Expr, Expected)] = {
    current match {
      case Self => reject("transition queries must inspect old nodes, not the new self")
      case Select(_, yes, no) => Seq((current, PointerKind), (yes, OldKind), (no, OldKind))
      case _ => Seq((current, PointerKind))
    }
  }

  private def pointerChildren(current: Expr): Seq[(Expr, Expected)] = {
    current match {
      case Self | Null => Nil
      case Pointer(path) => checkPath(path); Nil
      case Select(condition, yes, no) => Seq((condition, Boolean), (yes, PointerKind), (no, PointerKind))
      case Edge(target, field) if scaffold.pointers.contains(field) => Seq((target, OldKind))
      case _ => mismatch()
    }
  }

  private def booleanChildren(current: Expr): Seq[(Expr, Expected)] = {
    current match {
      case Const(_) => Nil
      case Symbol(char) if scaffold.alphabet.indexOf(char.toInt) >= 0 => Nil
      case Old(path, label) if scaffold.labels.contains(label) => checkPath(path); Nil
      case Exists(path) => checkPath(path); Nil
      case Read(target, label) if scaffold.labels.contains(label) => Seq((target, OldKind))
      case Present(target) => Seq((target, PointerKind))
      case And(values) => values.map(value => (value, Boolean))
      case Or(values) => values.map(value => (value, Boolean))
      case Not(value) => Seq((value, Boolean))
      case _ => mismatch()
    }
  }
}

/** Evaluates one transition: label and pointer expressions against the old root.
  *
  * Iterative with an explicit continuation stack, like the Python original,
  * so that very deep construction DAGs do not exhaust the host stack. Results
  * are memoized by node identity within one step.
  */
private final class ScaffoldEvaluator(root: Node, created: Node, char: Char) {
  import Expr.*

  private sealed trait Frame
  private final case class Eval(expr: Expr) extends Frame
  private final case class Save(expr: Expr) extends Frame
  private case object NotK extends Frame
  private final case class ReadK(label: String) extends Frame
  private final case class EdgeK(field: String) extends Frame
  private case object PresentK extends Frame
  private final case class SelectK(yes: Expr, no: Expr) extends Frame
  private final case class LogicalK(isOr: Boolean, values: Vector[Expr], index: Int) extends Frame

  /** Memo values are either `Boolean` or `Option[Node]`, as in the Python `out` register. */
  private val memo = new java.util.IdentityHashMap[Expr, Any]()

  private def walk(path: Vector[String]): Option[Node] = {
    var node: Option[Node] = Some(root)
    val fields = path.iterator
    while (node.isDefined && fields.hasNext) {
      node = node.get.pointers(fields.next())
    }
    node
  }

  def evalBoolean(expr: Expr): Boolean = evaluate(expr).asInstanceOf[Boolean]

  def evalPointer(expr: Expr): Option[Node] = evaluate(expr).asInstanceOf[Option[Node]]

  private def evaluate(expr: Expr): Any = {
    val work = mutable.Stack[Frame](Eval(expr))
    var out: Any = null
    def outBoolean: Boolean = out.asInstanceOf[Boolean]
    def outPointer: Option[Node] = out.asInstanceOf[Option[Node]]
    while (work.nonEmpty) {
      work.pop() match {
        case Save(key) => memo.put(key, out)
        case NotK => out = !outBoolean
        case ReadK(label) => out = outPointer.exists(_.labels(label))
        case EdgeK(field) => out = outPointer.flatMap(_.pointers(field))
        case PresentK => out = outPointer.isDefined
        case SelectK(yes, no) => work.push(Eval(if (outBoolean) { yes } else { no }))
        case LogicalK(isOr, values, index) =>
          if (outBoolean == isOr) {
            out = isOr
          } else if (index + 1 == values.length) {
            out = !isOr
          } else {
            work.push(LogicalK(isOr, values, index + 1))
            work.push(Eval(values(index + 1)))
          }
        case Eval(current) =>
          if (memo.containsKey(current)) {
            out = memo.get(current)
          } else {
            work.push(Save(current))
            out = dispatch(current, work, out)
          }
      }
    }
    out
  }

  /** Evaluate a leaf directly, or push the continuation frames of a compound node. */
  private def dispatch(current: Expr, work: mutable.Stack[Frame], out: Any): Any = {
    current match {
      case Const(value) => value
      case Symbol(c) => char == c
      case Old(path, label) => walk(path).exists(_.labels(label))
      case Exists(path) => walk(path).isDefined
      case Not(value) => work.push(NotK); work.push(Eval(value)); out
      case And(values) => logical(isOr = false, values, work, out)
      case Or(values) => logical(isOr = true, values, work, out)
      case Self => Some(created)
      case Null => None
      case Pointer(path) => walk(path)
      case Select(condition, yes, no) => work.push(SelectK(yes, no)); work.push(Eval(condition)); out
      case Read(target, label) => work.push(ReadK(label)); work.push(Eval(target)); out
      case Edge(target, field) => work.push(EdgeK(field)); work.push(Eval(target)); out
      case Present(target) => work.push(PresentK); work.push(Eval(target)); out
    }
  }

  private def logical(isOr: Boolean, values: Vector[Expr], work: mutable.Stack[Frame], out: Any): Any = {
    if (values.isEmpty) {
      !isOr
    } else {
      work.push(LogicalK(isOr, values, 0))
      work.push(Eval(values(0)))
      out
    }
  }
}

/** Renders a scaffold as ordinary PEG rules: `S`, `B_i` labels, `P_i` pointers, shared `E_i`. */
private final class ScaffoldRenderer(scaffold: Scaffold) {
  import Expr.*

  private val labelNames: Map[String, String] = scaffold.labels.keys.zipWithIndex.map { case (key, i) => key -> s"B_$i" }.toMap
  private val pointerNames: Map[String, String] = scaffold.pointers.keys.zipWithIndex.map { case (key, i) => key -> s"P_$i" }.toMap
  private val shared = mutable.HashMap.empty[Expr, Int]
  private val pending = mutable.ArrayBuffer.empty[Expr]

  private def literal(c: Char): String = PhasePeg.literal(c)

  private def path(fields: Vector[String]): String = "." + fields.map(key => " " + pointerNames(key)).mkString

  /** Name the shared rule for `expr`, queueing it for rendering on first use. */
  private def expression(expr: Expr): String = {
    val index = shared.getOrElseUpdate(expr, { pending += expr; pending.length - 1 })
    s"E_$index"
  }

  private def render(name: String, expr: Expr): String = {
    val body = expr match {
      case Const(value) => if (value) { "\"\"" } else { "!\"\"" }
      case Symbol(c) => "&" + literal(c)
      case Old(fields, label) => "&(" + path(fields) + " " + labelNames(label) + ")"
      case Exists(fields) => "&(" + path(fields) + ")"
      case Not(value) => "!" + expression(value)
      case And(values) => if (values.isEmpty) { "\"\"" } else { values.map(expression).mkString(" ") }
      case Or(values) => if (values.isEmpty) { "!\"\"" } else { values.map(expression).mkString(" / ") }
      case Self => "\"\""
      case Null => "!\"\""
      case Pointer(fields) => path(fields)
      case Select(condition, yes, no) =>
        val c = expression(condition)
        val y = expression(yes)
        val n = expression(no)
        // Guard the fallback: a selected null pointer must remain null.
        s"$c $y / !$c $n"
      case Read(target, label) => "&(" + expression(target) + " " + labelNames(label) + ")"
      case Edge(target, field) => expression(target) + " " + pointerNames(field)
      case Present(target) => "&" + expression(target)
    }
    s"$name = $body;"
  }

  /** The rule lines, lazily.
    *
    * Single use: the iterator mutates this renderer's `shared`/`pending` state
    * as it is consumed (that is what lets `E_i` numbering follow first use, as
    * in the Python generator). Create a new `ScaffoldRenderer` for a second pass.
    */
  def rules: Iterator[String] = {
    val start = Iterator.single(
      s"S = ${labelNames(scaffold.accepting)} (" + scaffold.alphabet.map(literal).mkString(" / ") + ")* !.;"
    )
    val labelRules = scaffold.labels.iterator.map { case (key, expr) =>
      val base = if (scaffold.initial(key)) { "!. / " } else { "" }
      s"${labelNames(key)} = $base&. ${expression(expr)};"
    }
    val pointerRules = scaffold.pointers.iterator.map { case (key, expr) =>
      s"${pointerNames(key)} = &. ${expression(expr)};"
    }
    // `pending` grows while rendering; the cursor iterator re-checks its length lazily.
    val sharedRules = Iterator.iterate(0)(_ + 1).takeWhile(_ < pending.length).map(cursor => render(s"E_$cursor", pending(cursor)))
    start ++ labelRules ++ pointerRules ++ sharedRules
  }
}
