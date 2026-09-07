package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Expr.{TRUE, FALSE, SELF, NULL}
import ScaffoldCircuit.{choose, choosePointer, neg, conjunction, disjunction}

/** Pack a finite sequence of local scaffold transitions into one input node.
  *
  * Virtual cells have (physical node, finite slot) addresses. Queries of slots
  * already made in this round use their construction expressions. Queries of old
  * nodes read slot-indexed fields. Self references survive as tagged self edges;
  * there are no queries of the physical node under construction and no equality
  * test on pointers. This pass does not derive how many transitions to schedule.
  *
  * Port of `scaffold_round.py`.
  */
object ScaffoldRound {

  def packRound(
      stages: Seq[Scaffold],
      inputSymbols: Option[Seq[collection.Map[Char, Expr]]] = None,
      alphabet: Option[String] = None
  ): Scaffold = {
    new RoundBuilder(stages, inputSymbols, alphabet).build()
  }
}

/** A virtual cell address: guards of the local slots it may be, else the old node `prior` tagged by `tag`. */
final case class Address(local: VectorMap[Int, Expr], prior: Expr, tag: Value[Int])

/** A translated source expression: a Boolean equation or a virtual address. */
type RoundValue = Expr | Address

/** Translates every stage of a round into slot-indexed labels, edges and tag bits. */
class RoundBuilder(
    stageSeq: Seq[Scaffold],
    inputSymbolSeq: Option[Seq[collection.Map[Char, Expr]]] = None,
    alphabetOverride: Option[String] = None
) {
  import RoundBuilder.{label, field, tagBit}

  val stages: Vector[Scaffold] = stageSeq.toVector
  if (stages.isEmpty) { throw new IllegalArgumentException("a round needs at least one transition") }
  val source: Scaffold = stages.head
  val alphabet: String = alphabetOverride.getOrElse(source.alphabet)

  /** Per stage, the Boolean guard standing for each source input symbol. */
  val inputSymbols: Vector[VectorMap[Char, Expr]] = inputSymbolSeq match {
    case None => stages.map(stage => VectorMap.from(stage.alphabet.map(char => char -> Expr.symbol(char))))
    case Some(mappings) => mappings.toVector.map(mapping => VectorMap.from(mapping))
  }
  if (inputSymbols.length != stages.length ||
      inputSymbols.zip(stages).exists { case (mapping, stage) => mapping.keySet != stage.alphabet.toSet }) {
    throw new IllegalArgumentException("one complete input-symbol substitution per transition required")
  }
  for (stage <- stages) {
    if (stage.initial != source.initial || stage.pointers.keySet != source.pointers.keySet || stage.alphabet != source.alphabet) {
      throw new IllegalArgumentException("round transitions need a common state schema and alphabet")
    }
  }

  val tags: Vector[Int] = stages.indices.toVector
  val bits: Int = ScaffoldCircuit.bitWidth(tags.length)
  val labels: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.empty
  val pointers: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.empty
  val initial: mutable.LinkedHashMap[String, Boolean] = mutable.LinkedHashMap.empty
  val slotLabels: mutable.ArrayBuffer[mutable.LinkedHashMap[String, Expr]] = mutable.ArrayBuffer.empty
  val slotPointers: mutable.ArrayBuffer[mutable.LinkedHashMap[String, Address]] = mutable.ArrayBuffer.empty
  val zeroTag: Value[Int] = Value.constant(0).recode(tags)
  val empty: Address = Address(VectorMap.empty, NULL, zeroTag)

  /** The translated label `key` of slot `slot` (Python `self.slot_labels[slot][key]`). */
  protected def slotLabel(slot: Int, key: String): Expr = slotLabels(slot)(key)

  /** The translated pointer `key` of slot `slot` (Python `self.slot_pointers[slot][key]`). */
  protected def slotPointer(slot: Int, key: String): Address = slotPointers(slot)(key)

  def select(guard: Expr, yes: Address, no: Address): Address = {
    if (guard == TRUE) {
      yes
    } else if (guard == FALSE) {
      no
    } else {
      val slots = CPythonSetOrder.unionKeys(yes.local.keys.toSeq, no.local.keys.toSeq)
      val local = slots.map(slot => slot -> choose(guard, yes.local.getOrElse(slot, FALSE), no.local.getOrElse(slot, FALSE)))
      Address(
        VectorMap.from(local.filter { case (_, g) => g != FALSE }),
        choosePointer(guard, yes.prior, no.prior),
        Value.select(guard, yes.tag, no.tag)
      )
    }
  }

  def exists(target: Address): Expr = {
    val prior = if (target.prior != NULL) { Expr.present(target.prior) } else { FALSE }
    disjunction((target.local.values.toVector :+ prior)*)
  }

  /** The slots an old-node tag may denote: none, one constant slot, or all of them. */
  def possibleTags(tag: Value[Int]): Vector[Int] = {
    if (tag.valid == FALSE) {
      Vector.empty
    } else if (tag.bits.forall(bit => bit == TRUE || bit == FALSE)) {
      val index = tag.bits.zipWithIndex.collect { case (bit, i) if bit == TRUE => 1 << i }.sum
      if (index < tag.domain.length) { Vector(tag.domain(index)) } else { Vector.empty }
    } else {
      tags
    }
  }

  def read(target: Address, key: String): Expr = {
    val values = mutable.ArrayBuffer.empty[Expr]
    for ((slot, guard) <- target.local) { values += conjunction(guard, slotLabel(slot, key)) }
    if (target.prior != NULL) {
      for (slot <- possibleTags(target.tag)) {
        val guard = target.tag.eqTo(slot)
        if (guard != FALSE) { values += conjunction(guard, Expr.read(target.prior, label(slot, key))) }
      }
    }
    disjunction(values.toSeq*)
  }

  def follow(target: Address, key: String): Address = {
    var result = empty
    if (target.prior != NULL) {
      var prior: Expr = NULL
      var tagBits: Vector[Expr] = Vector.fill(bits)(FALSE)
      for (slot <- possibleTags(target.tag)) {
        val guard = target.tag.eqTo(slot)
        if (guard != FALSE) {
          prior = choosePointer(guard, Expr.edge(target.prior, field(slot, key)), prior)
          tagBits = tagBits.zipWithIndex.map { case (value, bit) =>
            choose(guard, Expr.read(target.prior, tagBit(slot, key, bit)), value)
          }
        }
      }
      result = Address(VectorMap.empty, prior, Value.encoded(tags, tagBits))
    }
    for ((slot, guard) <- target.local) { result = select(guard, slotPointer(slot, key), result) }
    result
  }

  private def bool(value: RoundValue): Expr = {
    value match {
      case expr: Expr => expr
      case _ => throw new IllegalStateException("Boolean equation expected")
    }
  }

  private def address(value: RoundValue): Address = {
    value match {
      case target: Address => target
      case _ => throw new IllegalStateException("pointer address expected")
    }
  }

  private def walk(root: Address, path: Vector[String]): Address = path.foldLeft(root)((target, key) => follow(target, key))

  private sealed trait Task
  private final case class Eval(expr: Expr) extends Task
  private final case class Save(expr: Expr) extends Task
  private case object NotTask extends Task
  private final case class ReadTask(key: String) extends Task
  private final case class EdgeTask(key: String) extends Task
  private case object PresentTask extends Task
  private final case class Logical(isAnd: Boolean, args: Vector[Expr], index: Int, values: mutable.ArrayBuffer[Expr]) extends Task
  private final case class Branch(yes: Expr, no: Expr) extends Task
  private final case class Yes(guard: Expr, no: Expr) extends Task
  private final case class SelectTask(guard: Expr, yes: Address) extends Task

  /** Translate one source equation for `slot`, reading the previous node through `root`.
    *
    * Resolve guards first. An ingestion slot often disables the entire source
    * transition; eagerly translating both branches would expand it anyway.
    * `memo` is keyed by source node identity (Python `id(expr)`).
    */
  def translate(expression: Expr, slot: Int, root: Address, memo: java.util.IdentityHashMap[Expr, RoundValue]): RoundValue = {
    import Expr.{Const, Symbol, Self, Null, Old, Exists, Not, And, Or, Pointer, Select, Read, Edge, Present}
    val work = mutable.Stack[Task](Eval(expression))
    var value: RoundValue = FALSE
    while (work.nonEmpty) {
      work.pop() match {
        case Save(expr) => memo.put(expr, value)
        case NotTask => value = neg(bool(value))
        case ReadTask(key) => value = read(address(value), key)
        case EdgeTask(key) => value = follow(address(value), key)
        case PresentTask => value = exists(address(value))
        case Logical(isAnd, args, index, values) =>
          val current = bool(value)
          values += current
          if (current == (if (isAnd) { FALSE } else { TRUE })) {
            ()
          } else if (index + 1 == args.length) {
            value = if (isAnd) { conjunction(values.toSeq*) } else { disjunction(values.toSeq*) }
          } else {
            work.push(Logical(isAnd, args, index + 1, values))
            work.push(Eval(args(index + 1)))
          }
        case Branch(yes, no) =>
          val guard = bool(value)
          if (guard == TRUE || guard == FALSE) {
            work.push(Eval(if (guard == TRUE) { yes } else { no }))
          } else {
            work.push(Yes(guard, no))
            work.push(Eval(yes))
          }
        case Yes(guard, no) =>
          work.push(SelectTask(guard, address(value)))
          work.push(Eval(no))
        case SelectTask(guard, yes) => value = select(guard, yes, address(value))
        case Eval(expr) =>
          if (memo.containsKey(expr)) {
            value = memo.get(expr)
          } else {
            work.push(Save(expr))
            expr match {
              case Const(flag) => value = if (flag) { TRUE } else { FALSE }
              case Symbol(char) => value = inputSymbols(slot)(char)
              case Self => value = Address(VectorMap(slot -> TRUE), NULL, zeroTag)
              case Null => value = empty
              case Pointer(path) => value = walk(root, path)
              case Old(path, key) => value = read(walk(root, path), key)
              case Exists(path) => value = exists(walk(root, path))
              case Read(target, key) =>
                work.push(ReadTask(key))
                work.push(Eval(target))
              case Edge(target, key) =>
                work.push(EdgeTask(key))
                work.push(Eval(target))
              case Not(inner) =>
                work.push(NotTask)
                work.push(Eval(inner))
              case Present(target) =>
                work.push(PresentTask)
                work.push(Eval(target))
              case And(args) =>
                value = TRUE
                if (args.nonEmpty) {
                  work.push(Logical(true, args, 0, mutable.ArrayBuffer.empty))
                  work.push(Eval(args(0)))
                }
              case Or(args) =>
                value = FALSE
                if (args.nonEmpty) {
                  work.push(Logical(false, args, 0, mutable.ArrayBuffer.empty))
                  work.push(Eval(args(0)))
                }
              case Select(condition, yes, no) =>
                work.push(Branch(yes, no))
                work.push(Eval(condition))
            }
          }
      }
    }
    value
  }

  /** The address of the previous physical node as seen from slot 0. */
  protected def previousRoot(): Address = Address(VectorMap.empty, Expr.pointer(Nil), Value.constant(tags.last).recode(tags))

  /** Record a translated label as `s{slot}.label.{key}`. */
  protected def emitLabel(slot: Int, key: String, expression: Expr): Unit = {
    val name = label(slot, key)
    initial(name) = stages(slot).initial(key)
    labels(name) = expression
  }

  /** Record a translated pointer as `s{slot}.edge.{key}` plus its `s{slot}.tag.{key}.{bit}` labels. */
  protected def emitPointer(slot: Int, key: String, target: Address): Unit = {
    var edge = target.prior
    var tag: Value[Int] = target.tag
    for ((local, guard) <- target.local) {
      edge = choosePointer(guard, SELF, edge)
      tag = Value.select(guard, Value.constant(local), tag)
    }
    pointers(field(slot, key)) = edge
    for ((expression, bit) <- tag.recode(tags).bits.zipWithIndex) {
      val name = tagBit(slot, key, bit)
      initial(name) = false
      labels(name) = expression
    }
  }

  def build(): Scaffold = {
    var root = previousRoot()
    for ((stage, slot) <- stages.zipWithIndex) {
      val memo = new java.util.IdentityHashMap[Expr, RoundValue]()
      val stageLabels = mutable.LinkedHashMap.empty[String, Expr]
      for ((key, expr) <- stage.labels) { stageLabels(key) = bool(translate(expr, slot, root, memo)) }
      val stagePointers = mutable.LinkedHashMap.empty[String, Address]
      for ((key, expr) <- stage.pointers) { stagePointers(key) = address(translate(expr, slot, root, memo)) }
      slotLabels += stageLabels
      slotPointers += stagePointers
      for ((key, expression) <- stageLabels) { emitLabel(slot, key, expression) }
      for ((key, target) <- stagePointers) { emitPointer(slot, key, target) }
      root = Address(VectorMap(slot -> TRUE), NULL, zeroTag)
    }
    val accepting = label(tags.last, stages.last.accepting)
    new Scaffold(initial, labels, pointers, accepting, alphabet)
  }
}

object RoundBuilder {

  def label(slot: Int, key: String): String = s"s$slot.label.$key"

  def field(slot: Int, key: String): String = s"s$slot.edge.$key"

  def tagBit(slot: Int, key: String, bit: Int): String = s"s$slot.tag.$key.$bit"
}

/** Reproduces the iteration order of CPython's `dict_keys | dict_keys` for small non-negative ints.
  *
  * `RoundBuilder.select` merges the local slots of two addresses with that
  * union, and the resulting order decides how the multiplexers nest, hence the
  * rule numbering of the emitted PEG. Small ints hash to themselves, so the
  * order follows CPython's open-addressing table: linear runs of nine probes,
  * then perturbed jumps, growing by four while under fifty thousand entries.
  * `PySet_New(dict)` first sizes the table for the left operand; the right
  * operand's keys are then added one at a time.
  */
private[pal] object CPythonSetOrder {
  private val MinSize = 8
  private val LinearProbes = 9
  private val PerturbShift = 5
  private val Empty = -1

  def unionKeys(first: Seq[Int], second: Seq[Int]): Vector[Int] = {
    val table = new Table
    // set_update_internal(dict): one big resize before inserting the dict's keys.
    if (first.size * 5 >= table.mask * 3) { table.resize(first.size * 2) }
    first.foreach(table.add)
    second.foreach(table.add)
    table.keysInSlotOrder
  }

  private final class Table {
    private var keys: Array[Int] = Array.fill(MinSize)(Empty)
    private var fill = 0

    def mask: Int = keys.length - 1

    /** The slot holding `key`, or the empty slot the probe sequence reaches first. */
    private def find(table: Array[Int], key: Int): Int = {
      val m = table.length - 1
      var i = key & m
      var perturb = key.toLong
      var found = -1
      while (found < 0) {
        val probes = if (i + LinearProbes <= m) { LinearProbes } else { 0 }
        var entry = i
        var j = 0
        while (found < 0 && j <= probes) {
          if (table(entry) == Empty || table(entry) == key) { found = entry }
          entry += 1
          j += 1
        }
        if (found < 0) {
          perturb >>>= PerturbShift
          i = ((i.toLong * 5 + 1 + perturb) & m).toInt
        }
      }
      found
    }

    def add(key: Int): Unit = {
      val slot = find(keys, key)
      if (keys(slot) != key) {
        keys(slot) = key
        fill += 1
        if (fill * 5 >= mask * 3) { resize(if (fill > 50000) { fill * 2 } else { fill * 4 }) }
      }
    }

    def resize(minused: Int): Unit = {
      var size = MinSize
      while (size <= minused) { size <<= 1 }
      val fresh = Array.fill(size)(Empty)
      for (key <- keys if key != Empty) { fresh(find(fresh, key)) = key }
      keys = fresh
    }

    def keysInSlotOrder: Vector[Int] = keys.iterator.filter(_ != Empty).toVector
  }
}
