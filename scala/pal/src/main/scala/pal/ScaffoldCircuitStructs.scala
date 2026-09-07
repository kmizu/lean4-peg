package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Expr.{TRUE, FALSE}
import ScaffoldCircuit.{conjunction, disjunction, neg}
import Ref.{EMPTY, NEW, PREVIOUS}

/** Persistent stack and tape operations emitted as finite scaffold equations.
  *
  * All loops here range over a fixed construction-time cell layout. Several cells
  * may be allocated on the same physical scaffold node. Their labels and pointers
  * are read through Circuit's local snapshots until the node is emitted.
  *
  * Port of `scaffold_circuit_structs.py`. Python's `finalize()` methods are
  * `commit()` here (`Object.finalize` is deprecated on the JVM).
  */

/** A cell tag: the layout name and the slot index within that name. */
type CellTag = (String, Int)

/** A pool of finitely many cells, each with `below`, `tag`, `value` and `data` fields. */
final class StackPool(val circuit: Circuit, layoutFields: Iterable[(String, Int)], payloadValues: Seq[Any] = Vector(None)) {
  val layout: VectorMap[String, Int] = VectorMap.from(layoutFields)
  val tags: Vector[CellTag] = layout.toVector.flatMap { case (name, count) => (0 until count).map(index => (name, index)) }
  if (tags.isEmpty) { throw new IllegalArgumentException("nonempty finite cell layout required") }
  val used: mutable.LinkedHashMap[String, Int] = mutable.LinkedHashMap.empty
  val payload: Vector[Any] = payloadValues.toVector
  val tagIds: Map[CellTag, Int] = tags.zipWithIndex.toMap
  val prefix: String = s"pool${circuit.pools.size}"
  circuit.pools += this

  def key(tag: CellTag, field: String): String = s"$prefix.c${tagIds(tag)}.$field"

  /** Read scalar `field` of the cell selected by `tag`, defaulting to `initial` for no cell.
    *
    * Tag equality guards are pairwise disjoint. Encode a field read as one
    * sum of products per bit instead of a long nest of binary multiplexers.
    * This also shares the validity test across all slots of this pool.
    */
  def scalar[A](ref: Ref, tag: Value[?], field: String, domain: Seq[A], initial: A): Value[A] = {
    val default = Value.constant(initial).recode(domain)
    val choices = tags.flatMap { variant =>
      val condition = tag.eqTo(variant)
      if (condition != FALSE) { Some(condition -> circuit.get(ref, key(variant, field), domain, initial)) } else { None }
    }
    val missing = neg(disjunction(choices.map(_._1)*))
    val bits = default.bits.zipWithIndex.map { case (bit, index) =>
      disjunction((conjunction(missing, bit) +: choices.map { case (condition, value) => conjunction(condition, value.bits(index)) })*)
    }
    val valid = disjunction((missing +: choices.map { case (condition, value) => conjunction(condition, value.valid) })*)
    Value.encoded(domain, bits, valid)
  }

  /** Read pointer `field` of the cell selected by `tag`. */
  def pointer(ref: Ref, tag: Value[?], field: String): Ref = {
    var answer = EMPTY
    for (variant <- tags) {
      val condition = tag.eqTo(variant)
      if (condition != FALSE) {
        val value = circuit.getRef(ref, key(variant, field))
        answer = Ref.select(condition, value, answer)
      }
    }
    answer
  }

  /** Allocate the next (or the given) slot of `name`; returns the new cell and its tag. */
  def allocate(name: String, previous: Ref, previousTag: Value[?], value: Ref, data: Value[?], enabled: Expr, slot: Option[Int] = None): (Ref, Value[CellTag]) = {
    val index = slot.getOrElse(used.getOrElse(name, 0))
    if (index >= layout(name)) { throw new IllegalArgumentException(s"finite stack cell layout exhausted for $name") }
    used(name) = math.max(used.getOrElse(name, 0), index + 1)
    val tag: CellTag = (name, index)
    circuit.putRef(key(tag, "below"), Ref.select(enabled, previous, circuit.currentRefs.getOrElse(key(tag, "below"), EMPTY)))
    circuit.put(key(tag, "tag"),
      Value.select[Any](enabled, previousTag, circuit.currentValues.getOrElse(key(tag, "tag"), Value.constant(tags.head))),
      tags, tags.head)
    circuit.putRef(key(tag, "value"), Ref.select(enabled, value, circuit.currentRefs.getOrElse(key(tag, "value"), EMPTY)))
    circuit.put(key(tag, "data"),
      Value.select[Any](enabled, data, circuit.currentValues.getOrElse(key(tag, "data"), Value.constant(payload.head))),
      payload, payload.head)
    (NEW, Value.constant(tag).recode(tags))
  }
}

/** A persistent stack rooted in a pool cell; `commit()` writes the root back. */
final class Stack(val pool: StackPool, val name: String, allocation: Option[String] = None) {
  val circuit: Circuit = pool.circuit
  val allocationName: String = allocation.getOrElse(name)
  val rootKey: String = s"${pool.prefix}.$name.root"
  val tagKey: String = s"${pool.prefix}.$name.tag"
  var top: Ref = circuit.getRef(PREVIOUS, rootKey)
  var tag: Value[CellTag] = circuit.get(PREVIOUS, tagKey, pool.tags, pool.tags.head)

  def empty(): Expr = neg(top.present())

  def peek(): (Ref, Value[Any]) = {
    (pool.pointer(top, tag, "value"), pool.scalar(top, tag, "data", pool.payload, pool.payload.head))
  }

  def pop(enabled: Expr = TRUE): (Ref, Value[Any]) = {
    val value = peek()
    drop(enabled)
    value
  }

  def drop(enabled: Expr = TRUE): Unit = {
    val below = pool.pointer(top, tag, "below")
    val belowTag = pool.scalar(top, tag, "tag", pool.tags, pool.tags.head)
    top = Ref.select(enabled, below, top)
    tag = Value.select(enabled, belowTag, tag)
  }

  def push(value: Ref = EMPTY, data: Option[Value[Any]] = None, enabled: Expr = TRUE, slot: Option[Int] = None): Unit = {
    if (enabled != FALSE) {
      val payload = data.getOrElse(Value.constant(pool.payload.head))
      val (newTop, newTag) = pool.allocate(allocationName, top, tag, value, payload, enabled, slot)
      top = Ref.select(enabled, newTop, top)
      tag = Value.select(enabled, newTag, tag)
    }
  }

  def clear(enabled: Expr = TRUE): Unit = {
    top = Ref.select(enabled, EMPTY, top)
  }

  def copyFrom(other: Stack, enabled: Expr = TRUE): Unit = {
    if (pool ne other.pool) { throw new IllegalArgumentException("aliased stacks must share a declared finite cell pool") }
    top = Ref.select(enabled, other.top, top)
    tag = Value.select(enabled, other.tag, tag)
  }

  /** Python `finalize()`: write the root and tag back into the circuit. */
  def commit(): Unit = {
    circuit.putRef(rootKey, top)
    circuit.put(tagKey, tag)
  }
}

/** A two-stack tape with a focus symbol.
  *
  * Python accepted `slots` as one count for both sides or a `(left, right)`
  * pair; here the constructor takes the single count and `Tape.withSides`
  * takes the pair. Moving copies the focus symbol, never a stack cell. Left
  * and right cell tags therefore have separate finite domains, avoiding an
  * unnecessary cross-product during computed-cell reads.
  */
final class Tape private (
    val circuit: Circuit,
    val name: String,
    alphabetValues: Iterable[Any],
    sizes: (Int, Int),
    val blank: Any,
    pool: Option[StackPool]
) {

  /** `slots` cells on each side (Python `Tape(circuit, name, alphabet, slots=int, ...)`). */
  def this(circuit: Circuit, name: String, alphabet: Iterable[Any], slots: Int = 1, blank: Any = '_', pool: Option[StackPool] = None) = {
    this(circuit, name, alphabet, (slots, slots), blank, pool)
  }

  val alphabet: Vector[Any] = alphabetValues.toVector

  val (left: Stack, right: Stack) = {
    pool match {
      case None =>
        def side(suffix: String, count: Int): Stack = new Stack(new StackPool(circuit, Vector((name + suffix) -> count), alphabet), name + suffix)
        (side(".l", sizes._1), side(".r", sizes._2))
      case Some(shared) =>
        // A Program may assign the same construction slot to mutually exclusive
        // tape moves. Stack roots stay distinct; only their cell storage is shared.
        (new Stack(shared, name + ".l", Some("cells")), new Stack(shared, name + ".r", Some("cells")))
    }
  }

  val symbolKey: String = name + ".symbol"
  var focus: Value[Any] = circuit.get(PREVIOUS, symbolKey, alphabet, blank)

  def write(value: Value[Any], enabled: Expr = TRUE): Unit = {
    focus = Value.select(enabled, value.recode(alphabet), focus)
  }

  def reset(enabled: Expr = TRUE): Unit = {
    left.clear(enabled)
    right.clear(enabled)
    write(Value.constant(blank), enabled)
  }

  def move(direction: Int, enabled: Expr = TRUE, slot: Option[Int] = None): Unit = {
    if (enabled != FALSE) {
      val (pushed, popped) = if (direction == 1) { (left, right) } else { (right, left) }
      if (direction == -1) { circuit.require(neg(popped.empty()), enabled) }
      val empty = popped.empty()
      val (_, popValue) = popped.pop(enabled)
      val value = if (popValue.domain != alphabet) {
        val recoded = Value(alphabet.map(char => char -> popValue.eqTo(char)))
        circuit.require(recoded.valid, conjunction(enabled, neg(empty)))
        recoded
      } else {
        popValue
      }
      pushed.push(data = Some(focus), enabled = enabled, slot = slot)
      write(Value.select(empty, Value.constant(blank), value), enabled)
    }
  }

  /** Python `finalize()`. */
  def commit(): Unit = {
    left.commit()
    right.commit()
    circuit.put(symbolKey, focus)
  }
}

object Tape {

  /** Python `Tape(..., slots=(left, right), ...)`: different cell counts per side. */
  def withSides(circuit: Circuit, name: String, alphabet: Iterable[Any], slots: (Int, Int), blank: Any = '_', pool: Option[StackPool] = None): Tape = {
    new Tape(circuit, name, alphabet, slots, blank, pool)
  }
}

/** A signed unary counter: two stacks of which at most one is nonempty.
  *
  * The stacks are Python's `pos`/`neg` attributes, named `positiveStack` /
  * `negativeStack` here so that `neg` keeps meaning Boolean negation. They are
  * reassignable because `scaffold_window_stream` copies counters field-wise.
  */
final class Counter(pools: Map[String, StackPool], val name: String, allocationName: Option[String] = None) {

  def this(pool: StackPool, name: String, allocationName: Option[String]) = this(Map("pos" -> pool, "neg" -> pool), name, allocationName)

  def this(pool: StackPool, name: String) = this(pool, name, None)

  var positiveStack: Stack = new Stack(pools("pos"), name + ".pos", allocationName)
  var negativeStack: Stack = new Stack(pools("neg"), name + ".neg", allocationName)

  /** Python-name alias of `positiveStack`. */
  def pos: Stack = positiveStack

  def positive(): Expr = neg(positiveStack.empty())

  def negative(): Expr = neg(negativeStack.empty())

  def zero(): Expr = conjunction(positiveStack.empty(), negativeStack.empty())

  def inc(enabled: Expr = TRUE, slot: Option[Int] = None): Unit = {
    val empty = negativeStack.empty()
    negativeStack.drop(conjunction(enabled, neg(empty)))
    positiveStack.push(enabled = conjunction(enabled, empty), slot = slot)
  }

  def dec(enabled: Expr = TRUE, slot: Option[Int] = None): Unit = {
    val empty = positiveStack.empty()
    positiveStack.drop(conjunction(enabled, neg(empty)))
    negativeStack.push(enabled = conjunction(enabled, empty), slot = slot)
  }

  def reset(enabled: Expr = TRUE): Unit = {
    positiveStack.clear(enabled)
    negativeStack.clear(enabled)
  }

  def copyFrom(other: Counter, enabled: Expr = TRUE): Unit = {
    positiveStack.copyFrom(other.positiveStack, enabled)
    negativeStack.copyFrom(other.negativeStack, enabled)
  }

  /** Python `finalize()`. */
  def commit(): Unit = {
    positiveStack.commit()
    negativeStack.commit()
  }
}

object Counter {
  /** Python `Counter(pool, ...)` with a per-side pool dictionary. */
  def withPools(pools: Map[String, StackPool], name: String, allocationName: Option[String] = None): Counter = {
    new Counter(pools, name, allocationName)
  }
}

/** A FIFO queue built from seven stacks and two counters with amortized rotation. */
final class Queue(pools: Map[String, StackPool], counterPools: Map[String, StackPool], val name: String, val sharedSlots: Boolean = false) {

  def this(pool: StackPool, counterPool: StackPool, name: String, sharedSlots: Boolean) = {
    this(Queue.NAMES.map(role => role -> pool).toMap, Map("m" -> counterPool, "c" -> counterPool), name, sharedSlots)
  }

  def this(pool: StackPool, counterPool: StackPool, name: String) = this(pool, counterPool, name, false)

  val circuit: Circuit = pools("F").circuit
  private val allocation: Option[String] = if (sharedSlots) { Some("cells") } else { None }

  /** The seven role stacks (Python `self.s`). */
  val stacks: VectorMap[String, Stack] = VectorMap.from(Queue.NAMES.map(role => role -> new Stack(pools(role), s"$name.$role", allocation)))
  val m: Counter = new Counter(counterPools("m"), name + ".m", allocation)
  val c: Counter = new Counter(counterPools("c"), name + ".c", allocation)
  val phaseKey: String = name + ".phase"
  var phase: Value[String] = circuit.get(PREVIOUS, phaseKey, Vector("idle", "rev", "copy"), "idle")

  private def setPhase(value: String, enabled: Expr): Unit = {
    phase = Value.select(enabled, Value.constant(value), phase)
  }

  private def slotFor(index: Int = 0): Option[Int] = if (sharedSlots) { Some(index) } else { None }

  def push(value: Ref, enabled: Expr = TRUE): Unit = {
    val idle = phase.eqTo("idle")
    stacks("B").push(value, enabled = conjunction(enabled, idle), slot = slotFor())
    stacks("B2").push(value, enabled = conjunction(enabled, neg(idle)), slot = slotFor())
    c.dec(enabled, slot = slotFor())
  }

  def pop(enabled: Expr = TRUE): Ref = {
    circuit.require(neg(stacks("F").empty()), enabled)
    val (value, _) = stacks("F").pop(enabled)
    c.dec(enabled, slot = slotFor())
    val rotating = conjunction(enabled, neg(phase.eqTo("idle")))
    m.dec(rotating, slot = slotFor())
    maybeFinish(rotating)
    value
  }

  def empty(): Expr = conjunction(stacks("F").empty(), stacks("B").empty(), phase.eqTo("idle"))

  def clear(enabled: Expr = TRUE): Unit = {
    for (stack <- stacks.values) { stack.clear(enabled) }
    m.reset(enabled)
    c.reset(enabled)
    setPhase("idle", enabled)
  }

  private def start(enabled: Expr): Unit = {
    stacks("WF").copyFrom(stacks("F"), enabled)
    stacks("WB").copyFrom(stacks("B"), enabled)
    for (role <- Seq("Fr", "Br", "B2")) { stacks(role).clear(enabled) }
    m.reset(enabled)
    setPhase("rev", enabled)
  }

  private def maybeFinish(enabled: Expr): Unit = {
    val finish = conjunction(enabled, phase.eqTo("copy"), m.zero())
    stacks("F").copyFrom(stacks("Br"), finish)
    stacks("B").copyFrom(stacks("B2"), finish)
    for (role <- Seq("Br", "B2", "Fr")) { stacks(role).clear(finish) }
    setPhase("idle", finish)
  }

  private def unit(enabled: Expr): Unit = {
    val reverse = conjunction(enabled, phase.eqTo("rev"))
    val copy = conjunction(enabled, phase.eqTo("copy"))
    val rear = conjunction(reverse, neg(stacks("WB").empty()))
    val front = conjunction(reverse, neg(stacks("WF").empty()))
    val (rearValue, _) = stacks("WB").pop(rear)
    stacks("Br").push(rearValue, enabled = rear, slot = slotFor())
    c.inc(rear, slot = slotFor())
    c.inc(rear, slot = slotFor(1))
    val (frontValue, _) = stacks("WF").pop(front)
    stacks("Fr").push(frontValue, enabled = front, slot = slotFor())
    m.inc(front, slot = slotFor())
    val finishedReversal = conjunction(reverse, neg(disjunction(rear, front)))
    setPhase("copy", finishedReversal)
    maybeFinish(finishedReversal)
    val copying = conjunction(copy, m.positive(), neg(stacks("Fr").empty()))
    val (copyValue, _) = stacks("Fr").pop(copying)
    stacks("Br").push(copyValue, enabled = copying, slot = slotFor())
    m.dec(copying, slot = slotFor())
    maybeFinish(copy)
  }

  def work(enabled: Expr = TRUE): Unit = {
    if (sharedSlots) { throw new IllegalArgumentException("shared queue cells require one work_unit per physical transition") }
    for (_ <- 0 until 3) { workUnit(enabled) }
  }

  /** One rotation instruction; shared-slot users must schedule it explicitly. */
  def workUnit(enabled: Expr = TRUE): Unit = {
    start(conjunction(enabled, phase.eqTo("idle"), c.negative()))
    unit(conjunction(enabled, neg(phase.eqTo("idle"))))
  }

  def copyFrom(other: Queue, enabled: Expr = TRUE): Unit = {
    for (role <- Queue.NAMES) { stacks(role).copyFrom(other.stacks(role), enabled) }
    m.copyFrom(other.m, enabled)
    c.copyFrom(other.c, enabled)
    phase = Value.select(enabled, other.phase, phase)
  }

  /** Python `finalize()`. */
  def commit(): Unit = {
    for (stack <- stacks.values) { stack.commit() }
    m.commit()
    c.commit()
    circuit.put(phaseKey, phase)
  }
}

object Queue {
  val NAMES: Vector[String] = Vector("F", "B", "Fr", "Br", "WF", "WB", "B2")

  /** Python `Queue(pool_dict, counter_pool_dict, ...)`. */
  def withPools(pools: Map[String, StackPool], counterPools: Map[String, StackPool], name: String, sharedSlots: Boolean = false): Queue = {
    new Queue(pools, counterPools, name, sharedSlots)
  }
}
