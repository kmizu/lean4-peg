package pal

import scala.collection.immutable.VectorMap
import Expr.{TRUE, FALSE}
import ScaffoldCircuit.{conjunction as AND, disjunction as OR}

final case class Position(var origin: Value[String], var offset: Bits, var radius: BigInt = 0)

/** Head order over a bounded round, without intermediate distance cells.
  * An evolving head is an old origin plus finite signed displacement. Old
  * pair differences are saved once per input node and normalized once at exit.
  */
final class WindowPositions(val circuit: Circuit, nameSeq: Seq[String], val radius: BigInt, prefix: String = "positions") {
  val names: Vector[String] = nameSeq.toVector
  require(names.size >= 2 && names.distinct.size == names.size, "at least two distinct head names are required")
  require(radius >= 0, "a nonnegative finite movement bound is required")
  val pairs: Vector[(String, String)] = names.combinations(2).map(pair => (pair(0), pair(1))).toVector
  val bank: WindowCounters = new WindowCounters(circuit, pairs.indices.map(i => s"$prefix.$i"), 2 * radius)
  val counters: VectorMap[(String, String), WindowCounter] = VectorMap.from(pairs.zip(bank.counters.values))
  val saved: VectorMap[(String, String), WindowCounter] = VectorMap.from(counters.map { case (pair, counter) => pair -> counter.clone() })
  val width: Int = bank.width + 1
  val heads: VectorMap[String, Position] = VectorMap.from(names.map(name => name -> Position(Value.constant(name).recode(names), Bits.constant(0, width))))
  val old: VectorMap[(String, String), (Expr, Expr, Expr, Bits)] = VectorMap.from(saved.map { case (pair, counter) =>
    pair -> (counter.quotient.zero(), counter.quotient.negative(), counter.quotient.positive(), counter.digits)
  })
  def move(head: String, amount: BigInt, enabled: Expr = TRUE): Unit = {
    if (enabled != FALSE && amount != 0) {
      val target = heads(head)
      require(target.radius + amount.abs <= radius, "head lineage exceeds the declared movement bound")
      target.offset = Bits.select(enabled, target.offset.add(amount), target.offset)
      target.radius += amount.abs
    }
  }
  def copy(target: String, source: String, enabled: Expr = TRUE): Unit = copyPosition(target, heads(source), enabled)
  def copyPosition(target: String, source: Position, enabled: Expr = TRUE): Unit = {
    val a = heads(target)
    a.origin = Value.select(enabled, source.origin, a.origin)
    a.offset = Bits.select(enabled, source.offset, a.offset)
    a.radius = if (enabled == TRUE) { source.radius } else { a.radius.max(source.radius) }
  }
  def selectPosition(which: Value[?]): Position = {
    val cases = heads.toVector.map { case (name, head) => (which.eqTo(name), head) }.filter(_._1 != FALSE)
    val origin = Value.encoded(names, Vector.tabulate(ScaffoldCircuit.bitWidth(names.size))(bit =>
      OR(cases.map { case (guard, head) => AND(guard, head.origin.bits(bit)) }*)), OR(cases.map(_._1)*))
    val offset = Bits(Vector.tabulate(width)(bit => OR(cases.map { case (guard, head) => AND(guard, head.offset.bits(bit)) }*)))
    Position(origin, offset, cases.map(_._2.radius).maxOption.getOrElse(BigInt(0)))
  }
  def originCases(left: String, right: String): Vector[((String, String), Expr, Expr)] = positionCases(heads(left), heads(right))
  def positionCases(a: Position, b: Position): Vector[((String, String), Expr, Expr)] = {
    pairs.map { case pair @ (i, j) => (pair, AND(a.origin.eqTo(i), b.origin.eqTo(j)), AND(a.origin.eqTo(j), b.origin.eqTo(i))) }
  }
  def compare(left: String, right: String): (Expr, Expr) = {
    if (left == right) { (TRUE, FALSE) } else { comparePositions(heads(left), heads(right)) }
  }
  def comparePositions(a: Position, b: Position): (Expr, Expr) = {
    var near = OR(names.map(name => AND(a.origin.eqTo(name), b.origin.eqTo(name)))*)
    var negative = FALSE
    var digits = Bits.constant(0, width)
    for ((pair, forward, backward) <- positionCases(a, b)) {
      val (zero, below, above, value) = old(pair)
      near = OR(near, AND(OR(forward, backward), zero))
      negative = OR(negative, AND(forward, below), AND(backward, above))
      digits = Bits.select(forward, value, digits)
      digits = Bits.select(backward, value.negated(), digits)
    }
    val difference = digits.plus(a.offset).plus(b.offset.negated())
    (AND(near, difference.zero()), OR(negative, AND(near, difference.negative())))
  }
  def equal(left: String, right: String): Expr = compare(left, right)._1
  def less(left: String, right: String): Expr = compare(left, right)._2
  def commit(): Unit = {
    for (((left, right), target) <- counters) {
      target.reset()
      for ((pair, forward, backward) <- originCases(left, right)) {
        target.copyFrom(saved(pair), forward)
        target.copyFrom(saved(pair), backward, negateValue = true)
      }
      val a = heads(left)
      val b = heads(right)
      target.addWord(a.offset.plus(b.offset.negated()), a.radius + b.radius)
    }
    bank.commit()
  }
}
