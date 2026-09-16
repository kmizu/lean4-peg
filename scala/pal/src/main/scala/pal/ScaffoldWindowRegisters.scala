package pal

import scala.collection.immutable.VectorMap
import Expr.{TRUE, FALSE}
import Ref.EMPTY
import ScaffoldCircuit.{conjunction as AND, disjunction as OR, choose, neg}
import ScaffoldWindowRegisters.selectValue

final case class Register(origin: Value[String], reverse: Expr, digits: Bits, radius: BigInt = 0)

object ScaffoldWindowRegisters {
  def selectValue[A](cases: Iterable[(Expr, Value[A])], domain: Seq[A]): Value[A] = {
    val values = cases.iterator.filter(_._1 != FALSE).map { case (guard, value) => (guard, value.recode(domain)) }.toVector
    Value.encoded(domain, Vector.tabulate(ScaffoldCircuit.bitWidth(domain.size))(bit =>
      OR(values.map { case (guard, value) => AND(guard, value.bits(bit)) }*)),
      OR(values.map { case (guard, value) => AND(guard, value.valid) }*))
  }
}

/** Finite bursts of signed register operations without heap reads.
  * Registers retain an old quotient origin/orientation and an extended low
  * word. Only finalization selects quotient pointers and allocates carries.
  */
final class WindowRegisters(val circuit: Circuit, nameSeq: Seq[String], val radius: BigInt) {
  val names: Vector[String] = nameSeq.toVector
  val bank: WindowCounters = new WindowCounters(circuit, names, radius)
  val saved: VectorMap[String, WindowCounter] = VectorMap.from(bank.counters.map { case (name, counter) => name -> counter.clone() })
  val width: Int = bank.width + 1
  val old: VectorMap[String, (Expr, Expr, Expr)] = VectorMap.from(saved.map { case (name, counter) =>
    name -> (counter.quotient.zero(), counter.quotient.negative(), counter.quotient.positive())
  })
  var registers: VectorMap[String, Register] = VectorMap.from(saved.map { case (name, counter) =>
    name -> Register(Value.constant(name).recode(names), FALSE, counter.digits)
  })
  def select(which: Value[?]): Register = select(which, registers)
  def select(which: Value[?], registers: collection.Map[String, Register]): Register = {
    val cases = which.domain.collect { case name: String if registers.contains(name) && which.eqTo(name) != FALSE =>
      (which.eqTo(name), registers(name))
    }
    Register(selectValue(cases.map { case (guard, source) => (guard, source.origin) }, names),
      OR(cases.map { case (guard, source) => AND(guard, source.reverse) }*),
      Bits(Vector.tabulate(width)(bit => OR(cases.map { case (guard, source) => AND(guard, source.digits.bits(bit)) }*))),
      cases.map(_._2.radius).maxOption.getOrElse(BigInt(0)))
  }
  def assign(target: String, source: Register, enabled: Expr = TRUE, reverse: Expr = FALSE): Unit = {
    if (enabled != FALSE) {
      val prior = registers(target)
      val digits = Bits.select(reverse, source.digits.negated(), source.digits)
      registers = registers.updated(target, Register(Value.select(enabled, source.origin, prior.origin),
        choose(enabled, choose(reverse, neg(source.reverse), source.reverse), prior.reverse),
        Bits.select(enabled, digits, prior.digits), if (enabled == TRUE) { source.radius } else { source.radius.max(prior.radius) }))
    }
  }
  def reset(target: String, enabled: Expr = TRUE): Unit = {
    val prior = registers(target)
    // Invalid origin denotes exact zero without a quotient.
    val zero = Register(Value.encoded(names, Vector.fill(prior.origin.bits.size)(FALSE), FALSE), FALSE, Bits.constant(0, width))
    assign(target, zero, enabled)
  }
  def add(target: String, amount: BigInt, enabled: Expr = TRUE): Unit = {
    if (enabled != FALSE && amount != 0) {
      val prior = registers(target)
      require(prior.radius + amount.abs <= radius, "register lineage exceeds its proved finite radius")
      registers = registers.updated(target, prior.copy(digits = Bits.select(enabled, prior.digits.add(amount), prior.digits), radius = prior.radius + amount.abs))
    }
  }
  /** ROM fields may have heterogeneous domains; movement entries must be integers. */
  private[pal] def integer(value: Any): BigInt = value match {
    case value: Int => BigInt(value)
    case value: Long => BigInt(value)
    case value: BigInt => value
    case _ => throw new IllegalArgumentException("a fixed integer update is required")
  }
  def addSelected(target: String, amount: Value[?], enabled: Expr = TRUE): Unit = {
    val prior = registers(target)
    val bound = amount.domain.map(value => integer(value).abs).max
    require(prior.radius + bound <= radius, "register lineage exceeds its proved finite radius")
    var digits = prior.digits
    for (delta <- amount.domain if integer(delta) != 0) {
      digits = Bits.select(AND(enabled, amount.eqTo(delta)), prior.digits.add(integer(delta)), digits)
    }
    registers = registers.updated(target, prior.copy(digits = digits, radius = prior.radius + bound))
  }
  def compareZero(register: Register): (Expr, Expr) = {
    var near = neg(register.origin.valid)
    var below = FALSE
    var above = FALSE
    for ((name, (zero, negative, positive)) <- old) {
      val selected = register.origin.eqTo(name)
      near = OR(near, AND(selected, zero))
      below = OR(below, AND(selected, negative))
      above = OR(above, AND(selected, positive))
    }
    (AND(near, register.digits.zero()), OR(choose(register.reverse, above, below), AND(near, register.digits.negative())))
  }
  def commit(): Unit = {
    for ((name, target) <- bank.counters) {
      val register = registers(name)
      for (positive <- Vector(true, false)) {
        val stack = if (positive) { target.quotient.pos } else { target.quotient.negativeStack }
        var top = EMPTY
        val cases = Vector.newBuilder[(Expr, Value[CellTag])]
        for ((origin, source) <- saved; reverse <- Vector(false, true)) {
          val guard = AND(register.origin.eqTo(origin), if (reverse) { register.reverse } else { neg(register.reverse) })
          val selected = if (positive != reverse) { source.quotient.pos } else { source.quotient.negativeStack }
          top = Ref.select(guard, selected.top, top)
          cases += ((guard, selected.tag))
        }
        stack.top = top
        stack.tag = selectValue(cases.result(), stack.tag.domain)
      }
      target.digits = register.digits
      target.radius = register.radius
    }
    bank.commit()
  }
}
