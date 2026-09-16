package pal

import scala.collection.immutable.VectorMap
import Expr.{TRUE, FALSE}
import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction as AND, disjunction as OR, choose, neg}

/** Little-endian finite signed words; arithmetic is modulo their width. */
final case class Bits(bits: Vector[Expr]) {
  private def common(other: Bits): Unit = {
    require(bits.size == other.bits.size, "finite words need a common width")
  }
  def store(circuit: Circuit, key: String): Unit = {
    for ((expression, bit) <- bits.zipWithIndex) {
      circuit.put(s"$key.$bit", Value.select(expression, Value.constant(true), Value.constant(false)), Vector(false, true), false)
    }
  }
  def zero(): Expr = AND(bits.map(neg)*)
  def negative(): Expr = bits.last
  def negated(): Bits = Bits(bits.map(neg)).add(1)
  def plus(other: Bits): Bits = {
    common(other)
    var carry = FALSE
    Bits(bits.zip(other.bits).map { case (a, b) =>
      val unequal = choose(a, neg(b), b)
      val result = choose(carry, neg(unequal), unequal)
      carry = OR(AND(a, b), AND(carry, unequal))
      result
    })
  }
  def equal(other: Bits): Expr = {
    common(other)
    AND(bits.zip(other.bits).map { case (a, b) => choose(a, b, neg(b)) }*)
  }
  def unsignedLess(other: Bits): Expr = {
    common(other)
    bits.zip(other.bits).foldLeft(FALSE) { case (less, (a, b)) =>
      OR(AND(neg(a), b), AND(choose(a, b, neg(b)), less))
    }
  }
  /** A fixed signed addend, modulo the finite bit-vector width. */
  def add(amount: BigInt): Bits = {
    var carry = FALSE
    Bits(bits.zipWithIndex.map { case (bit, index) =>
      if (amount.testBit(index)) {
        val result = choose(carry, bit, neg(bit))
        carry = OR(bit, carry)
        result
      } else {
        val result = choose(carry, neg(bit), bit)
        carry = AND(bit, carry)
        result
      }
    })
  }
}

object Bits {
  def constant(value: BigInt, width: Int): Bits = Bits(Vector.tabulate(width)(bit => if (value.testBit(bit)) { TRUE } else { FALSE }))
  def load(circuit: Circuit, key: String, width: Int): Bits = {
    Bits(Vector.tabulate(width)(bit => circuit.get(PREVIOUS, s"$key.$bit", Vector(false, true), false).eqTo(true)))
  }
  def select(enabled: Expr, yes: Bits, no: Bits): Bits = {
    require(yes.bits.size == no.bits.size, "finite words need a common width")
    Bits(yes.bits.zip(no.bits).map { case (a, b) => choose(enabled, a, b) })
  }
}

/** B*Q+r, with a signed unary quotient and -B/2 <= r < B/2.
  * Only the finite low word changes during a round. One final allocation
  * normalizes the quotient independently of the number of instructions.
  */
final class WindowCounter(val bank: WindowCounters, val name: String, val slot: Int) {
  val circuit: Circuit = bank.circuit
  var quotient: Counter = new Counter(bank.pool, name + ".quotient", Some("cells"))
  private val low = Bits.load(circuit, name + ".low", bank.width)
  var digits: Bits = Bits(low.bits :+ low.negative())
  var radius: BigInt = 0
  var finished: Boolean = false

  private def carry(): (Expr, Expr, Expr) = {
    val high = digits.bits(digits.bits.size - 2)
    val sign = digits.bits.last
    val up = AND(high, neg(sign))
    val down = AND(neg(high), sign)
    (up, down, neg(OR(up, down)))
  }
  private def quotientState(): (Expr, Expr, Expr) = {
    val positive = quotient.positive()
    val negative = quotient.negative()
    val zero = AND(neg(positive), neg(negative))
    val single = Vector(quotient.pos -> positive, quotient.negativeStack -> negative).map { case (stack, has) =>
      val below = stack.pool.pointer(stack.top, stack.tag, "below")
      AND(has, neg(below.present()))
    }
    val (up, down, same) = carry()
    (OR(AND(same, zero), AND(up, single(1)), AND(down, single(0))),
      OR(AND(negative, neg(AND(up, single(1)))), AND(down, zero)),
      OR(AND(positive, neg(AND(down, single(0)))), AND(up, zero)))
  }
  def zero(): Expr = AND(quotientState()._1, Bits(digits.bits.take(bank.width)).zero())
  def negative(): Expr = {
    val (zero, negative, _) = quotientState()
    OR(negative, AND(zero, digits.bits(bank.width - 1)))
  }
  def positive(): Expr = {
    val (zero, _, positive) = quotientState()
    val low = Bits(digits.bits.take(bank.width))
    OR(positive, AND(zero, neg(low.negative()), neg(low.zero())))
  }
  /** Snapshot mutable quotient stacks; immutable expression DAGs stay shared. */
  override def clone(): WindowCounter = {
    val result = new WindowCounter(bank, name, slot)
    result.quotient = ScaffoldWindowStream.cloneCounter(quotient)
    result.digits = digits
    result.radius = radius
    result.finished = finished
    result
  }
  /** Add a finite signed word with a separately supplied static bound. */
  def addWord(delta: Bits, radius: BigInt, enabled: Expr = TRUE): Unit = {
    require(!finished && radius >= 0, "a live counter and a finite nonnegative bound are required")
    if (enabled != FALSE) {
      require(this.radius + radius < bank.base / 2, "counter lineage exceeds the declared finite window")
      digits = Bits.select(enabled, digits.plus(delta), digits)
      this.radius += radius
    }
  }
  def add(amount: BigInt, enabled: Expr = TRUE): Unit = {
    require(!finished, "counter round has already been finalized")
    if (enabled != FALSE && amount != 0) {
      val radius = this.radius + amount.abs
      require(radius < bank.base / 2, "counter lineage exceeds the declared finite window")
      digits = Bits.select(enabled, digits.add(amount), digits)
      this.radius = radius
    }
  }
  def inc(enabled: Expr = TRUE): Unit = add(1, enabled)
  def dec(enabled: Expr = TRUE): Unit = add(-1, enabled)
  def copyFrom(other: WindowCounter, enabled: Expr = TRUE, negateValue: Boolean = false): Unit = {
    require((bank eq other.bank) && !finished, "copy requires live counters in the same window bank")
    if (enabled != FALSE) {
      val sources = if (negateValue) { Vector(other.quotient.negativeStack, other.quotient.pos) }
                    else { Vector(other.quotient.pos, other.quotient.negativeStack) }
      val snapshots = sources.map(stack => (stack.top, stack.tag))
      for ((destination, (top, tag)) <- Vector(quotient.pos, quotient.negativeStack).zip(snapshots)) {
        destination.top = Ref.select(enabled, top, destination.top)
        destination.tag = Value.select(enabled, tag, destination.tag)
      }
      digits = Bits.select(enabled, if (negateValue) { other.digits.negated() } else { other.digits }, digits)
      radius = if (enabled == TRUE) { other.radius } else { radius.max(other.radius) }
    }
  }
  def reset(enabled: Expr = TRUE): Unit = {
    require(!finished, "counter round has already been finalized")
    quotient.reset(enabled)
    digits = Bits.select(enabled, Bits.constant(0, bank.width + 1), digits)
    if (enabled == TRUE) { radius = 0 }
  }
  def commit(): Unit = {
    require(!finished, "counter round has already been finalized")
    val (up, down, _) = carry()
    quotient.inc(up, Some(slot))
    quotient.dec(down, Some(slot))
    quotient.commit()
    Bits(digits.bits.take(bank.width)).store(circuit, name + ".low")
    finished = true
  }
}

final class WindowCounters(val circuit: Circuit, nameSeq: Seq[String], radius: BigInt) {
  val names: Vector[String] = nameSeq.toVector
  require(names.nonEmpty && names.distinct.size == names.size, "distinct finite counter names are required")
  require(radius >= 0, "a nonnegative construction-time radius is required")
  val width: Int = math.max(1, radius.bitLength + 1)
  val base: BigInt = BigInt(1) << width
  val pool: StackPool = new StackPool(circuit, Vector("cells" -> names.size))
  val counters: VectorMap[String, WindowCounter] = VectorMap.from(names.zipWithIndex.map { case (name, slot) => name -> new WindowCounter(this, name, slot) })
  def commit(): Unit = { counters.values.foreach(_.commit()) }
}

object ScaffoldWindowCounter {
  /** Each actual character performs conditional arithmetic and copies. */
  def fixture(radius: BigInt = 31): (Circuit, WindowCounters, Scaffold) = {
    val circuit = new Circuit("abcdefgh")
    val bank = new WindowCounters(circuit, Vector("x", "y"), radius)
    val x = bank.counters("x")
    val y = bank.counters("y")
    val char = circuit.input()
    x.add(7, char.eqTo('a'))
    x.add(-5, char.eqTo('b'))
    y.copyFrom(x, char.eqTo('c'))
    x.copyFrom(y, char.eqTo('d'))
    y.add(-3, char.eqTo('e'))
    x.reset(char.eqTo('f'))
    x.copyFrom(x, char.eqTo('g'), negateValue = true)
    y.copyFrom(x, char.eqTo('h'), negateValue = true)
    for (counter <- Vector(x, y); (name, condition) <- Vector("zero" -> counter.zero(), "negative" -> counter.negative(), "positive" -> counter.positive())) {
      circuit.put(counter.name + "." + name, Value.select(condition, Value.constant(true), Value.constant(false)), Vector(false, true), name == "zero")
    }
    val answer = x.zero()
    bank.commit()
    (circuit, bank, circuit.machine(answer, initialAccepting = true))
  }
}
