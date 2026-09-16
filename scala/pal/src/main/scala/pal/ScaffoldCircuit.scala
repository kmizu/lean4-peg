package pal

import scala.collection.mutable

import Expr.{TRUE, FALSE, SELF, NULL}

/** Predicated finite-value and local-pointer equations for scaffold lowering.
  *
  * This is a construction-time API. Its finite expression maps are consumed at
  * construction; the emitted machine has only Boolean labels, pointer fields,
  * and ordinary PEG rules. `Ref` distinguishes a cell allocated during this
  * tick from an old cell so reading a new cell uses its construction-time
  * fields, never recursive queries of the new scaffold node. No pointer
  * identity operation is supplied.
  *
  * Port of `scaffold_circuit.py`. The Boolean simplifiers (`neg`, `conjunction`,
  * `disjunction`, `choose`, `choosePointer`) live here; `Value`, `Ref` and
  * `Circuit` are top-level classes of package `pal`.
  */
object ScaffoldCircuit {

  def neg(a: Expr): Expr = {
    a match {
      case Expr.Const(true) => FALSE
      case Expr.Const(false) => TRUE
      case Expr.Not(inner) => inner
      case _ => Expr.intern(Expr.Not(a))
    }
  }

  /** The distinct non-`unit` operands in first-occurrence order plus their set, or `None` when `zero` short-circuits. */
  private def operands(args: Seq[Expr], zero: Expr, unit: Expr): Option[(Vector[Expr], mutable.HashSet[Expr])] = {
    val result = Vector.newBuilder[Expr]
    val seen = mutable.HashSet.empty[Expr]
    var shortCircuit = false
    val remaining = args.iterator
    while (!shortCircuit && remaining.hasNext) {
      val arg = remaining.next()
      if (arg == zero) {
        shortCircuit = true
      } else if (arg != unit && seen.add(arg)) {
        result += arg
      }
    }
    if (shortCircuit) { None } else { Some((result.result(), seen)) }
  }

  /** Shared body of `conjunction` (`isOr = false`) and `disjunction` (`isOr = true`). */
  private def connective(args: Seq[Expr], isOr: Boolean): Expr = {
    val zero = if (isOr) { TRUE } else { FALSE }
    val unit = if (isOr) { FALSE } else { TRUE }
    operands(args, zero, unit) match {
      case None => zero
      case Some((result, seen)) =>
        if (result.exists(x => seen.contains(neg(x)))) {
          zero
        } else if (result.isEmpty) {
          unit
        } else if (result.length == 1) {
          result.head
        } else if (isOr) {
          Expr.intern(Expr.Or(result))
        } else {
          Expr.intern(Expr.And(result))
        }
    }
  }

  def conjunction(args: Expr*): Expr = connective(args, isOr = false)

  def disjunction(args: Expr*): Expr = connective(args, isOr = true)

  def choose(guard: Expr, yes: Expr, no: Expr): Expr = {
    if (guard == TRUE || yes == no) {
      yes
    } else if (guard == FALSE) {
      no
    } else if (yes == TRUE && no == FALSE) {
      guard
    } else if (yes == FALSE && no == TRUE) {
      neg(guard)
    } else {
      disjunction(conjunction(guard, yes), conjunction(neg(guard), no))
    }
  }

  def choosePointer(guard: Expr, yes: Expr, no: Expr): Expr = {
    if (guard == TRUE || yes == no) {
      yes
    } else if (guard == FALSE) {
      no
    } else {
      Expr.select(guard, yes, no)
    }
  }

  /** Python `max(0, (size - 1).bit_length())`: bits needed to index `size` variants.
    *
    * Note `(-1).bit_length() == 1`, so an empty domain still gets one (false) bit.
    */
  private[pal] def bitWidth(size: Int): Int = {
    if (size <= 0) { 1 } else { 32 - Integer.numberOfLeadingZeros(size - 1) }
  }
}

/** A finite tagged value with a shared binary encoding and a validity bit.
  *
  * Domain elements are arbitrary (Python used characters, Booleans, integers,
  * strings, `None` and tag tuples); Scala `None` plays the role of Python `None`.
  */
final class Value[+A] private (val domain: Vector[A], val bits: Vector[Expr], val valid: Expr) {
  import ScaffoldCircuit.*

  /** Position of each domain element (Python `domain.index`, but O(1) after the first use). */
  private lazy val positions: Map[Any, Int] = domain.zipWithIndex.toMap[Any, Int]

  /** `(value, guard)` pairs in domain order (Python `cases` dict). */
  def cases: Vector[(A, Expr)] = domain.map(value => value -> eqTo(value))

  /** Guard for `this == value` (Python `Value.eq`; renamed because `AnyRef.eq` is final). */
  def eqTo(value: Any): Expr = {
    positions.get(value) match {
      case None => FALSE
      case Some(index) =>
        val tests = bits.zipWithIndex.map { case (bit, i) => if ((index & (1 << i)) != 0) { bit } else { neg(bit) } }
        conjunction((valid +: tests)*)
    }
  }

  def recode[B >: A](target: Seq[B]): Value[B] = {
    val domain = target.toVector
    if (domain == this.domain) {
      this
    } else {
      val available = domain.toSet
      if (!this.domain.forall(value => available.contains(value))) {
        throw new IllegalArgumentException("cannot discard variants of a finite value")
      }
      val bits = (0 until bitWidth(domain.length)).map { bit =>
        disjunction(domain.zipWithIndex.collect { case (value, index) if (index & (1 << bit)) != 0 => eqTo(value) }*)
      }
      Value.encoded(domain, bits, valid)
    }
  }

  def map[B](function: A => B): Value[B] = {
    // A LinkedHashMap keeps the position of the first occurrence when a key is
    // merged again, exactly like the Python dict the original accumulated into.
    val result = mutable.LinkedHashMap.empty[B, Expr]
    for ((value, guard) <- cases) {
      val mapped = function(value)
      result(mapped) = disjunction(result.getOrElse(mapped, FALSE), guard)
    }
    Value(result)
  }

  /** Rotate a power-of-two domain by one with a binary carry circuit. */
  def cycle(direction: Int = 1): Value[A] = {
    val size = domain.length
    if ((direction != -1 && direction != 1) || size == 0 || (size & (size - 1)) != 0) {
      throw new IllegalArgumentException("unit cyclic movement requires a power-of-two domain")
    }
    var carry = TRUE
    val rotated = Vector.newBuilder[Expr]
    for (bit <- bits) {
      rotated += choose(carry, neg(bit), bit)
      carry = conjunction(carry, if (direction == 1) { bit } else { neg(bit) })
    }
    Value.encoded(domain, rotated.result(), valid)
  }

  def equal(other: Value[?]): Expr = {
    if (domain == other.domain) {
      val agree = bits.zip(other.bits).map { case (a, b) => choose(a, b, neg(b)) }
      conjunction((Vector(valid, other.valid) ++ agree)*)
    } else {
      disjunction(cases.map { case (value, guard) => conjunction(guard, other.eqTo(value)) }*)
    }
  }

  override def toString: String = s"Value(domain=$domain, bits=$bits, valid=$valid)"
}

object Value {
  import ScaffoldCircuit.*

  /** Build from `(value, guard)` cases in order; `FALSE` guards are dropped. */
  def apply[A](cases: Iterable[(A, Expr)]): Value[A] = {
    val merged = mutable.LinkedHashMap.empty[A, Expr]
    for ((value, guard) <- cases) { merged(value) = guard }
    val live = merged.toVector.filter { case (_, guard) => guard != FALSE }
    val domain = live.map(_._1)
    val valid = disjunction(live.map(_._2)*)
    val bits = (0 until bitWidth(live.length)).map { bit =>
      disjunction(live.zipWithIndex.collect { case ((_, guard), index) if (index & (1 << bit)) != 0 => guard }*)
    }
    encoded(domain, bits, valid)
  }

  def encoded[A](domain: Seq[A], bits: Iterable[Expr], valid: Expr = TRUE): Value[A] = {
    new Value(domain.toVector, bits.toVector, valid)
  }

  def constant[A](value: A): Value[A] = apply(Vector(value -> TRUE))

  def select[A](guard: Expr, yes: Value[A], no: Value[A]): Value[A] = {
    if (guard == TRUE) {
      yes
    } else if (guard == FALSE) {
      no
    } else {
      val domain = (no.domain ++ yes.domain).distinct
      val y = yes.recode(domain)
      val n = no.recode(domain)
      encoded(domain, y.bits.zip(n.bits).map { case (a, b) => choose(guard, a, b) }, choose(guard, y.valid, n.valid))
    }
  }
}

/** A cell reference: `isNew` when allocated this tick, else the old pointer `prior`. */
final case class Ref(isNew: Expr = FALSE, prior: Expr = NULL) {
  import ScaffoldCircuit.*

  def present(): Expr = disjunction(isNew, if (prior != NULL) { Expr.present(prior) } else { FALSE })

  def expression(): Expr = choosePointer(isNew, SELF, prior)
}

object Ref {
  import ScaffoldCircuit.*

  def select(guard: Expr, yes: Ref, no: Ref): Ref = {
    Ref(choose(guard, yes.isNew, no.isNew), choosePointer(guard, yes.prior, no.prior))
  }

  val NEW: Ref = Ref(TRUE, NULL)
  val EMPTY: Ref = Ref()
  val PREVIOUS: Ref = Ref(FALSE, Expr.pointer(Nil))
}

/** Accumulates finite scalar and pointer equations, then emits a `Scaffold`. */
final class Circuit(val alphabet: String = "ab", val checkInvariants: Boolean = true) {
  import ScaffoldCircuit.*

  /** Declared scalar domains: key -> (domain, initial value). */
  val domains: mutable.LinkedHashMap[String, (Vector[Any], Any)] = mutable.LinkedHashMap.empty
  val initial: mutable.LinkedHashMap[String, Boolean] = mutable.LinkedHashMap.empty
  val labels: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.empty
  val pointers: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.empty
  val currentValues: mutable.LinkedHashMap[String, Value[Any]] = mutable.LinkedHashMap.empty
  val currentRefs: mutable.LinkedHashMap[String, Ref] = mutable.LinkedHashMap.empty
  val labelIds: mutable.LinkedHashMap[(String, Int), String] = mutable.LinkedHashMap.empty

  /** Accumulated invariant violations (Python's lazily created `fault` attribute). */
  var fault: Option[Expr] = None

  /** Cell pools registered by `StackPool` (Python's dynamically attached `_pools`). */
  val pools: mutable.ArrayBuffer[StackPool] = mutable.ArrayBuffer.empty

  private def label(key: String, bit: Int): String = labelIds.getOrElseUpdate((key, bit), s"v${labelIds.size}")

  def scalar[A](key: String, domain: Seq[A], initial: A): Unit = {
    val values: Vector[Any] = domain.toVector
    if (!values.contains(initial) || values.distinct.length != values.length) {
      throw new IllegalArgumentException("finite scalar domain must be distinct and include its initial value")
    }
    domains.get(key) match {
      case Some(declared) =>
        if (declared != ((values, initial))) { throw new IllegalArgumentException(s"inconsistent scalar declaration: $key") }
      case None =>
        domains(key) = (values, initial)
        val index = values.indexOf(initial)
        for (bit <- 0 until bitWidth(values.length)) {
          val name = label(key, bit)
          this.initial(name) = (index & (1 << bit)) != 0
          labels(name) = FALSE
        }
    }
  }

  def get[A](target: Ref, key: String, domain: Seq[A], initial: A): Value[A] = {
    scalar(key, domain, initial)
    val current = currentValues.getOrElse(key, Value.constant(initial)).recode(domain)
    val bits = current.bits.zipWithIndex.map { case (bit, i) => choose(target.isNew, bit, Expr.read(target.prior, label(key, i))) }
    Value.encoded(domain, bits, target.present())
  }

  def put(key: String, value: Value[Any]): Unit = {
    if (!domains.contains(key)) { throw new IllegalArgumentException(s"undeclared scalar: $key") }
    store(key, value)
  }

  def put[A](key: String, value: Value[A], domain: Seq[A], initial: A): Unit = {
    if (!domains.contains(key)) { scalar(key, domain, initial) }
    store(key, value)
  }

  private def store(key: String, value: Value[Any]): Unit = {
    val recoded = value.recode(domains(key)._1)
    currentValues(key) = recoded
    for ((expr, bit) <- recoded.bits.zipWithIndex) { labels(label(key, bit)) = expr }
  }

  def getRef(target: Ref, key: String): Ref = {
    pointers.getOrElseUpdate(key, NULL)
    val local = currentRefs.getOrElse(key, Ref.EMPTY)
    Ref(choose(target.isNew, local.isNew, FALSE), choosePointer(target.isNew, local.prior, Expr.edge(target.prior, key)))
  }

  def putRef(key: String, value: Ref): Unit = {
    currentRefs(key) = value
    pointers(key) = value.expression()
  }

  def input(): Value[Char] = Value(alphabet.toVector.map(char => char -> Expr.symbol(char)))

  def require(condition: Expr, enabled: Expr = TRUE): Unit = {
    if (checkInvariants) {
      val current = fault.getOrElse(get(Ref.PREVIOUS, "circuit.fault", Vector(false, true), false).eqTo(true))
      fault = Some(disjunction(current, conjunction(enabled, neg(condition))))
    }
  }

  def machine(accepting: Expr, initialAccepting: Boolean = false): Scaffold = {
    val accept = fault match {
      case Some(current) =>
        put("circuit.fault", Value.select(current, Value.constant(true), Value.constant(false)))
        conjunction(accepting, neg(current))
      case None => accepting
    }
    // Unwritten cell fields have their declared defaults; this matters when a
    // later node aliases a slot never allocated in a particular branch.
    for ((key, (domain, initial)) <- domains if !currentValues.contains(key)) {
      val index = domain.indexOf(initial)
      for (bit <- 0 until bitWidth(domain.length)) {
        labels(label(key, bit)) = if ((index & (1 << bit)) != 0) { TRUE } else { FALSE }
      }
    }
    val name = "accept"
    if (initial.contains(name)) { throw new IllegalArgumentException("reserved acceptance label") }
    initial(name) = initialAccepting
    labels(name) = accept
    new Scaffold(initial, labels, pointers, name, alphabet)
  }
}
