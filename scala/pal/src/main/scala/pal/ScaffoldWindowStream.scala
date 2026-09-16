package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable
import Expr.{TRUE, FALSE, pointer, edge}
import Ref.{PREVIOUS, NEW, EMPTY}
import ScaffoldCircuit.{conjunction as AND, disjunction as OR, choose, choosePointer, neg}

object ScaffoldWindowStream {
  private[pal] def cloneStack(source: Stack): Stack = {
    val result = new Stack(source.pool, source.name, Some(source.allocationName))
    result.top = source.top
    result.tag = source.tag
    result
  }
  def cloneCounter(source: Counter): Counter = {
    val result = new Counter(Map("pos" -> source.pos.pool, "neg" -> source.negativeStack.pool), source.name, Some(source.pos.allocationName))
    result.positiveStack = cloneStack(source.pos)
    result.negativeStack = cloneStack(source.negativeStack)
    result
  }
  def cloneQueue(source: Queue): Queue = {
    val pools = source.stacks.view.mapValues(_.pool).toMap
    val counterPools = Map("m" -> Map("pos" -> source.m.pos.pool, "neg" -> source.m.negativeStack.pool),
      "c" -> Map("pos" -> source.c.pos.pool, "neg" -> source.c.negativeStack.pool))
    val result = new Queue(pools, counterPools, source.name, source.sharedSlots)
    // Each new queue owns fresh stack objects, but shares physical pools.
    for ((name, stack) <- source.stacks) {
      result.stacks(name).top = stack.top
      result.stacks(name).tag = stack.tag
    }
    for ((target, prior) <- Vector(result.m -> source.m, result.c -> source.c)) {
      target.positiveStack = cloneStack(prior.pos)
      target.negativeStack = cloneStack(prior.negativeStack)
    }
    result.phase = source.phase
    result
  }
  def fixture(quantum: Int = 3): (Circuit, WindowStream, VectorMap[String, String], Scaffold) = {
    val circuit = new Circuit("abcdefgh")
    val stream = new WindowStream(circuit, Vector("x", "y"), 2 * quantum + 2)
    val x = stream.heads("x")
    val y = stream.heads("y")
    val char = circuit.input()
    for (_ <- 0 until quantum) {
      x.move(1, AND(char.eqTo('a'), x.canMove(1)))
      x.move(-1, AND(char.eqTo('b'), x.canMove(-1)))
    }
    y.copyFrom(x, char.eqTo('c'))
    x.copyFrom(y, char.eqTo('d'))
    y.move(1, AND(char.eqTo('e'), y.canMove(1)))
    y.move(-1, AND(char.eqTo('f'), y.canMove(-1)))
    val observations = VectorMap.from(Vector(x, y).map { head =>
      val value = head.read(head.available())
      val key = head.name + ".read"
      circuit.put(key, value, circuit.alphabet :+ None, None)
      head.name -> key
    })
    val answer = x.read(x.available()).eqTo('a')
    stream.commit()
    (circuit, stream, observations, circuit.machine(answer))
  }
}

/** A block zipper snapshot; all clones share storage but own evolving roots. */
final class BlockState(val bank: WindowStream, val name: String) {
  val circuit: Circuit = bank.circuit
  val focusKey: String = name + ".block_end"
  val liveKey: String = name + ".live"
  var focus: Ref = circuit.getRef(PREVIOUS, focusKey)
  var live: Expr = circuit.get(PREVIOUS, liveKey, Vector(false, true), true).eqTo(true)
  var left: Stack = new Stack(bank.cells, name + ".left")
  var right: Stack = new Stack(bank.cells, name + ".right")
  var queue: Queue = new Queue(bank.queueCells, bank.counterCells, name + ".incoming")
  override def clone(): BlockState = {
    val result = new BlockState(bank, name)
    result.focus = focus
    result.live = live
    result.left = ScaffoldWindowStream.cloneStack(left)
    result.right = ScaffoldWindowStream.cloneStack(right)
    result.queue = ScaffoldWindowStream.cloneQueue(queue)
    result
  }
  def completeBlock(completed: Expr): Unit = {
    queue.push(NEW, AND(completed, neg(live)))
    queue.work(completed)
    focus = Ref.select(AND(completed, live), NEW, focus)
    live = AND(live, neg(completed))
  }
  def moveLeft(enabled: Expr): Unit = {
    // A live block is not pushed: later completion queues its actual endpoint.
    right.push(focus, enabled = AND(enabled, neg(live)))
    val (prior, _) = left.pop(enabled)
    focus = Ref.select(enabled, prior, focus)
    live = AND(live, neg(enabled))
  }
  def moveRight(enabled: Expr): Unit = {
    left.push(focus, enabled = enabled)
    val stacked = neg(right.empty())
    val queued = neg(queue.empty())
    val fromQueue = AND(enabled, neg(stacked), queued)
    val (a, _) = right.pop(AND(enabled, stacked))
    val b = queue.pop(fromQueue)
    queue.work(fromQueue)
    focus = Ref.select(enabled, Ref.select(stacked, a, b), focus)
    live = choose(enabled, AND(neg(stacked), neg(queued)), live)
  }
  def copyFrom(other: BlockState, enabled: Expr): Unit = {
    focus = Ref.select(enabled, other.focus, focus)
    live = choose(enabled, other.live, live)
    left.copyFrom(other.left, enabled)
    right.copyFrom(other.right, enabled)
    queue.copyFrom(other.queue, enabled)
  }
  def commit(): Unit = {
    circuit.putRef(focusKey, focus)
    circuit.put(liveKey, Value.select(live, Value.constant(true), Value.constant(false)))
    left.commit()
    right.commit()
    queue.commit()
  }
}

final class WindowHead private[pal] (val bank: WindowStream, val name: String,
                                    var origin: Value[String], var offset: Bits, var radius: BigInt) {
  def this(bank: WindowStream, name: String) = {
    this(bank, name, Value.constant(name).recode(bank.names),
      Bits(Bits.load(bank.circuit, name + ".offset", bank.width).bits ++ Vector(FALSE, FALSE)), BigInt(0))
  }
  def variants(): Vector[(BlockState, Expr, Expr)] = variants(offset)
  def variants(offset: Bits): Vector[(BlockState, Expr, Expr)] = {
    val high = offset.bits(offset.bits.size - 2)
    val sign = offset.bits.last
    val directions = Vector(-1 -> AND(high, sign), 0 -> AND(neg(high), neg(sign)), 1 -> AND(high, neg(sign)))
    bank.names.flatMap { name =>
      val origin = this.origin.eqTo(name)
      if (origin == FALSE) { Vector.empty } else {
        directions.map { case (direction, guard) =>
          val (state, valid) = bank.neighbors(name)(direction)
          (state, AND(origin, guard), valid)
        }
      }
    }
  }
  def describe(): (Ref, Expr, Expr) = describe(offset)
  def describe(offset: Bits): (Ref, Expr, Expr) = {
    var endpoint = EMPTY
    var live = FALSE
    var valid = FALSE
    for ((state, guard, permitted) <- variants(offset)) {
      endpoint = Ref.select(guard, state.focus, endpoint)
      live = OR(live, AND(guard, state.live))
      valid = OR(valid, AND(guard, permitted))
    }
    (endpoint, live, valid)
  }
  def locationFlags(): (Expr, Expr) = locationFlags(offset)
  /** Availability does not construct discarded endpoint-selection DAGs. */
  def locationFlags(offset: Bits): (Expr, Expr) = {
    var live = FALSE
    var valid = FALSE
    for ((state, guard, permitted) <- variants(offset)) {
      live = OR(live, AND(guard, state.live))
      valid = OR(valid, AND(guard, permitted))
    }
    (live, valid)
  }
  def available(): Expr = {
    val (live, valid) = locationFlags()
    val low = Bits(offset.bits.take(bank.width))
    AND(valid, OR(neg(live), low.unsignedLess(bank.phase)))
  }
  def canMove(amount: BigInt): Expr = {
    val candidate = offset.add(amount)
    val (live, valid) = locationFlags(candidate)
    val low = Bits(candidate.bits.take(bank.width))
    AND(valid, OR(neg(live), low.unsignedLess(bank.phase), low.equal(bank.phase)))
  }
  def move(amount: BigInt, enabled: Expr = TRUE): Unit = {
    if (enabled != FALSE && amount != 0) {
      require(radius + amount.abs < bank.base, "head lineage exceeds the declared finite window")
      bank.circuit.require(canMove(amount), enabled)
      offset = Bits.select(enabled, offset.add(amount), offset)
      radius += amount.abs
    }
  }
  def copyFrom(other: WindowHead, enabled: Expr = TRUE): Unit = {
    require(other.bank eq bank, "head copies require a common stream")
    origin = Value.select(enabled, other.origin, origin)
    offset = Bits.select(enabled, other.offset, offset)
    radius = if (enabled == TRUE) { other.radius } else { radius.max(other.radius) }
  }
  private def integer(value: Any): BigInt = value match {
    case value: Int => BigInt(value)
    case value: Long => BigInt(value)
    case value: BigInt => value
    case _ => throw new IllegalArgumentException("head motion must have a fixed finite distance")
  }
  def moveSelected(amount: Value[?], enabled: Expr = TRUE): Unit = {
    val bound = amount.domain.map(value => integer(value).abs).max
    require(radius + bound < bank.base, "selected head motion exceeds the prepared finite window")
    val before = offset
    var after = offset
    for (delta <- amount.domain if integer(delta) != 0) {
      val guard = AND(enabled, amount.eqTo(delta))
      bank.circuit.require(canMove(integer(delta)), guard)
      after = Bits.select(guard, before.add(integer(delta)), after)
    }
    offset = after
    radius += bound
  }
  def read(enabled: Expr = TRUE): Value[Any] = {
    val c = bank.circuit
    val available = this.available()
    c.require(available, enabled)
    val (end, live, _) = describe()
    val low = Bits(offset.bits.take(bank.width))
    val fullDistance = Bits(low.bits.map(neg))
    val liveDistance = bank.phase.plus(low.negated()).add(-1)
    val distance = Bits.select(live, liveDistance, fullDistance)
    var endpoint = Ref.select(live, NEW, end)
    for ((enabledBit, bit) <- distance.bits.zipWithIndex) {
      endpoint = Ref.select(enabledBit, bank.hop(endpoint, BigInt(1) << bit), endpoint)
    }
    val value = c.get(endpoint, bank.inputKey, c.alphabet, c.alphabet.head)
    Value.select(available, value, Value.constant(None))
  }
  def readRelative(amount: BigInt, enabled: Expr = TRUE): Value[Any] = {
    require(radius + amount.abs < bank.base, "relative read exceeds the prepared head window")
    new WindowHead(bank, name, origin, offset.add(amount), radius).read(enabled)
  }
  def commit(): Unit = {
    val target = bank.states(name)
    for ((source, guard, valid) <- variants()) {
      bank.circuit.require(valid, guard)
      target.copyFrom(source, guard)
    }
    Bits(offset.bits.take(bank.width)).store(bank.circuit, name + ".offset")
    target.commit()
  }
}

/** Bounded motion over blocks of original, unexpanded input.
  * Old block and neighbor zippers are prepared once. Only selected final
  * states are saved; intermediate motion/copies allocate no cells. Every
  * input character belongs to this stream in consecutive transitions.
  */
final class WindowStream(val circuit: Circuit, nameSeq: Seq[String], radius: BigInt, val prefix: String = "stream") {
  require(radius >= 0, "a nonnegative finite movement radius is required")
  val names: Vector[String] = nameSeq.toVector
  require(names.nonEmpty && names.distinct.size == names.size, "distinct finite head names required")
  val width: Int = math.max(1, radius.bitLength)
  val base: BigInt = BigInt(1) << width
  val phaseKey: String = prefix + ".phase"
  val inputKey: String = prefix + ".input"
  private val oldPhase = Bits.load(circuit, phaseKey, width)
  private val completed = AND(oldPhase.bits*)
  val phase: Bits = oldPhase.add(1)
  circuit.put(inputKey, circuit.input(), circuit.alphabet, circuit.alphabet.head)
  val cells: StackPool = new StackPool(circuit, for (name <- names; side <- Vector(".left", ".right")) yield (name + side) -> 1)
  private def pool(layout: (String, Int)*): StackPool = {
    new StackPool(circuit, for (name <- names; (role, count) <- layout) yield s"$name.incoming.$role" -> count)
  }
  private val front = pool("Br" -> 12)
  private val rear = pool("B" -> 1, "B2" -> 1)
  private val reverse = pool("Fr" -> 6)
  val queueCells: Map[String, StackPool] = Map("F" -> front, "WF" -> front, "Br" -> front, "B" -> rear, "WB" -> rear, "B2" -> rear, "Fr" -> reverse)
  val counterCells: Map[String, Map[String, StackPool]] = Map(
    "m" -> Map("pos" -> pool("m.pos" -> 6), "neg" -> pool("m.neg" -> 8)),
    "c" -> Map("pos" -> pool("c.pos" -> 12), "neg" -> pool("c.neg" -> 2)))
  val states: VectorMap[String, BlockState] = VectorMap.from(names.map(name => name -> new BlockState(this, name)))
  private val jumpFields = mutable.LinkedHashMap.empty[BigInt, String]
  def jumps: VectorMap[BigInt, String] = VectorMap.from(jumpFields)
  val neighbors: VectorMap[String, VectorMap[Int, (BlockState, Expr)]] = VectorMap.from(states.map { case (name, state) =>
    state.completeBlock(completed)
    val center = state.clone()
    val before = center.clone()
    val after = center.clone()
    val canLeft = neg(center.left.empty())
    val canRight = neg(center.live)
    before.moveLeft(canLeft)
    after.moveRight(canRight)
    name -> VectorMap(-1 -> (before, canLeft), 0 -> (center, TRUE), 1 -> (after, canRight))
  })
  val heads: VectorMap[String, WindowHead] = VectorMap.from(names.map(name => name -> new WindowHead(this, name)))
  /** An original-input predecessor by a fixed distance, in O(log B) fields. */
  def jump(distance: BigInt): String = {
    require(distance >= 1, "positive original-input hop required")
    if (!jumpFields.contains(distance)) {
      val name = s"$prefix.back$distance"
      jumpFields(distance) = name
      val path = if (distance == 1) { Vector.empty } else if (distance.testBit(0)) {
        Vector.fill(2)(jump(distance / 2))
      } else {
        val half = distance / 2
        Vector(jump(half)) ++ (if (half > 1) { Vector(jump(half - 1)) } else { Vector.empty })
      }
      circuit.pointers(name) = pointer(path)
    }
    jumpFields(distance)
  }
  def hop(target: Ref, distance: BigInt): Ref = {
    val fromNew = if (distance == 1) { pointer(Vector.empty) } else { pointer(Vector(jump(distance - 1))) }
    Ref(FALSE, choosePointer(target.isNew, fromNew, edge(target.prior, jump(distance))))
  }
  def selectHead(which: Value[?]): WindowHead = {
    val cases = heads.toVector.map { case (name, head) => (which.eqTo(name), head) }.filter(_._1 != FALSE)
    val origin = Value.encoded(names, Vector.tabulate(ScaffoldCircuit.bitWidth(names.size))(bit =>
      OR(cases.map { case (guard, head) => AND(guard, head.origin.bits(bit)) }*)), OR(cases.map(_._1)*))
    val offset = Bits(Vector.tabulate(width + 2)(bit => OR(cases.map { case (guard, head) => AND(guard, head.offset.bits(bit)) }*)))
    new WindowHead(this, "", origin, offset, cases.map(_._2.radius).maxOption.getOrElse(BigInt(0)))
  }
  def commit(): Unit = {
    heads.values.foreach(_.commit())
    phase.store(circuit, phaseKey)
  }
}
