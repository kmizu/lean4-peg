package pal

import Expr.{FALSE, TRUE}
import Ref.{EMPTY, NEW, PREVIOUS}
import ScaffoldCircuit.{conjunction as AND, disjunction as OR, neg}

/** Many flag pushes per round, stored in one immutable packet per input node.
  *
  * Port of `scaffold_flag_packets.py`.  Packet slots are finite construction
  * indices; each slot stores its bit and the preceding valid slot.
  */
final class FlagPackets(val circuit: Circuit, val capacity: Int, val prefix: String = "packets") {
  if (capacity < 1) {
    throw new IllegalArgumentException("a positive finite packet capacity is required")
  }

  val indices: Vector[Int] = -1 +: (0 until capacity).toVector
  val width: Int = BigInt(capacity).bitLength
  val backKey: String = prefix + ".previous"
  val indexKey: String = prefix + ".previous_index"
  var writerCreated: Boolean = false

  def index(slot: Int): Value[Int] = {
    if (slot < -1 || slot >= capacity) {
      throw new IllegalArgumentException("packet slot outside the finite layout")
    }
    Value.encoded(indices, Bits.constant(BigInt(slot + 1), width).bits)
  }

  def equal(index: Value[Int], slot: Int): Expr = {
    Bits(index.bits).equal(Bits.constant(BigInt(slot + 1), width))
  }

  def fields(slot: Int): (String, String) = {
    (s"$prefix.$slot.bit", s"$prefix.$slot.previous_index")
  }

  def read(root: Ref, index: Value[Int]): (Expr, Value[Int]) = {
    var bit = FALSE
    var previous = Vector.fill(width)(FALSE)
    for (slot <- 0 until capacity) {
      val enabled = equal(index, slot)
      if (enabled != FALSE) {
        val (bitKey, previousKey) = fields(slot)
        val value = circuit.get(root, bitKey, Vector(false, true), false).eqTo(true)
        val saved = circuit.get(root, previousKey, indices, -1)
        bit = OR(bit, AND(enabled, value))
        previous = previous.zip(saved.bits).map { case (result, field) => OR(result, AND(enabled, field)) }
      }
    }
    (bit, Value.encoded(indices, previous))
  }
}

final class FlagStack(val pool: FlagPackets, val name: String) {
  val circuit: Circuit = pool.circuit
  val rootKey: String = name + ".root"
  val indexKey: String = name + ".index"
  var root: Ref = circuit.getRef(PREVIOUS, rootKey)
  var index: Value[Int] = circuit.get(PREVIOUS, indexKey, pool.indices, -1)

  def empty(): Expr = neg(root.present())

  def clear(enabled: Expr = TRUE): Unit = {
    root = Ref.select(enabled, EMPTY, root)
    index = Value.select(enabled, pool.index(-1), index)
  }

  def copyFrom(other: FlagStack, enabled: Expr = TRUE): Unit = {
    if (!(other.pool eq pool)) {
      throw new IllegalArgumentException("flag stack copies require a common packet pool")
    }
    root = Ref.select(enabled, other.root, root)
    index = Value.select(enabled, other.index, index)
  }

  def pop(enabled: Expr = TRUE): Expr = {
    circuit.require(neg(empty()), enabled)
    val (bit, previous) = pool.read(root, index)
    val boundary = pool.equal(previous, -1)
    val backRoot = circuit.getRef(root, pool.backKey)
    val backIndex = circuit.get(root, pool.indexKey, pool.indices, -1)
    root = Ref.select(AND(enabled, boundary), backRoot, root)
    index = Value.select(enabled, Value.select(boundary, backIndex, previous), index)
    bit
  }

  /** Python `finalize()`. */
  def commit(): Unit = {
    circuit.putRef(rootKey, root)
    circuit.put(indexKey, index)
  }
}

final class PacketWriter(val stack: FlagStack) {
  val pool: FlagPackets = stack.pool
  val circuit: Circuit = stack.circuit
  if (pool.writerCreated) {
    throw new IllegalArgumentException("one writer per packet pool and input node is required")
  }
  pool.writerCreated = true
  var started: Expr = FALSE
  var nextSlot: Int = 0

  circuit.putRef(pool.backKey, stack.root)
  circuit.put(pool.indexKey, stack.index, pool.indices, -1)

  def push(bit: Expr, enabled: Expr = TRUE): Unit = {
    if (nextSlot >= pool.capacity) {
      throw new IllegalArgumentException("finite flag packet capacity exhausted")
    }
    val slot = nextSlot
    nextSlot += 1
    val (bitKey, previousKey) = pool.fields(slot)
    val previous = Value.select(started, stack.index, pool.index(-1))
    circuit.put(bitKey, Value.select(bit, Value.constant(true), Value.constant(false)), Vector(false, true), false)
    circuit.put(previousKey, previous, pool.indices, -1)
    stack.root = Ref.select(enabled, NEW, stack.root)
    stack.index = Value.select(enabled, pool.index(slot), stack.index)
    started = OR(started, enabled)
  }
}

object ScaffoldFlagPackets {
  def fixture(capacity: Int = 7): (Circuit, FlagPackets, (FlagStack, FlagStack), Scaffold) = {
    val circuit = new Circuit("ab<>cr!")
    val pool = new FlagPackets(circuit, capacity)
    val x = new FlagStack(pool, "x")
    val y = new FlagStack(pool, "y")
    val char = circuit.input()
    x.clear(char.eqTo('!'))
    y.copyFrom(x, char.eqTo('c'))
    x.copyFrom(y, char.eqTo('r'))
    val a = x.pop(AND(char.eqTo('<'), neg(x.empty())))
    val b = y.pop(AND(char.eqTo('>'), neg(y.empty())))
    val writer = new PacketWriter(x)
    for (slot <- 0 until capacity) {
      val enabled = OR(char.eqTo('a'), if (slot % 3 != 1) { char.eqTo('b') } else { FALSE })
      val bit = if (slot % 2 == 0) { char.eqTo('a') } else { char.eqTo('b') }
      writer.push(bit, enabled)
    }
    val answer = OR(AND(char.eqTo('<'), a), AND(char.eqTo('>'), b))
    x.commit()
    y.commit()
    (circuit, pool, (x, y), circuit.machine(answer))
  }
}
