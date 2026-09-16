package pal

import scala.collection.immutable.VectorMap
import Expr.TRUE
import Ref.{NEW, PREVIOUS}
import ScaffoldCircuit.{conjunction, disjunction, neg, choose}
import ScaffoldCircuitInput.{InputHead, HeadPools, CounterPools}

/** A frozen reversed prefix followed by incrementally arriving text.
  * Text heads denote cuts and inspect their next cell, so they can wait at
  * the arrival frontier without moving past it or inventing an end marker.
  */
object ScaffoldMatchInput {
  final case class Pools(heads: HeadPools, queues: HeadPools, counters: CounterPools)

  /** Fixed construction counts: each name maps to (append, right, left). */
  def inputPools(circuit: Circuit, operations: collection.Map[String, (Int, Int, Int)]): Pools = {
    def pool(layout: Iterable[(String, Int)]): StackPool = {
      val entries = layout.toVector
      new StackPool(circuit, if (entries.exists(_._2 != 0)) { entries } else { Vector("unused" -> 1) })
    }
    val heads = VectorMap.from(Vector("l" -> 1, "r" -> 2).map { case (side, index) =>
      side -> pool(operations.map { case (name, counts) =>
        (name + "." + side) -> (if (index == 1) { counts._2 } else { counts._3 })
      })
    })
    val units = VectorMap.from(operations.iterator.map { case (name, counts) => name -> (3 * (counts._1 + 2 * counts._2)) })
    val rear = pool(for ((name, counts) <- operations.toVector; role <- Vector("B", "B2")) yield {
      (name + ".in." + role) -> counts._1
    })
    val reverse = pool(units.map { case (name, amount) => (name + ".in.Fr") -> amount })
    val front = pool(units.map { case (name, amount) => (name + ".in.Br") -> (2 * amount) })
    val queues = VectorMap("F" -> front, "WF" -> front, "Br" -> front, "B" -> rear, "WB" -> rear, "B2" -> rear, "Fr" -> reverse)
    val counters = VectorMap.from(Vector("m", "c").map { role =>
      role -> VectorMap.from(Vector("pos", "neg").map { side =>
        side -> pool(operations.map { case (name, calls) =>
          val amount = if (side == "pos") {
            if (role == "m") { units(name) } else { 2 * units(name) }
          } else if (role == "m") { units(name) + calls._2 } else { calls._1 + calls._2 }
          (name + ".in." + role + "." + side) -> amount
        })
      })
    })
    Pools(heads, queues, counters)
  }

  def fixture(): (Circuit, (MatchInput, MatchInput), Scaffold) = {
    val circuit = new Circuit("ab!<>[]xy.")
    var operations = VectorMap("global.begin" -> (1, 0, 0), "global.end" -> (1, 1, 0))
    for (name <- Vector("A", "B")) {
      operations = operations.updated(name + ".pattern", (0, 1, 1)).updated(name + ".text", (1, 1, 1))
    }
    val pools = inputPools(circuit, operations)
    val begin = new InputHead(pools.heads, pools.queues, pools.counters, "global.begin")
    val end = new InputHead(pools.heads, pools.queues, pools.counters, "global.end")
    val a = new MatchInput(pools, "A")
    val b = new MatchInput(pools, "B")
    val char = circuit.input()
    val arrival = disjunction(char.eqTo('a'), char.eqTo('b'))
    circuit.put("input", Value.select(char.eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    var active = circuit.get(PREVIOUS, "active", Vector(false, true), false).eqTo(true)
    Vector(begin, end).foreach(_.append(NEW, arrival))
    end.right(arrival)
    Vector(a, b).foreach(_.append(NEW, conjunction(arrival, active)))
    a.start(end, char.eqTo('!'))
    b.start(begin, char.eqTo('!'))
    active = disjunction(active, char.eqTo('!'))
    for ((head, right, left) <- Vector((a, '>', '<'), (b, ']', '['))) {
      head.move(1, conjunction(active, char.eqTo(right), head.available()))
      head.move(-1, conjunction(active, char.eqTo(left)))
    }
    a.copyFrom(b, char.eqTo('x'))
    b.copyFrom(a, char.eqTo('y'))
    Vector(begin, end).foreach(_.commit(maintain = false))
    for ((name, head) <- Vector("A" -> a, "B" -> b)) {
      circuit.put(name + ".observed", head.read(), Vector(None, 'a', 'b'), None)
      head.commit()
    }
    circuit.put("active", Value.select(active, Value.constant(true), Value.constant(false)))
    (circuit, (a, b), circuit.machine(conjunction(active, a.available(), b.available(), a.read().equal(b.read()))))
  }
}

final class MatchInput(pools: ScaffoldMatchInput.Pools, name: String) {
  val pattern = new InputHead(pools.heads, pools.queues, pools.counters, name + ".pattern")
  val text = new InputHead(pools.heads, pools.queues, pools.counters, name + ".text")
  val circuit: Circuit = pattern.circuit
  val modeKey: String = name + ".text_mode"
  var textMode: Expr = circuit.get(PREVIOUS, modeKey, Vector(false, true), false).eqTo(true)

  def start(snapshot: InputHead, enabled: Expr = TRUE): Unit = {
    pattern.copyFrom(snapshot, enabled)
    text.reset(enabled)
    textMode = choose(enabled, neg(snapshot.focus.present()), textMode)
  }
  def append(cell: Ref, enabled: Expr = TRUE): Unit = { text.append(cell, enabled) }
  def available(): Expr = choose(textMode, text.canRight(), pattern.focus.present())
  def read(): Value[Any] = {
    val target = Ref.select(textMode, text.peekRight(), pattern.focus)
    val value = circuit.get(target, "input", Vector('a', 'b'), 'a')
    Value.select(target.present(), value, Value.constant(None))
  }
  def move(direction: Int, enabled: Expr = TRUE): Unit = {
    if (direction != -1 && direction != 1) { throw new IllegalArgumentException("unit direction required") }
    val mode = textMode
    if (direction == 1) {
      pattern.left(conjunction(enabled, neg(mode)))
      text.right(conjunction(enabled, mode))
      val reachedText = conjunction(enabled, neg(mode), neg(pattern.focus.present()))
      textMode = disjunction(mode, reachedText)
    } else {
      val atTextStart = neg(text.focus.present())
      text.left(conjunction(enabled, mode, neg(atTextStart)))
      val enterPattern = conjunction(enabled, mode, atTextStart)
      pattern.right(conjunction(enabled, disjunction(neg(mode), atTextStart)))
      textMode = conjunction(mode, neg(enterPattern))
    }
  }
  def copyFrom(other: MatchInput, enabled: Expr = TRUE): Unit = {
    pattern.copyFrom(other.pattern, enabled)
    text.copyFrom(other.text, enabled)
    textMode = choose(enabled, other.textMode, textMode)
  }
  def commit(): Unit = {
    pattern.commit(maintain = false)
    text.commit(maintain = false)
    circuit.put(modeKey, Value.select(textMode, Value.constant(true), Value.constant(false)))
  }
}
