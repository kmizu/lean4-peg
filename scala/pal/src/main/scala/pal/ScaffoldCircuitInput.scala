package pal

import Expr.TRUE
import Ref.{EMPTY, NEW, PREVIOUS}
import ScaffoldCircuit.*

/** Clonable readonly letter/gap input heads in the symbolic scaffold circuit. */
object ScaffoldCircuitInput {
  type HeadPools = Map[String, StackPool]
  type CounterPools = Map[String, Map[String, StackPool]]

  private def headPools(pool: StackPool): HeadPools = Map("l" -> pool, "r" -> pool)
  private def queuePools(pool: StackPool): HeadPools =
    Vector("F", "B", "B2", "Fr", "Br", "WF", "WB").map(_ -> pool).toMap
  private def counterPools(pool: StackPool): CounterPools =
    Map("m" -> Map("pos" -> pool, "neg" -> pool), "c" -> Map("pos" -> pool, "neg" -> pool))

  final class InputHead(pools: HeadPools, queues: HeadPools, counters: CounterPools,
                        val name: String, val alphabet: String = "ab") {
    def this(headPool: StackPool, queuePool: StackPool, counterPool: StackPool, name: String) = {
      this(headPools(headPool), queuePools(queuePool), counterPools(counterPool), name, "ab")
    }
    val circuit: Circuit = pools("l").circuit
    val focusKey: String = name + ".focus"
    var focus: Ref = circuit.getRef(PREVIOUS, focusKey)
    val leftStack: Stack = new Stack(pools("l"), name + ".l")
    val rightStack: Stack = new Stack(pools("r"), name + ".r")
    val incoming: Queue = new Queue(queues, counters, name + ".in")

    def append(cell: Ref = NEW, enabled: Expr = TRUE): Unit = {
      incoming.push(cell, enabled)
      incoming.work(enabled)
    }

    def read(): Value[Any] = {
      val symbol = circuit.get(focus, "input", alphabet.toVector, alphabet.head)
      Value.select(focus.present(), symbol, Value.constant(None))
    }

    def canRight(): Expr = disjunction(neg(rightStack.empty()), neg(incoming.empty()))

    /** Read the next cell at an operation boundary without moving the head. */
    def peekRight(): Ref = {
      val saved = rightStack.peek()._1
      val arrived = incoming.stacks("F").peek()._1
      val fromStack = neg(rightStack.empty())
      circuit.require(neg(incoming.stacks("F").empty()), conjunction(neg(fromStack), neg(incoming.empty())))
      Ref.select(fromStack, saved, arrived)
    }

    def reset(enabled: Expr = TRUE): Unit = {
      focus = Ref.select(enabled, EMPTY, focus)
      leftStack.clear(enabled)
      rightStack.clear(enabled)
      incoming.clear(enabled)
    }

    def right(enabled: Expr = TRUE): Unit = {
      circuit.require(canRight(), enabled)
      leftStack.push(focus, enabled = enabled)
      val fromStack = neg(rightStack.empty())
      val fromQueue = conjunction(enabled, neg(fromStack))
      val saved = rightStack.pop(conjunction(enabled, fromStack))._1
      incoming.work(fromQueue)
      val arrived = incoming.pop(fromQueue)
      incoming.work(fromQueue)
      focus = Ref.select(enabled, Ref.select(fromStack, saved, arrived), focus)
    }

    def left(enabled: Expr = TRUE): Unit = {
      circuit.require(neg(leftStack.empty()), enabled)
      rightStack.push(focus, enabled = enabled)
      val saved = leftStack.pop(enabled)._1
      focus = Ref.select(enabled, saved, focus)
    }

    def copyFrom(other: InputHead, enabled: Expr = TRUE): Unit = {
      focus = Ref.select(enabled, other.focus, focus)
      leftStack.copyFrom(other.leftStack, enabled)
      rightStack.copyFrom(other.rightStack, enabled)
      incoming.copyFrom(other.incoming, enabled)
    }

    def commit(maintain: Boolean = true): Unit = {
      if (maintain) { incoming.work() }
      leftStack.commit()
      rightStack.commit()
      incoming.commit()
      circuit.putRef(focusKey, focus)
    }
  }

  final class PlaceHead(pools: HeadPools, queues: HeadPools, counters: CounterPools,
                        val name: String, alphabet: String = "ab") {
    def this(headPool: StackPool, queuePool: StackPool, counterPool: StackPool, name: String) = {
      this(headPools(headPool), queuePools(queuePool), counterPools(counterPool), name, "ab")
    }
    val head: InputHead = new InputHead(pools, queues, counters, name, alphabet)
    val circuit: Circuit = head.circuit
    val gapKey: String = name + ".gap"
    var gap: Expr = circuit.get(PREVIOUS, gapKey, Vector(false, true), true).eqTo(true)

    def append(cell: Ref, enabled: Expr = TRUE): Unit = head.append(cell, enabled)

    def read(): Value[Any] = {
      val value = head.read()
      Value.select(value.eqTo(None), Value.constant(None), Value.select(gap, Value.constant('s'), value))
    }

    def canRight(): Expr = disjunction(neg(gap), head.canRight())

    def right(enabled: Expr = TRUE): Unit = {
      head.right(conjunction(enabled, gap))
      gap = choose(enabled, neg(gap), gap)
    }

    def left(enabled: Expr = TRUE): Unit = {
      circuit.require(neg(head.read().eqTo(None)), enabled)
      head.left(conjunction(enabled, neg(gap)))
      gap = choose(enabled, neg(gap), gap)
    }

    def isFirst(): Expr = {
      val before = head.leftStack.peek()._1
      conjunction(neg(gap), neg(head.leftStack.empty()), neg(before.present()))
    }

    def copyFrom(other: PlaceHead, enabled: Expr = TRUE): Unit = {
      head.copyFrom(other.head, enabled)
      gap = choose(enabled, other.gap, gap)
    }

    def commit(): Unit = {
      head.commit()
      circuit.put(gapKey, Value.select(gap, Value.constant(true), Value.constant(false)))
    }
  }
}
