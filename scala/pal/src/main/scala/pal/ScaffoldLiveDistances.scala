package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Compile only live head differences, sharing finite counter registers.
  * Port of `scaffold_live_distances.py`; copies use pre-instruction snapshots.
  */
final class LiveDistances(val circuit: Circuit, val program: Program, headNames: Vector[String],
                          prefix: String = "distance", observePositions: Boolean = true,
                          availabilityDistance: Boolean = true) {
  import Expr.{TRUE, FALSE}
  import ScaffoldCircuit.disjunction

  val analysis: Liveness = GsHeadLiveness.analyze(program, headNames, observePositions, availabilityDistance)
  val names: Vector[String] = analysis.names
  val pool = new StackPool(circuit, Vector("cells" -> (analysis.registers + 1)))
  val registers: Vector[Counter] = Vector.tabulate(analysis.registers) { index =>
    new Counter(pool, s"$prefix.r$index", Some("cells"))
  }
  val counters: VectorMap[(String, String), Counter] = VectorMap.from(analysis.colors.iterator.map {
    case (pair, color) => pair -> registers(color)
  })
  val length = new Counter(pool, prefix + ".load_length", Some("cells"))

  def equal(left: String, right: String): Expr = {
    analysis.canonical(left, right)._1.fold(TRUE)(pair => counters(pair).zero())
  }

  def less(left: String, right: String): Expr = {
    val (pair, sign) = analysis.canonical(left, right)
    pair.fold(FALSE) { p => if (sign == 1) counters(p).negative() else counters(p).positive() }
  }

  def loadOne(enabled: Expr): Unit = length.inc(enabled, Some(analysis.registers))

  def initialize(values: collection.Map[(String, String), Option[(Counter, Int)]], enabled: Expr): Unit = {
    if (values.keySet != analysis.before(program.start)) {
      throw new IllegalArgumentException("every live entry difference needs an explicit initialization")
    }
    values.foreach { case (pair, value) =>
      value match {
        case None => counters(pair).reset(enabled)
        case Some((source, sign)) => assign(counters(pair), source.positiveStack, source.negativeStack, sign, enabled)
      }
    }
  }

  private def assign(target: Counter, positive: Stack, negative: Stack, sign: Int, enabled: Expr): Unit = {
    target.positiveStack.copyFrom(if (sign == -1) negative else positive, enabled)
    target.negativeStack.copyFrom(if (sign == -1) positive else negative, enabled)
  }

  def execute(events: Seq[Expr]): Unit = {
    if (events.size != program.code.size) {
      throw new IllegalArgumentException("one instruction guard per finite state required")
    }
    val increments = Vector.fill(registers.size)(mutable.ArrayBuffer.empty[Expr])
    val decrements = Vector.fill(registers.size)(mutable.ArrayBuffer.empty[Expr])
    val resets = mutable.LinkedHashMap.empty[Int, mutable.ArrayBuffer[Expr]]
    val copies = mutable.LinkedHashMap.empty[(Int, Int, Int), mutable.ArrayBuffer[Expr]]
    program.code.zip(events).zipWithIndex.foreach { case ((row, enabled), state) =>
      row.event match {
        case Event.Move(moves) =>
          if (moves.size != 1 || math.abs(moves.head.delta) != 1) {
            throw new IllegalArgumentException("unit movement required")
          }
          val Event.Movement(head, amount) = moves.head
          analysis.after(state).foreach { pair =>
            if (pair._1 == head || pair._2 == head) {
              val change = if (pair._1 == head) amount else -amount
              (if (change == 1) increments else decrements)(analysis.colors(pair)) += enabled
            }
          }
        case Event.Copy(target, source) =>
          analysis.after(state).foreach { pair =>
            if (pair._1 == target || pair._2 == target) {
              val (original, sign) = analysis.canonical(
                if (pair._1 == target) source else pair._1, if (pair._2 == target) source else pair._2)
              val destination = analysis.colors(pair)
              original match {
                case None => resets.getOrElseUpdate(destination, mutable.ArrayBuffer.empty) += enabled
                case Some(from) =>
                  val origin = analysis.colors(from)
                  if (destination != origin || sign != 1) {
                    copies.getOrElseUpdate((destination, origin, sign), mutable.ArrayBuffer.empty) += enabled
                  }
              }
            }
          }
        case _ => ()
      }
    }
    val snapshots = registers.map(counter => new Counter(pool, counter.positiveStack.name.stripSuffix(".pos"), Some("cells")))
    registers.zipWithIndex.foreach { case (counter, index) =>
      counter.inc(disjunction(increments(index).toSeq*), Some(index))
      counter.dec(disjunction(decrements(index).toSeq*), Some(index))
    }
    resets.foreach { case (index, conditions) => registers(index).reset(disjunction(conditions.toSeq*)) }
    copies.foreach { case ((destination, origin, sign), conditions) =>
      val source = snapshots(origin)
      assign(registers(destination), source.positiveStack, source.negativeStack, sign, disjunction(conditions.toSeq*))
    }
  }

  def commit(): Unit = { registers.foreach(_.commit()); length.commit() }
}
