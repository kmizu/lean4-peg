package pal

import Expr.{TRUE, FALSE}
import ScaffoldCircuit.{conjunction as AND, choose, neg}

/** Live GS head differences as windowed signed registers and a finite ROM. */
final class WindowLiveDistances(circuit: Circuit, val program: Program, names: Seq[String], radius: BigInt,
                                prefix: String = "distance", extra: Seq[String] = Vector.empty,
                                val availabilityDistance: Boolean = true) {
  val analysis: Liveness = GsHeadLiveness.analyze(program, names.toVector, observePositions = false, availabilityDistance = availabilityDistance)
  val keys: Vector[String] = Vector.tabulate(analysis.registers)(i => s"$prefix.r$i")
  val lengthKey: String = prefix + ".length"
  val values: WindowRegisters = new WindowRegisters(circuit, keys ++ Vector(lengthKey) ++ extra, radius)

  /** Add simultaneous register-transfer columns to the controller ROM.
    * Rows/domains are insertion-ordered mutable builders, as in the Python ROM.
    * A missing source is represented by Scala None (Python None).
    */
  def augmentRows(rows: Vector[ScaffoldRom.TableRow], domains: ScaffoldRom.Domains): Unit = {
    for (((instruction, row), state) <- program.code.zip(rows).zipWithIndex) {
      for (key <- keys) {
        row(key + ".source") = key
        row(key + ".reverse") = false
        row(key + ".delta") = 0
      }
      row("distance.test") = keys.head
      row("distance.reverse") = false
      val comparison = instruction.event match {
        case Event.Less(a, b) => Some((a, b))
        case Event.Equal(a, b) => Some((a, b))
        case Event.AssertEqual(a, b) => Some((a, b))
        case Event.Available(a) if availabilityDistance => Some((a, "OriginalEnd"))
        case _ => None
      }
      for ((a, b) <- comparison) {
        val (pair, sign) = analysis.canonical(a, b)
        row("distance.test") = pair.map(p => keys(analysis.colors(p))).getOrElse(None)
        row("distance.reverse") = sign == -1
      }
      instruction.event match {
        case Event.Move(moves) =>
          val deltas = moves.map(move => move.head -> move.delta).toMap
          for (pair <- analysis.after(state)) {
            row(keys(analysis.colors(pair)) + ".delta") = deltas.getOrElse(pair._1, 0) - deltas.getOrElse(pair._2, 0)
          }
        case Event.Copy(target, source) =>
          for (pair <- analysis.after(state) if pair._1 == target || pair._2 == target) {
            val (original, sign) = analysis.canonical(if (pair._1 == target) { source } else { pair._1 }, if (pair._2 == target) { source } else { pair._2 })
            val key = keys(analysis.colors(pair))
            row(key + ".source") = original.map(p => keys(analysis.colors(p))).getOrElse(None)
            row(key + ".reverse") = sign == -1
          }
        case _ => ()
      }
    }
    for (key <- keys :+ "distance") {
      val suffixes = if (key != "distance") { Vector("source", "reverse", "delta") } else { Vector("test", "reverse") }
      for (suffix <- suffixes) {
        val field = key + "." + suffix
        domains(field) = rows.map(_(field)).distinct.toVector
      }
    }
  }
  def initialize(enabled: Expr): Unit = {
    for (pair <- analysis.before(program.start)) {
      val target = keys(analysis.colors(pair))
      if (pair._1 == "OriginalEnd" || pair._2 == "OriginalEnd") {
        values.assign(target, values.registers(lengthKey), enabled, if (pair._2 == "OriginalEnd") { TRUE } else { FALSE })
      } else {
        values.reset(target, enabled)
      }
    }
  }
  def initializeValues(mapping: collection.Map[(String, String), Option[(String, Int)]], enabled: Expr): Unit = {
    require(mapping.keySet == analysis.before(program.start), "every live entry distance requires an explicit source")
    for ((pair, value) <- mapping) {
      val target = keys(analysis.colors(pair))
      value match {
        case None => values.reset(target, enabled)
        case Some((key, sign)) => values.assign(target, values.registers(key), enabled, if (sign == -1) { TRUE } else { FALSE })
      }
    }
  }
  def loadOne(enabled: Expr): Unit = values.add(lengthKey, 1, enabled)
  def compare(fields: collection.Map[String, Value[Any]]): (Expr, Expr) = {
    val register = values.select(fields("distance.test"))
    val (zero, less) = values.compareZero(register)
    (zero, choose(fields("distance.reverse").eqTo(true), AND(neg(zero), neg(less)), less))
  }
  def execute(fields: collection.Map[String, Value[Any]], enabled: Expr): Unit = {
    val snapshots = values.registers
    for (key <- keys) {
      val source = values.select(fields(key + ".source"), snapshots)
      values.assign(key, source, enabled, fields(key + ".reverse").eqTo(true))
      values.addSelected(key, fields(key + ".delta"), enabled)
    }
  }
  def commit(): Unit = values.commit()
}
