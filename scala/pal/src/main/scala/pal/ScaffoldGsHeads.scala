package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable
import Expr.FALSE
import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction, disjunction, neg}

/** Finite GS head table lowered to one-instruction scaffold transitions.
  * Loading and rewinding are actual transitions; the fixture is not PAL.
  */
final class ScaffoldGsHeads(val circuit: Circuit, source: Option[Program] = None,
                    prefix: String = "gs", val compact: Boolean = true) {
  val program: Program = GsHeads.unitMoves(source.getOrElse(GsHeads.compileController()))
  val bank: Option[LiveDistances] = if (compact) {
    Some(new LiveDistances(circuit, program, GsHeads.HEADS, prefix + ".distance"))
  } else { None }
  val fullBank: Option[HeadDistances] = if (compact) { None } else {
    Some(new HeadDistances(circuit, GsHeads.HEADS, prefix = prefix + ".distance", exclusiveMoves = true))
  }
  val pool = new StackPool(circuit, Vector("cells" -> 1), Vector('_', 'a', 'b', '#'))
  val tapes: VectorMap[String, Tape] = VectorMap.from(GsHeads.HEADS.filterNot(GsHeads.BLIND).map { head =>
    head -> new Tape(circuit, prefix + "." + head, pool.payload, pool = Some(pool))
  })
  val pcKey: String = prefix + ".pc"
  val modeKey: String = prefix + ".mode"
  var pc: Value[Int] = circuit.get(PREVIOUS, pcKey, program.code.indices.toVector, program.start)
  var mode: Value[String] = circuit.get(PREVIOUS, modeKey, Vector("load", "rewind", "run", "done"), "load")
  val foundKey: String = prefix + ".found"
  var found: Expr = circuit.get(PREVIOUS, foundKey, Vector(false, true), false).eqTo(true)
  var border: Expr = FALSE

  private def equal(left: String, right: String): Expr = {
    bank.fold(fullBank.get.equal(left, right))(_.equal(left, right))
  }
  private def less(left: String, right: String): Expr = {
    bank.fold(fullBank.get.less(left, right))(_.less(left, right))
  }

  def copy(target: String, source: String, enabled: Expr): Unit = {
    fullBank.foreach(_.copy(target, source, enabled))
    if (tapes.contains(target)) {
      if (!tapes.contains(source)) { throw new IllegalArgumentException("a data head cannot copy a blind coordinate") }
      val a = tapes(target)
      val b = tapes(source)
      a.left.copyFrom(b.left, enabled)
      a.right.copyFrom(b.right, enabled)
      a.write(b.focus, enabled)
    }
  }

  def tick(): Unit = {
    val char = circuit.input()
    val load = conjunction(mode.eqTo("load"), disjunction("ab#".map(char.eqTo)*))
    val finishLoad = conjunction(mode.eqTo("load"), char.eqTo('!'))
    val rewind = conjunction(mode.eqTo("rewind"), char.eqTo('.'))
    val atOrigin = if (compact) { tapes("Origin").left.empty() } else { equal("Origin", "First") }
    val begin = conjunction(rewind, atOrigin)
    val active = conjunction(mode.eqTo("run"), char.eqTo('.'))
    val moves = mutable.LinkedHashMap.from(for (head <- GsHeads.HEADS; d <- Vector(-1, 1)) yield {
      (head, d) -> mutable.ArrayBuffer.empty[Expr]
    })
    val copies = mutable.LinkedHashMap.empty[(String, String), Expr]
    val nextPc = mutable.LinkedHashMap.empty[Int, Expr]
    val halts = mutable.ArrayBuffer.empty[Expr]
    val borders = mutable.ArrayBuffer.empty[Expr]
    def edge(destination: Int, enabled: Expr): Unit = {
      nextPc(destination) = disjunction(nextPc.getOrElse(destination, FALSE), enabled)
    }
    val events = program.code.indices.map(state => conjunction(active, pc.eqTo(state))).toVector
    for ((enabled, Row(event, targets)) <- events.zip(program.code)) {
      def branch(decision: Expr): Unit = {
        edge(targets(0), conjunction(enabled, neg(decision)))
        edge(targets(1), conjunction(enabled, decision))
      }
      event match {
        case Event.Symbols(left, right) =>
          val a = tapes(left).focus
          val b = tapes(right).focus
          circuit.require(conjunction(neg(a.eqTo('_')), neg(b.eqTo('_'))), enabled)
          branch(a.equal(b))
        case Event.Equal(left, right) => branch(equal(left, right))
        case Event.Less(left, right) => branch(less(left, right))
        case Event.Halt => halts += enabled
        case other =>
          edge(targets(0), enabled)
          other match {
            case Event.Move(batch) =>
              if (batch.size != 1 || math.abs(batch.head.delta) != 1) {
                throw new IllegalArgumentException("unit head instruction required")
              }
              moves((batch.head.head, batch.head.delta)) += enabled
            case Event.Copy(target, source) =>
              val pair = (target, source)
              copies(pair) = disjunction(copies.getOrElse(pair, FALSE), enabled)
            case Event.Border(_) => borders += enabled
            case _ => throw new IllegalArgumentException("unsupported GS instruction")
          }
      }
    }
    moves(("OriginalEnd", 1)) += load
    moves(("Origin", -1)) += conjunction(rewind, neg(atOrigin))
    tapes("OriginalEnd").write(Value("ab#".map(s => s -> char.eqTo(s))), load)
    bank.foreach { distances => distances.execute(events); distances.loadOne(load) }
    for (((head, direction), conditions) <- moves) {
      val enabled = disjunction(conditions.toSeq*)
      if (enabled != FALSE) {
        fullBank.foreach(_.move(head, direction, enabled))
        tapes.get(head).foreach(_.move(direction, enabled, Some(0)))
      }
    }
    for (((target, source), enabled) <- copies) { copy(target, source, enabled) }
    copy("Origin", "OriginalEnd", finishLoad)
    for (target <- GsHeads.HEADS if target != "Origin" && target != "OriginalEnd") { copy(target, "Origin", begin) }
    bank.foreach(distances => distances.initialize(Map(("Origin", "OriginalEnd") -> Some((distances.length, -1))), begin))
    val halt = disjunction(halts.toSeq*)
    border = disjunction(borders.toSeq*)
    found = disjunction(found, border)
    pc = Value.select(conjunction(active, neg(halt)), Value(nextPc), pc)
    mode = Value.select(finishLoad, Value.constant("rewind"), mode)
    mode = Value.select(begin, Value.constant("run"), mode)
    mode = Value.select(halt, Value.constant("done"), mode)
  }

  def commit(): Unit = {
    bank.foreach(_.commit())
    fullBank.foreach(_.commit())
    tapes.values.foreach(_.commit())
    circuit.put(pcKey, pc)
    circuit.put(modeKey, mode)
    circuit.put(foundKey, Value.select(found, Value.constant(true), Value.constant(false)))
  }
}

object ScaffoldGsHeads {
  def fixture(program: Option[Program] = None, compact: Boolean = true): (Circuit, ScaffoldGsHeads, Scaffold) = {
    val circuit = new Circuit("ab#!.")
    val worker = new ScaffoldGsHeads(circuit, program, compact = compact)
    worker.tick()
    worker.commit()
    circuit.put("gs.border", Value.select(worker.border, Value.constant(true), Value.constant(false)), Vector(false, true), false)
    (circuit, worker, circuit.machine(conjunction(worker.mode.eqTo("done"), worker.found)))
  }
}
