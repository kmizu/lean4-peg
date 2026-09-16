package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Finite lookup tables as shared Boolean decision diagrams.
  * A read instantiates a fixed Boolean DAG; emitted PEGs contain no array lookup.
  * Port of `scaffold_rom.py`.
  */
final class ROM(sourceRows: Iterable[collection.Map[String, Any]],
                sourceDomains: collection.Map[String, Seq[Any]]) {
  val rows: Vector[VectorMap[String, Any]] = sourceRows.iterator.map(VectorMap.from).toVector
  val domains: VectorMap[String, Vector[Any]] = VectorMap.from(sourceDomains.iterator.map {
    case (key, values) => key -> values.toVector
  })
  if (rows.isEmpty || rows.exists(_.keySet != domains.keySet)) {
    throw new IllegalArgumentException("every finite table row must cover the declared columns")
  }
  if (domains.values.exists(d => d.isEmpty || d.distinct.size != d.size)) {
    throw new IllegalArgumentException("finite column values must be distinct")
  }
  val width: Int = 32 - Integer.numberOfLeadingZeros(rows.size - 1)
  private val nodeBuffer = mutable.ArrayBuffer.empty[(Int, Int, Int)]
  private val unique = mutable.HashMap.empty[(Int, Int, Int), Int]
  private val memo = mutable.HashMap.empty[(Int, Vector[Boolean]), Int]

  private def build(values: Vector[Boolean], bit: Int): Int = {
    if (!values.contains(true)) { 0 }
    else if (!values.contains(false)) { 1 }
    else {
      memo.getOrElseUpdate((bit, values), {
        val half = values.size / 2
        val no = build(values.take(half), bit - 1)
        val yes = build(values.drop(half), bit - 1)
        if (yes == no) { yes }
        else {
          val node = (bit, yes, no)
          unique.getOrElseUpdate(node, {
            val index = nodeBuffer.size + 2
            nodeBuffer += node
            index
          })
        }
      })
    }
  }

  val outputs: VectorMap[String, Vector[Int]] = {
    val padded = rows ++ Vector.fill((1 << width) - rows.size)(rows.head)
    VectorMap.from(domains.iterator.map { case (key, domain) =>
      val indices = domain.zipWithIndex.toMap
      val encoded = padded.map(row => indices(row(key)))
      val bits = 32 - Integer.numberOfLeadingZeros(domain.size - 1)
      key -> Vector.tabulate(bits)(bit => build(encoded.map(v => (v & (1 << bit)) != 0), width - 1))
    })
  }
  val nodes: Vector[(Int, Int, Int)] = nodeBuffer.toVector

  def read(bits: Seq[Expr]): VectorMap[String, Value[Any]] = {
    if (bits.size != width) {
      throw new IllegalArgumentException("ROM address width does not match its finite table")
    }
    val expressions = mutable.ArrayBuffer[Expr](Expr.FALSE, Expr.TRUE)
    nodes.foreach { case (bit, yes, no) =>
      expressions += ScaffoldCircuit.choose(bits(bit), expressions(yes), expressions(no))
    }
    VectorMap.from(outputs.iterator.map { case (key, indices) =>
      key -> Value.encoded(domains(key), indices.map(expressions))
    })
  }
}

object ScaffoldRom {
  type TableRow = mutable.LinkedHashMap[String, Any]
  type Domains = mutable.LinkedHashMap[String, Seq[Any]]

  /** Decode a GS finite table, optionally including colored data-head roles. */
  def controllerTable(program: Program, names: Seq[String], readers: Option[ReaderLiveness] = None,
                      readerNames: Seq[String] = Vector.empty, batched: Boolean = false,
                      augment: Option[(Vector[TableRow], Domains) => Unit] = None): ROM = {
    import Event.*
    val tests = Set("equal", "less", "symbols", "available")
    val rows = program.code.zipWithIndex.map { case (instruction, state) =>
      val event = instruction.event
      val next = instruction.targets.headOption.getOrElse(state)
      val row = mutable.LinkedHashMap[String, Any](
        "op" -> event.op, "left" -> names.head, "right" -> names.head, "direction" -> 1,
        "bit" -> false, "no" -> next,
        "yes" -> (if (tests(event.op)) instruction.targets(1) else next))
      def pair(left: String, right: String): Unit = { row("left") = left; row("right") = right }
      event match {
        case Equal(l, r) => pair(l, r)
        case Less(l, r) => pair(l, r)
        case Symbols(l, r) => pair(l, r)
        case AssertEqual(l, r) => pair(l, r)
        case Copy(l, r) => pair(l, r)
        case Move(moves) =>
          if (!batched && (moves.size != 1 || math.abs(moves.head.delta) != 1)) {
            throw new IllegalArgumentException("unit movement table required")
          }
          if (!batched) { row("left") = moves.head.head; row("direction") = moves.head.delta }
        case Available(head) => row("left") = head
        case Match(head) => row("left") = head
        case Border(head) => row("left") = head
        case Flag(bit) => row("bit") = bit
        case Halt => ()
      }
      readers.foreach { live =>
        Vector("data_left", "data_right", "data_target", "data_source", "data_move").foreach(row(_) = None)
        if (batched) { readerNames.foreach(name => row("data_delta." + name) = 0) }
        def color(name: String): String = readerNames(live.colors(name))
        event match {
          case Symbols(l, r) => row("data_left") = color(l); row("data_right") = color(r)
          case Available(head) => row("data_left") = color(head)
          case Copy(target, source) if live.after(state)(target) =>
            row("data_target") = color(target); row("data_source") = color(source)
          case Move(moves) if batched =>
            moves.filter(m => live.after(state)(m.head)).foreach { move =>
              val key = "data_delta." + color(move.head)
              row(key) = row(key).asInstanceOf[Int] + move.delta
            }
          case Move(moves) if live.after(state)(moves.head.head) => row("data_move") = color(moves.head.head)
          case _ => ()
        }
      }
      row
    }
    val domains: Domains = mutable.LinkedHashMap(
      "op" -> rows.map(_("op")).distinct, "left" -> names, "right" -> names,
      "direction" -> Vector(-1, 1), "bit" -> Vector(false, true),
      "no" -> rows.indices.toVector, "yes" -> rows.indices.toVector)
    if (readers.nonEmpty) {
      Vector("data_left", "data_right", "data_target", "data_source", "data_move").foreach { key =>
        domains(key) = Vector(None) ++ readerNames
      }
      if (batched) {
        readerNames.foreach { name =>
          val key = "data_delta." + name
          domains(key) = rows.map(_(key)).distinct
        }
      }
    }
    augment.foreach(_(rows, domains))
    new ROM(rows, domains)
  }
}
