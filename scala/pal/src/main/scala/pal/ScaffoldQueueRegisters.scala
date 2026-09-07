package pal

import scala.collection.immutable.VectorMap

import Expr.FALSE
import ScaffoldCircuit.{conjunction, disjunction, neg}
import Ref.NEW

/** A fixed bank of queues sharing one physical instruction's cell storage.
  *
  * In each transition exactly one bank operation may allocate: push, pop, or
  * one rotation work unit on one selected queue. Copies allocate no cells.
  * Three separately scheduled work units follow each logical push/pop before
  * another logical operation on that queue. They are not unrolled into a bank
  * of per-object allocation slots.
  *
  * Port of `scaffold_queue_registers.py`.
  */
final class QueueRegisters(val circuit: Circuit, nameSeq: Seq[String]) {
  val names: Vector[String] = nameSeq.toVector
  if (names.isEmpty || names.distinct.length != names.length) {
    throw new IllegalArgumentException("a fixed nonempty set of distinct queue names is required")
  }

  private def pool(slots: Int = 1): StackPool = new StackPool(circuit, Vector("cells" -> slots))

  private val front = pool()
  private val rear = pool()
  private val reverse = pool()

  /** Stack role -> shared cell pool. */
  val cells: Map[String, StackPool] = Map("F" -> front, "WF" -> front, "Br" -> front, "B" -> rear, "WB" -> rear,
                                          "B2" -> rear, "Fr" -> reverse)

  /** Counter role -> side -> pool. */
  val counterCells: Map[String, Map[String, StackPool]] = Map(
    "m" -> Map("pos" -> pool(), "neg" -> pool()),
    "c" -> Map("pos" -> pool(2), "neg" -> pool())
  )

  val queues: VectorMap[String, Queue] = VectorMap.from(names.map(name => name -> new Queue(cells, counterCells, name, sharedSlots = true)))

  /** Python `finalize()`. */
  def commit(): Unit = {
    for (queue <- queues.values) { queue.commit() }
  }
}

object ScaffoldQueueRegisters {

  /** Two queues driven by distinct symbols, with cross copies on `x`/`y`. */
  def fixture(): (Circuit, QueueRegisters, Scaffold) = {
    val circuit = new Circuit("abAB>.],xy")
    val bank = new QueueRegisters(circuit, Vector("q0", "q1"))
    val char = circuit.input()
    circuit.put("input", Value.select(disjunction(char.eqTo('b'), char.eqTo('B')),
                                      Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    var answer = FALSE
    val commands = Vector(('a', 'b', '>', '.'), ('A', 'B', ']', ','))
    for (((pushA, pushB, pop, work), index) <- commands.zipWithIndex) {
      val queue = bank.queues(s"q$index")
      queue.push(NEW, disjunction(char.eqTo(pushA), char.eqTo(pushB)))
      val take = conjunction(char.eqTo(pop), neg(queue.stacks("F").empty()))
      val value = queue.pop(take)
      answer = disjunction(answer, conjunction(take, circuit.get(value, "input", Vector('a', 'b'), 'a').eqTo('a')))
      queue.workUnit(char.eqTo(work))
    }
    bank.queues("q1").copyFrom(bank.queues("q0"), char.eqTo('x'))
    bank.queues("q0").copyFrom(bank.queues("q1"), char.eqTo('y'))
    bank.commit()
    (circuit, bank, circuit.machine(answer))
  }
}
