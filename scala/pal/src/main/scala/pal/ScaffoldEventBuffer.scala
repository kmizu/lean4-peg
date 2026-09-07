package pal

import scala.collection.mutable

import Expr.{TRUE, FALSE}
import ScaffoldCircuit.{choose, conjunction as AND, disjunction as OR, neg as NOT}
import Ref.{NEW, PREVIOUS}

/** Finite local FIFO wrapper for an online read/work/output scaffold.
  *
  * Wrapper events a/b enqueue one real input; '.' performs one source service
  * unit. The source sees a/b only at its read boundary, otherwise '.'. The
  * buffer uses the existing persistent real-time queue, with a fixed number of
  * stack operations per wrapper transition. A later round packing binds one
  * enqueue and the derived number of service transitions to each real symbol.
  *
  * Port of `scaffold_event_buffer.py`.
  */
object ScaffoldEventBuffer {
  import Expr.*

  val PREFIX = "source."

  /** Rename source fields and substitute its input event predicates.
    *
    * Returns the rewritten label and pointer equations of `source`, in order.
    */
  def substituteSource(source: Scaffold, symbols: collection.Map[Char, Expr]): (mutable.LinkedHashMap[String, Expr], mutable.LinkedHashMap[String, Expr]) = {
    val memo = new java.util.IdentityHashMap[Expr, Expr]()

    // Python: every argument of not/and/or/select/present, the target of read/edge, else nothing.
    def children(expr: Expr): Vector[Expr] = ScaffoldOptimize.children(expr)

    def rename(path: Vector[String]): Vector[String] = path.map(PREFIX + _)

    def rebuild(expr: Expr): Expr = {
      expr match {
        case Symbol(char) => symbols(char)
        case Old(path, label) => Expr.old(rename(path), PREFIX + label)
        case Exists(path) => Expr.exists(rename(path))
        case Pointer(path) => Expr.pointer(rename(path))
        case Read(target, label) => Expr.read(memo.get(target), PREFIX + label)
        case Edge(target, field) => Expr.edge(memo.get(target), PREFIX + field)
        case _ =>
          val parts = children(expr)
          if (parts.nonEmpty) { Expr.make(expr.tag, parts.map(memo.get)) } else { expr }
      }
    }

    def rewrite(expression: Expr): Expr = {
      val work = mutable.Stack[(Expr, Boolean)]((expression, false))
      while (work.nonEmpty) {
        val (expr, done) = work.pop()
        if (!memo.containsKey(expr)) {
          if (!done) {
            work.push((expr, true))
            children(expr).foreach(child => work.push((child, false)))
          } else {
            memo.put(expr, rebuild(expr))
          }
        }
      }
      memo.get(expression)
    }

    val labels = mutable.LinkedHashMap.empty[String, Expr]
    for ((key, expr) <- source.labels) { labels(key) = rewrite(expr) }
    val pointers = mutable.LinkedHashMap.empty[String, Expr]
    for ((key, expr) <- source.pointers) { pointers(key) = rewrite(expr) }
    (labels, pointers)
  }

  /** Wrap `source` (alphabet `ab.`) in a local FIFO; returns the circuit and the machine over `ab.`. */
  def bufferSource(source: Scaffold, readyLabel: String, eventLabel: String, valueLabel: String): (Circuit, Scaffold) = {
    if (source.alphabet != "ab.") { throw new IllegalArgumentException("source must expose binary read events and '.' work") }
    if (!source.initial(readyLabel)) { throw new IllegalArgumentException("source must initially await input") }
    val c = new Circuit("ab.")
    val ingest = NOT(c.input().eqTo('.'))
    c.put("buffer.symbol", Value.select(c.input().eqTo('b'), Value.constant('b'), Value.constant('a')), Vector('a', 'b'), 'a')
    val cells = new StackPool(c, Vector("q.F" -> 0, "q.B" -> 1, "q.B2" -> 1,
                                        "q.Fr" -> 6, "q.Br" -> 12, "q.WF" -> 0, "q.WB" -> 0))
    val counters = new StackPool(c, Vector("q.m.pos" -> 6, "q.m.neg" -> 7,
                                           "q.c.pos" -> 12, "q.c.neg" -> 2))
    val queue = new Queue(cells, counters, "q")
    queue.push(NEW, ingest)
    queue.work()
    val ready = Expr.old(Nil, PREFIX + readyLabel)
    val advance = AND(NOT(ingest), OR(NOT(ready), NOT(queue.empty())))
    val take = AND(advance, ready)
    val offered = queue.pop(take)
    val char = c.get(offered, "buffer.symbol", Vector('a', 'b'), 'a')
    queue.work()
    val (labels, pointers) = substituteSource(source, Map(
      'a' -> AND(take, char.eqTo('a')), 'b' -> AND(take, char.eqTo('b')), '.' -> NOT(take)))
    val complete = AND(advance, labels(eventLabel), queue.empty())
    val previousAnswer = c.get(PREVIOUS, "buffer.answer", Vector(false, true), true).eqTo(true)
    val answer = choose(ingest, FALSE, choose(complete, labels(valueLabel), previousAnswer))
    c.put("buffer.answer", Value.select(answer, Value.constant(true), Value.constant(false)))
    queue.commit()
    // Declare the renamed source fields before validating the combined graph;
    // the queue dispatch and answer expressions already refer to those fields.
    for ((key, value) <- source.initial) {
      c.initial(PREFIX + key) = value
      c.labels(PREFIX + key) = choose(advance, labels(key), Expr.old(Nil, PREFIX + key))
    }
    for ((key, expr) <- pointers) {
      c.pointers(PREFIX + key) = Expr.select(advance, expr, Expr.pointer(Seq(PREFIX + key)))
    }
    val machine = c.machine(answer, initialAccepting = true)
    (c, machine)
  }

  /** Pack one arrival and `service` work transitions of `wrapper` into one round over `ab`. */
  def packService(wrapper: Scaffold, service: Int, lazyRound: Boolean = false): Scaffold = {
    if (service < 1) { throw new IllegalArgumentException("positive finite source service required") }
    if (wrapper.alphabet != "ab.") { throw new IllegalArgumentException("expected a buffered source event alphabet") }
    val arrival: Map[Char, Expr] = Map('a' -> Expr.symbol('a'), 'b' -> Expr.symbol('b'), '.' -> FALSE)
    val work: Map[Char, Expr] = Map('a' -> FALSE, 'b' -> FALSE, '.' -> TRUE)
    val inputs = arrival +: Vector.fill(service)(work)
    val stages = Vector.fill(service + 1)(wrapper)
    if (lazyRound) {
      ScaffoldRoundLazy.packRoundLazy(stages, Some(inputs), Some("ab"))
    } else {
      ScaffoldRound.packRound(stages, Some(inputs), Some("ab"))
    }
  }
}
