package pal

import scala.collection.mutable

import Expr.{TRUE, FALSE, SELF, NULL}
import ScaffoldCircuit.{neg, conjunction, disjunction, choosePointer}

/** Constant-field propagation and query closure for finite scaffold equations.
  *
  * A label is folded only when its sentinel value and every transition agree.
  * A null pointer field is null at the sentinel and on every transition. These
  * facts are closed to a fixed point; input samples do not participate.
  *
  * Port of `scaffold_optimize.py`.
  */
object ScaffoldOptimize {
  import Expr.*

  /** The Python `stats` dictionary returned next to the reduced machine. */
  final case class OptimizeStats(
      rounds: Int,
      constantLabels: Int,
      nullPointers: Int,
      labelsRemoved: Int,
      pointersRemoved: Int
  )

  /** Direct sub-expressions: the computed pointer of a read/edge, else every argument. */
  def children(expression: Expr): Vector[Expr] = {
    expression match {
      case Read(target, _) => Vector(target)
      case Edge(target, _) => Vector(target)
      case Not(value) => Vector(value)
      case Present(target) => Vector(target)
      case And(values) => values
      case Or(values) => values
      case Select(condition, yes, no) => Vector(condition, yes, no)
      case _ => Vector.empty
    }
  }

  private sealed trait Work
  private final case class LabelWork(key: String) extends Work
  private final case class PointerWork(key: String) extends Work
  private final case class ExprWork(expr: Expr) extends Work

  /** Keep only the labels and pointer fields reachable from `roots` (label names). */
  def project(
      initial: collection.Map[String, Boolean],
      labels: collection.Map[String, Expr],
      pointers: collection.Map[String, Expr],
      roots: Seq[String],
      accepting: String,
      alphabet: String
  ): Scaffold = {
    val liveLabels = mutable.HashSet.empty[String]
    val livePointers = mutable.HashSet.empty[String]
    // Python keyed this scratch set by `id(item)`; identity is what it means here.
    val seen = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Expr, java.lang.Boolean]())
    val work = mutable.Stack[Work](roots.map(LabelWork(_))*)
    while (work.nonEmpty) {
      work.pop() match {
        case LabelWork(key) =>
          if (liveLabels.add(key)) { work.push(ExprWork(labels(key))) }
        case PointerWork(key) =>
          if (livePointers.add(key)) { work.push(ExprWork(pointers(key))) }
        case ExprWork(item) =>
          if (seen.add(item)) {
            item match {
              case Old(path, label) =>
                path.foreach(key => work.push(PointerWork(key)))
                work.push(LabelWork(label))
              case Exists(path) => path.foreach(key => work.push(PointerWork(key)))
              case Pointer(path) => path.foreach(key => work.push(PointerWork(key)))
              case Read(_, label) => work.push(LabelWork(label))
              case Edge(_, field) => work.push(PointerWork(field))
              case _ => ()
            }
            children(item).foreach(child => work.push(ExprWork(child)))
          }
      }
    }
    // Validation below traverses the live DAG again. Its own visited sets do
    // not need to coexist with this complete reachability scratch set.
    seen.clear()
    new Scaffold(
      initial.filter { case (key, _) => liveLabels.contains(key) },
      labels.filter { case (key, _) => liveLabels.contains(key) },
      pointers.filter { case (key, _) => livePointers.contains(key) },
      accepting,
      alphabet
    )
  }

  /** Fold constant labels and null pointers to a fixed point, then project onto `roots`. */
  def optimize(machine: Scaffold, roots: Seq[String] = Nil): (Scaffold, OptimizeStats) = {
    var labels: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.from(machine.labels)
    var pointers: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.from(machine.pointers)
    var constants: mutable.LinkedHashMap[String, Expr] = mutable.LinkedHashMap.empty
    var nulls: Set[String] = Set.empty
    var rounds = 0
    var converged = false
    while (!converged) {
      val newConstants = labels.filter { case (key, expression) =>
        expression == (if (machine.initial(key)) { TRUE } else { FALSE })
      }
      val newNulls = pointers.collect { case (key, expression) if expression == NULL => key }.toSet
      if (rounds > 0 && newConstants == constants && newNulls == nulls) {
        converged = true
      } else {
        constants = newConstants
        nulls = newNulls
        val rewriter = new ConstantRewriter(constants, nulls)
        labels = labels.map { case (key, expression) => key -> rewriter.rewrite(expression) }
        pointers = pointers.map { case (key, expression) => key -> rewriter.rewrite(expression) }
        rounds += 1
      }
    }
    // Rewritten roots own every expression that remains live. Retaining the
    // old-id -> new-expression table through projection and validation can
    // otherwise multiply peak memory for a large, fixed transition circuit.
    // (The rewriter and its memo are unreachable from here on.)
    val reduced = project(machine.initial, labels, pointers, machine.accepting +: roots, machine.accepting, machine.alphabet)
    val stats = OptimizeStats(
      rounds = rounds,
      constantLabels = constants.size,
      nullPointers = nulls.size,
      labelsRemoved = labels.size - reduced.labels.size,
      pointersRemoved = pointers.size - reduced.pointers.size
    )
    (reduced, stats)
  }

  /** One round of bottom-up rewriting under the current constant/null facts. */
  private final class ConstantRewriter(constants: collection.Map[String, Expr], nulls: Set[String]) {

    /** Python `memo[id(expr)]`: rewritten node per original node identity. */
    private val memo = new java.util.IdentityHashMap[Expr, Expr]()

    private def has(target: Expr): Expr = {
      if (target == NULL) {
        FALSE
      } else if (target == SELF || target == Expr.pointer(Nil)) {
        TRUE
      } else {
        Expr.present(target)
      }
    }

    private def path(fields: Vector[String]): Expr = {
      if (fields.exists(nulls.contains)) { NULL } else { Expr.pointer(fields) }
    }

    private def get(target: Expr, key: String): Expr = {
      if (target == NULL || constants.get(key).contains(FALSE)) {
        FALSE
      } else if (constants.get(key).contains(TRUE)) {
        has(target)
      } else {
        target match {
          case Pointer(fields) => Expr.old(fields, key)
          case _ => Expr.read(target, key)
        }
      }
    }

    def rewrite(expression: Expr): Expr = {
      val work = mutable.Stack[(Expr, Boolean)]((expression, false))
      while (work.nonEmpty) {
        val (current, done) = work.pop()
        if (!memo.containsKey(current)) {
          if (!done) {
            work.push((current, true))
            children(current).foreach(child => work.push((child, false)))
          } else {
            val result = fold(current)
            memo.put(current, if (result == current) { current } else { result })
          }
        }
      }
      memo.get(expression)
    }

    /** Rebuild `current` from its already rewritten children. */
    private def fold(current: Expr): Expr = {
      current match {
        case Old(fields, label) => get(path(fields), label)
        case Exists(fields) => has(path(fields))
        case Pointer(fields) => path(fields)
        case Read(target, label) => get(memo.get(target), label)
        case Edge(target, field) =>
          val rewrittenTarget = memo.get(target)
          if (rewrittenTarget == NULL || nulls.contains(field)) { NULL } else { Expr.edge(rewrittenTarget, field) }
        case Present(target) => has(memo.get(target))
        case Not(value) => neg(memo.get(value))
        case And(values) => conjunction(values.map(memo.get)*)
        case Or(values) => disjunction(values.map(memo.get)*)
        case Select(condition, yes, no) => choosePointer(memo.get(condition), memo.get(yes), memo.get(no))
        case _ => current
      }
    }
  }
}
