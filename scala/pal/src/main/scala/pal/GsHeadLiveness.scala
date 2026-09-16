package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** Result of [[GsHeadLiveness.analyze]]: live head-difference pairs before and
  * after every instruction, plus a register (color) for each pair.
  */
final case class Liveness(names: Vector[String], before: Vector[Set[(String, String)]],
                          after: Vector[Set[(String, String)]], colors: VectorMap[(String, String), Int]) {
  def registers: Int = colors.values.maxOption.getOrElse(-1) + 1

  /** The canonical ordered pair of two heads and the sign of `left - right`
    * relative to it; `(None, 1)` for a head against itself.
    */
  def canonical(left: String, right: String): (Option[(String, String)], Int) = {
    if (left == right) {
      (None, 1)
    } else if (names.indexOf(left) < names.indexOf(right)) {
      (Some((left, right)), 1)
    } else {
      (Some((right, left)), -1)
    }
  }
}

/** Result of [[GsHeadLiveness.analyzeReaders]]: live symbol-reading heads. */
final case class ReaderLiveness(before: Vector[Set[String]], after: Vector[Set[String]],
                                colors: VectorMap[String, Int]) {
  def registers: Int = colors.values.maxOption.getOrElse(-1) + 1
}

/** Exact backward liveness for the finite program's head differences.
  *
  * Only differences needed by a subsequent test/output are retained. Copying a
  * head substitutes its source in those future differences. No input traces or
  * numeric positions participate in this analysis.
  *
  * Port of `gs_head_liveness.py`.
  */
object GsHeadLiveness {
  import Event.*

  type Pair = (String, String)

  /** Greedy interference-graph coloring: repeatedly pick the uncolored node that
    * maximizes `key` (Python's `max`, first maximum on ties, though the keys are
    * distinct here) and give it the smallest color unused by its neighbors.
    */
  private def color[N, K: Ordering](graph: VectorMap[N, Set[N]], key: (N, Int) => K): VectorMap[N, Int] = {
    var colors = VectorMap.empty[N, Int]
    while (colors.size != graph.size) {
      def colored(node: N): Set[Int] = graph(node).flatMap(colors.get)
      val chosen = graph.keys.filterNot(colors.contains).maxBy(node => key(node, colored(node).size))
      val occupied = colored(chosen)
      val fresh = Iterator.from(0).find(c => !occupied.contains(c)).get
      colors = colors.updated(chosen, fresh)
    }
    colors
  }

  private def interferenceGraph[N](sets: Iterable[Set[N]], nodes: Iterable[Set[N]]): VectorMap[N, Set[N]] = {
    val graph = mutable.LinkedHashMap.empty[N, mutable.Set[N]]
    nodes.foreach(live => live.foreach(node => graph.getOrElseUpdate(node, mutable.LinkedHashSet.empty)))
    // The union of successors matters at branching instructions: simultaneous
    // counter updates must not alias values needed by either successor.
    sets.foreach(live => live.foreach(node => graph(node) ++= (live - node)))
    VectorMap.from(graph.view.mapValues(_.toSet))
  }

  private def successorsUnion[N](before: Int => Set[N], targets: Vector[Int]): Set[N] = {
    targets.foldLeft(Set.empty[N])((live, target) => live ++ before(target))
  }

  def analyze(program: Program, names: Vector[String] = GsHeads.HEADS, observePositions: Boolean = true,
              availabilityDistance: Boolean = true): Liveness = {
    val rank = names.zipWithIndex.toMap
    if (rank.size != names.size) {
      throw new IllegalArgumentException("distinct head names required")
    }

    def pair(left: String, right: String): Option[Pair] = {
      if (!rank.contains(left) || !rank.contains(right)) {
        throw new IllegalArgumentException("unknown head in finite program")
      }
      if (left == right) {
        None
      } else if (rank(left) < rank(right)) {
        Some((left, right))
      } else {
        Some((right, left))
      }
    }

    def liveBefore(row: Row, successors: Set[Pair]): Set[Pair] = {
      val substituted = row.event match {
        case Copy(target, source) =>
          successors.flatMap { case (left, right) =>
            pair(if (left == target) source else left, if (right == target) source else right)
          }
        case _ => successors
      }
      row.event match {
        case Less(left, right) => substituted ++ pair(left, right)
        case Equal(left, right) => substituted ++ pair(left, right)
        case AssertEqual(left, right) => substituted ++ pair(left, right)
        case Border(head) if observePositions => substituted ++ pair("Origin", head)
        case Match(head) if observePositions => substituted ++ pair("Origin", head)
        case Available(head) if availabilityDistance => substituted ++ pair(head, "OriginalEnd")
        case _ => substituted
      }
    }

    val before = fixpoint(program, liveBefore)
    val after = program.code.map(row => successorsUnion(before, row.targets))
    val graph = interferenceGraph(before ++ after, before)
    val colors = color[Pair, (Int, Int, Int, Int)](graph, (p, colored) => (colored, graph(p).size, rank(p._1), rank(p._2)))
    Liveness(names, before, after, colors)
  }

  /** Iterate the backward dataflow equations to a fixpoint, visiting the states
    * in reverse order as the Python original does.
    */
  private def fixpoint[N](program: Program, transfer: (Row, Set[N]) => Set[N]): Vector[Set[N]] = {
    val before = Array.fill(program.code.size)(Set.empty[N])
    var changed = true
    while (changed) {
      changed = false
      (program.code.size - 1 to 0 by -1).foreach { state =>
        val row = program.code(state)
        val live = transfer(row, successorsUnion(before, row.targets))
        if (live != before(state)) {
          before(state) = live
          changed = true
        }
      }
    }
    before.toVector
  }

  /** Liveness of the symbol-reading heads: which heads may still read a symbol
    * later, and a register for each.
    */
  def analyzeReaders(program: Program): ReaderLiveness = {
    def liveBefore(row: Row, successors: Set[String]): Set[String] = {
      val substituted = row.event match {
        case Copy(target, source) if successors.contains(target) => successors - target + source
        case _ => successors
      }
      row.event match {
        case Symbols(left, right) => substituted + left + right
        case Available(head) => substituted + head
        case _ => substituted
      }
    }

    val before = fixpoint(program, liveBefore)
    val after = program.code.map(row => successorsUnion(before, row.targets))
    val graph = interferenceGraph(before ++ after, before)
    val colors = color[String, (Int, Int, String)](graph, (head, colored) => (colored, graph(head).size, head))
    ReaderLiveness(before, after, colors)
  }
}
