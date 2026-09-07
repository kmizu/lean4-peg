package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Expr.{TRUE, FALSE}

/** Order/equality of finitely many heads by maintained signed differences.
  *
  * This does not compare SCA pointers. The controller must apply the same moves
  * and copies to its actual heads. It cannot load an arbitrary historical head
  * and infer that head's distances to the current bank.
  *
  * Port of `scaffold_head_distances.py`. `moves` gives each head its
  * (left, right) construction counts; by default one move each way.
  */
final class HeadDistances(
    circuit: Circuit,
    nameSeq: Seq[String],
    moves: Option[collection.Map[String, (Int, Int)]] = None,
    prefix: String = "head.distance",
    val exclusiveMoves: Boolean = false
) {
  val names: Vector[String] = nameSeq.toVector
  if (names.length < 2 || names.distinct.length != names.length) {
    throw new IllegalArgumentException("at least two distinct fixed head names required")
  }
  val index: Map[String, Int] = names.zipWithIndex.toMap

  private val counts: collection.Map[String, (Int, Int)] = moves.getOrElse(names.map(name => name -> (1, 1)).toMap)
  if (counts.keySet != names.toSet || counts.values.exists { case (left, right) => left < 0 || right < 0 }) {
    throw new IllegalArgumentException("each head needs nonnegative (left, right) construction counts")
  }

  private val layoutBuilder = mutable.LinkedHashMap.empty[String, Int]
  private val keyBuilder = mutable.LinkedHashMap.empty[(String, String), String]
  for ((left, i) <- names.zipWithIndex; right <- names.drop(i + 1)) {
    val key = s"$prefix.$left.$right"
    keyBuilder((left, right)) = key
    layoutBuilder(key + ".pos") = counts(left)._2 + counts(right)._1
    layoutBuilder(key + ".neg") = counts(left)._1 + counts(right)._2
  }

  /** Cell layout: `<pair key>.pos`/`.neg` -> slot count. */
  val layout: VectorMap[String, Int] = VectorMap.from(layoutBuilder)

  /** Ordered head pair -> its counter name. */
  val keys: VectorMap[(String, String), String] = VectorMap.from(keyBuilder)
  if (!layout.values.exists(_ != 0)) {
    throw new IllegalArgumentException("the bank requires at least one declared movement")
  }

  // With at most one moving head per physical step, its differences to
  // each other head need one cell apiece. Both signs and all possible
  // moving heads may share those H slots under disjoint instruction guards.
  val pool: StackPool = new StackPool(circuit, if (exclusiveMoves) { Vector("cells" -> names.length) } else { layout })

  /** Ordered head pair -> signed distance counter (`left - right` is its sign). */
  val counters: VectorMap[(String, String), Counter] = keys.map { case (pair, key) =>
    pair -> new Counter(pool, key, if (exclusiveMoves) { Some("cells") } else { None })
  }

  private def ordered(left: String, right: String): (String, String) = {
    if (!index.contains(left) || !index.contains(right)) { throw new IllegalArgumentException("unknown head") }
    if (index(left) < index(right)) { (left, right) } else { (right, left) }
  }

  def equal(left: String, right: String): Expr = {
    val pair = ordered(left, right)
    if (left == right) { TRUE } else { counters(pair).zero() }
  }

  def less(left: String, right: String): Expr = {
    val pair = ordered(left, right)
    if (left == right) {
      FALSE
    } else {
      val counter = counters(pair)
      if (pair._1 == left) { counter.negative() } else { counter.positive() }
    }
  }

  def move(head: String, direction: Int, enabled: Expr = TRUE): Unit = {
    if (!index.contains(head) || (direction != -1 && direction != 1)) {
      throw new IllegalArgumentException("known head and unit direction required")
    }
    for ((pair, counter) <- counters if pair._1 == head || pair._2 == head) {
      val change = if (pair._1 == head) { direction } else { -direction }
      val other = if (pair._1 == head) { pair._2 } else { pair._1 }
      val slot = if (exclusiveMoves) { Some(index(other)) } else { None }
      if (change == 1) { counter.inc(enabled, slot) } else { counter.dec(enabled, slot) }
    }
  }

  def copy(target: String, source: String, enabled: Expr = TRUE): Unit = {
    ordered(target, source)
    if (target != source) {
      for ((pair, counter) <- counters if pair._1 == target || pair._2 == target) {
        val left = if (pair._1 == target) { source } else { pair._1 }
        val right = if (pair._2 == target) { source } else { pair._2 }
        if (left == right) {
          counter.reset(enabled)
        } else {
          val sourcePair = ordered(left, right)
          val original = counters(sourcePair)
          val (positive, negative) = if (sourcePair._1 == left) { (original.positiveStack, original.negativeStack) } else { (original.negativeStack, original.positiveStack) }
          // Source pairs exclude target, so these updates cannot overwrite a
          // distance subsequently needed by this same head-copy operation.
          counter.positiveStack.copyFrom(positive, enabled)
          counter.negativeStack.copyFrom(negative, enabled)
        }
      }
    }
  }

  /** Reset after the associated controller has placed all heads together. */
  def coincide(enabled: Expr = TRUE): Unit = {
    for (counter <- counters.values) { counter.reset(enabled) }
  }

  /** Python `finalize()`. */
  def commit(): Unit = {
    for (counter <- counters.values) { counter.commit() }
  }
}
