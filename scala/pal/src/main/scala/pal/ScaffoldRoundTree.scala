package pal

import scala.collection.mutable

import Expr.{TRUE, FALSE}
import ScaffoldRound.packRound

/** Factor a fixed service round into binary compositions of the same packer.
  *
  * Identity stages complete the binary tree. They do not advance the source or
  * read input. The number of source service transitions remains exactly service.
  *
  * Port of `scaffold_round_tree.py`.
  */
object ScaffoldRoundTree {

  def packServiceTree(wrapper: Scaffold, service: Int): Scaffold = {
    if (service < 1) { throw new IllegalArgumentException("positive finite source service required") }
    if (wrapper.alphabet != "ab.") { throw new IllegalArgumentException("expected a buffered source event alphabet") }
    val (arrival, work) = Expr.share {
      val arrival = packRound(Seq(wrapper), Some(Seq(Map('a' -> Expr.symbol('a'), 'b' -> Expr.symbol('b'), '.' -> FALSE))), Some("ab"))
      val work = packRound(Seq(wrapper), Some(Seq(Map('a' -> FALSE, 'b' -> FALSE, '.' -> TRUE))), Some("ab"))
      (arrival, work)
    }
    val identity = new Scaffold(
      work.initial,
      work.labels.keys.map(key => key -> Expr.old(Nil, key)),
      work.pointers.keys.map(key => key -> Expr.pointer(Seq(key))),
      work.accepting,
      "ab"
    )
    // Python `1 << service.bit_length()`.
    val width = 1 << (32 - Integer.numberOfLeadingZeros(service))
    var layer: Vector[Scaffold] = arrival +: (Vector.fill(service)(work) ++ Vector.fill(width - service - 1)(identity))
    while (layer.length > 1) {
      // Keyed by the identity of the paired stages (Python `tuple(map(id, pair))`;
      // `Scaffold` has reference equality).
      val cache = mutable.HashMap.empty[(Scaffold, Scaffold), Scaffold]
      val next = Vector.newBuilder[Scaffold]
      var index = 0
      while (index < layer.length) {
        val pair = (layer(index), layer(index + 1))
        next += cache.getOrElseUpdate(pair, Expr.share { packRound(Seq(pair._1, pair._2)) })
        index += 2
      }
      layer = next.result()
    }
    layer.head
  }
}
