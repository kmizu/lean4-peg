package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import Expr.TRUE
import ScaffoldCircuit.neg
import Ref.{NEW, PREVIOUS}

/** Fixed ordinary PEG rules that consume floor(n/2) or ceil(n/2) symbols.
  *
  * The source enqueues each input-node address and dequeues one on every second
  * arrival. Its focus therefore names node floor(n/2), including the sentinel.
  * Scaffold-to-PEG reversal makes that pointer consume n-floor(n/2) characters.
  * This constructs a midpoint component, not a palindrome recognizer.
  *
  * Port of `midpoint_peg.py`; `main OUTPUT` regenerates `generated/midpoint.peg`.
  */
object MidpointPeg {

  def build(): (Circuit, Scaffold) = {
    val c = new Circuit("ab")
    val cells = new StackPool(c, Vector("q.F" -> 0, "q.B" -> 1, "q.B2" -> 1, "q.Fr" -> 3,
                                        "q.Br" -> 6, "q.WF" -> 0, "q.WB" -> 0))
    val counters = new StackPool(c, Vector("q.m.pos" -> 3, "q.m.neg" -> 4,
                                           "q.c.pos" -> 6, "q.c.neg" -> 2))
    val queue = new Queue(cells, counters, "q")
    val first = c.get(PREVIOUS, "first", Vector(false, true), true).eqTo(true)
    val odd = c.get(PREVIOUS, "odd", Vector(false, true), false).eqTo(true)
    var focus = Ref.select(first, PREVIOUS, c.getRef(PREVIOUS, "half"))
    queue.push(NEW)
    // Three rotation units run before the optional pop. At rotation start,
    // rear <= front+2; reverse/switch/copy require <=2*front+3 units. Before
    // a (front+1)-st pop could need the new front, 3*(front+1) units are served.
    // See MIDPOINT.md for the queue and pointer invariants.
    queue.work()
    val offered = queue.pop(odd)
    focus = Ref.select(odd, offered, focus)
    queue.commit()
    c.put("first", Value.constant(false))
    c.put("odd", Value.select(neg(odd), Value.constant(true), Value.constant(false)))
    c.putRef("half", focus)
    // The offered front is node ceil(n/2), whether or not this arrival pops it.
    c.putRef("upper_half", offered)
    (c, c.machine(TRUE, initialAccepting = true))
  }

  def grammar(): String = {
    val projected = Expr.share {
      val (_, machine) = build()
      // Keep precisely the equations needed by the returned pointer. The full
      // machine above retains its fault monitor for independent state checks.
      val root = "midpoint.present"
      val observed = new Scaffold(machine.initial + (root -> false),
                                  machine.labels + (root -> Expr.present(Expr.pointer(Seq("half")))),
                                  machine.pointers, root, machine.alphabet)
      val other = "midpoint.upper.present"
      val both = new Scaffold(observed.initial + (other -> false),
                              observed.labels + (other -> Expr.present(Expr.pointer(Seq("upper_half")))),
                              observed.pointers, root, observed.alphabet)
      ScaffoldOptimize.optimize(both, roots = Seq(other))._1
    }
    val half = s"P_${projected.pointers.keys.toVector.indexOf("half")}"
    val upper = s"P_${projected.pointers.keys.toVector.indexOf("upper_half")}"
    val rules = projected.iterRules().toVector
    // H's contract is for a binary suffix. S is only a standalone full-input
    // wrapper; it accepts all binary strings, not PAL.
    val edited = rules.updated(0, "S = H (\"a\" / \"b\")* !.;") ++
      Vector(s"HalfCeil = !. / $half;", s"HalfFloor = !. / $upper;", "H = HalfCeil;")
    edited.mkString("", "\n", "\n")
  }

  /** Python `json.dumps` of a string (ASCII-only output). */
  private[pal] def jsonString(text: String): String = {
    val out = new StringBuilder("\"")
    for (c <- text) {
      c match {
        case '"' => out.append("\\\"")
        case '\\' => out.append("\\\\")
        case '\n' => out.append("\\n")
        case '\r' => out.append("\\r")
        case '\t' => out.append("\\t")
        case '\b' => out.append("\\b")
        case '\f' => out.append("\\f")
        case other if other < 0x20 || other > 0x7e => out.append(f"\\u${other.toInt}%04x")
        case other => out.append(other)
      }
    }
    out.append('"').toString
  }

  /** The JSON summary printed by the Python `main()`. */
  def summary(output: String, source: String): String = {
    val rules = source.count(_ == ';')
    val bytes = source.getBytes(StandardCharsets.UTF_8).length
    s"""{"output": ${jsonString(output)}, "rules": $rules, "bytes": $bytes, "palindrome_recognizer": false}"""
  }

  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      System.err.println("usage: MidpointPeg OUTPUT")
      sys.exit(2)
    }
    val source = grammar()
    Files.write(Paths.get(args(0)), source.getBytes(StandardCharsets.UTF_8))
    println(summary(args(0), source))
  }
}
