package pal

import GalilContracts.*

/** Pins `ContractAudit` and the stack decoding of `GalilContracts` with
  * hand-built fake nodes/sources/results: the same scenario is driven through
  * `galil_contracts.py` with equivalent Python fakes (see [[driver]]) and the
  * recorded rows and counts must be identical.
  *
  * The scenario visits every `observe*` path: main (first observation, a
  * replay and a search restart), dp_found, move, replay_start, replay_return,
  * shift, shift_return and three outputs (the timing checks need a previous
  * output).
  */
class GalilContractsAuditSuite extends munit.FunSuite {

  /** A node with fixed labels and pointers; a missing key throws like Python's `KeyError`. */
  final class FakeNode(val t: Int, labels: Map[String, LabelValue], ptrs: Map[String, Option[Node]]) extends Node {
    def label(key: String): LabelValue = labels(key)
    def ptr(key: String): Option[Node] = ptrs(key)
  }

  /** A root with unary stacks: `places` as `(depth, gap)`, `numbers` as
    * `(pos, neg)` depths and plain `depths`. Each stack level names the next
    * creator/slot pair differently, so the key recomputation of `depth` is
    * exercised at every hop.
    */
  def fake(t: Int, labels: Map[String, LabelValue], places: Map[String, (Int, Boolean)] = Map.empty,
           numbers: Map[String, (Int, Int)] = Map.empty, depths: Map[String, Int] = Map.empty): FakeNode = {
    var rootLabels: Map[String, LabelValue] = labels
    var rootPtrs: Map[String, Option[Node]] = Map.empty
    def stack(name: String, depth: Int): Unit = {
      rootLabels = rootLabels.updated(name + ".tname", name + "c0").updated(name + ".tslot", 0)
      var node: Option[Node] = None
      (depth - 1 to 0 by -1).foreach { i =>
        val key = s"${name}c$i.$i."
        val hop: Map[String, LabelValue] = Map(key + "bname" -> s"${name}c${i + 1}", key + "bslot" -> (i + 1))
        node = Some(new FakeNode(-1, hop, Map(key + "below" -> node)))
      }
      rootPtrs = rootPtrs.updated(name + ".top", node)
    }
    places.foreach { case (name, (depth, gap)) =>
      stack(name + ".l", depth)
      rootLabels = rootLabels.updated(name + ".gap", gap)
    }
    numbers.foreach { case (name, (pos, neg)) =>
      stack(name + ".pos", pos)
      stack(name + ".neg", neg)
    }
    depths.foreach { case (name, depth) => stack(name, depth) }
    new FakeNode(t, rootLabels, rootPtrs)
  }

  object FakeTiming extends Timing {
    val moveSlope: Int = 2
    val intervalOverhead: Int = 3
    val predictability: Int = 4
  }

  final class FakeSource(val top: Node) extends Source {
    def timing: Timing = FakeTiming
  }

  final case class FakeResult(output: Option[Int] = None, replays: Int = 0, restarts: Int = 0, shifts: Int = 0)
    extends StepResult {
    def inputReady: Boolean = true
    def events: Map[String, Int] = Map("fpp_calls" -> 0, "chain_shifts" -> shifts, "search_restarts" -> restarts, "replays" -> replays)
  }

  val scan: Map[String, LabelValue] = Map("g.mode" -> "scan", "sp.mode" -> "search", "g.replaying" -> false)

  /** `(word, root, result)` per observation; mirrors `steps` in [[driver]]. */
  lazy val steps: Vector[(String, FakeNode, FakeResult)] = Vector(
    ("aabaa", fake(10, scan, Map("C" -> (3, false), "R" -> (4, false), "L" -> (2, false)),
      Map("sp.lo" -> (2, 0), "g.rad" -> (3, 1))), FakeResult()),
    ("ababa", fake(11, scan.updated("sp.mode", "found"), Map("C" -> (5, false), "R" -> (5, true)),
      Map("sp.lo" -> (1, 1)), Map("dp.t11.l" -> 2)), FakeResult()),
    ("aabaa", fake(12, scan.updated("g.mode", "copy"), Map("C" -> (3, false), "R" -> (4, true), "L" -> (1, true)),
      Map("g.rad" -> (3, 0), "g.rem" -> (6, 0))), FakeResult()),
    ("aabaa", fake(13, scan.updated("g.replaying", true), Map("C" -> (4, false), "R" -> (4, false), "L" -> (4, false)),
      Map("sp.lo" -> (0, 0), "g.rad" -> (2, 2), "g.replay" -> (1, 0))), FakeResult(replays = 1)),
    ("aabaa", fake(14, scan, Map("C" -> (4, false), "R" -> (4, true), "L" -> (3, true)),
      Map("g.rad" -> (1, 0), "g.len" -> (3, 0), "g.replay" -> (2, 2))), FakeResult()),
    ("ababa", fake(15, scan.updated("g.mode", "shift").updated("ch.phase", 4),
      Map("C" -> (3, false), "R" -> (5, false), "L" -> (1, false)),
      Map("ch.h" -> (2, 0), "g.rem" -> (2, 0), "ch.lag" -> (1, 1))), FakeResult(shifts = 1)),
    ("ababa", fake(16, scan, Map("C" -> (4, false), "R" -> (5, false), "L" -> (3, false)),
      Map("g.rad" -> (2, 0), "g.len" -> (5, 0), "ch.cycle" -> (4, 0))), FakeResult()),
    ("ababa", fake(17, scan, Map("C" -> (3, false))), FakeResult(output = Some(1))),
    ("ababab", fake(24, scan, Map("C" -> (4, true))), FakeResult(output = Some(0))),
    ("ababababa", fake(27, scan, Map("C" -> (5, false))), FakeResult(output = Some(1))),
    ("aabaa", fake(28, scan, Map("C" -> (3, false), "R" -> (4, false), "L" -> (2, false)),
      Map("sp.lo" -> (2, 0), "g.rad" -> (3, 1))), FakeResult(restarts = 1))
  )

  /** The Python side of the comparison: the same fakes and steps, printing the
    * decoded coordinates of the first root, every recorded row and the counts.
    */
  val driver: String = """
from galil_contracts import ContractAudit, depth, number, place

class Node:
  def __init__(self, t, label, ptr):
    self.t, self.label, self.ptr = t, label, ptr

class Fake(Node):
  def __init__(self, t, labels, places={}, numbers={}, depths={}):
    super().__init__(t, dict(labels), {})
    for name, (d, gap) in places.items():
      self.stack(name + ".l", d)
      self.label[name + ".gap"] = gap
    for name, (pos, neg) in numbers.items():
      self.stack(name + ".pos", pos)
      self.stack(name + ".neg", neg)
    for name, d in depths.items():
      self.stack(name, d)

  def stack(self, name, d):
    self.label[name + ".tname"], self.label[name + ".tslot"] = name + "c0", 0
    node = None
    for i in reversed(range(d)):
      key = f"{name}c{i}.{i}."
      node = Node(-1, {key + "bname": f"{name}c{i + 1}", key + "bslot": i + 1}, {key + "below": node})
    self.ptr[name + ".top"] = node

class Timing:
  move_slope, interval_overhead, predictability = 2, 3, 4

class Source:
  def __init__(self, root):
    self.vm = type("VM", (), {"top": root})()
    self.timing = Timing()

class Result:
  def __init__(self, output=None, replays=0, restarts=0, shifts=0):
    self.output, self.input_ready = output, True
    self.events = {"fpp_calls": 0, "chain_shifts": shifts, "search_restarts": restarts, "replays": replays}

scan = {"g.mode": "scan", "sp.mode": "search", "g.replaying": False}
steps = [
  ("aabaa", Fake(10, scan, {"C": (3, False), "R": (4, False), "L": (2, False)},
                 {"sp.lo": (2, 0), "g.rad": (3, 1)}), Result()),
  ("ababa", Fake(11, {**scan, "sp.mode": "found"}, {"C": (5, False), "R": (5, True)},
                 {"sp.lo": (1, 1)}, {"dp.t11.l": 2}), Result()),
  ("aabaa", Fake(12, {**scan, "g.mode": "copy"}, {"C": (3, False), "R": (4, True), "L": (1, True)},
                 {"g.rad": (3, 0), "g.rem": (6, 0)}), Result()),
  ("aabaa", Fake(13, {**scan, "g.replaying": True}, {"C": (4, False), "R": (4, False), "L": (4, False)},
                 {"sp.lo": (0, 0), "g.rad": (2, 2), "g.replay": (1, 0)}), Result(replays=1)),
  ("aabaa", Fake(14, scan, {"C": (4, False), "R": (4, True), "L": (3, True)},
                 {"g.rad": (1, 0), "g.len": (3, 0), "g.replay": (2, 2)}), Result()),
  ("ababa", Fake(15, {**scan, "g.mode": "shift", "ch.phase": 4}, {"C": (3, False), "R": (5, False), "L": (1, False)},
                 {"ch.h": (2, 0), "g.rem": (2, 0), "ch.lag": (1, 1)}), Result(shifts=1)),
  ("ababa", Fake(16, scan, {"C": (4, False), "R": (5, False), "L": (3, False)},
                 {"g.rad": (2, 0), "g.len": (5, 0), "ch.cycle": (4, 0)}), Result()),
  ("ababa", Fake(17, scan, {"C": (3, False)}), Result(output=1)),
  ("ababab", Fake(24, scan, {"C": (4, True)}), Result(output=0)),
  ("ababababa", Fake(27, scan, {"C": (5, False)}), Result(output=1)),
  ("aabaa", Fake(28, scan, {"C": (3, False), "R": (4, False), "L": (2, False)},
                 {"sp.lo": (2, 0), "g.rad": (3, 1)}), Result(restarts=1)),
]
root = steps[0][1]
print("decode", depth(root, "C.l"), number(root, "sp.lo"), number(root, "g.rad"), place(root, "C"), place(root, "R"), place(root, "L"))
audit = ContractAudit()
for word, root, result in steps:
  audit.observe(Source(root), word, result)
for row in audit.rows:
  print(row["event"], "t=" + str(row["tick"]), " ".join(f"{k}={v}" for k, v in row.items() if k not in ("event", "tick")))
print("counts", " ".join(f"{k}={v}" for k, v in audit.counts.items()))
"""

  def render(audit: ContractAudit): Vector[String] = {
    audit.rows.toVector.map(row => s"${row.event} t=${row.tick} " + row.values.map { case (k, v) => s"$k=$v" }.mkString(" ")) :+
      ("counts " + audit.counts.map { case (k, v) => s"$k=$v" }.mkString(" "))
  }

  test("decoded coordinates, audit rows and counts are identical to galil_contracts.py") {
    val root = steps(0)._2
    val decode = "decode " + Vector(depth(root, "C.l"), number(root, "sp.lo"), number(root, "g.rad"),
      place(root, "C"), place(root, "R"), place(root, "L")).mkString(" ")
    val audit = new ContractAudit
    steps.foreach { case (word, root, result) => audit.observe(new FakeSource(root), word, result) }
    val actual = (decode +: render(audit)).mkString("", "\n", "\n")
    PyDiff.assertSameAsPython(actual, "-c", driver)
    assertEquals(audit.counts.keys.toVector,
      Vector("main", "dp_found", "move", "replay_start", "replay_return", "shift", "shift_return", "output"))
    assertEquals(audit.rows.size, 12)
  }

  test("stack decoding: depth, number and place") {
    val root = fake(0, Map.empty, Map("X" -> (4, true), "Y" -> (4, false), "Z" -> (0, false)),
      Map("N" -> (5, 2)), Map("D" -> 3))
    assertEquals(depth(root, "D"), 3)
    assertEquals(depth(root, "Z.l"), 0)
    assertEquals(number(root, "N"), 3)
    assertEquals(place(root, "X"), 8)
    assertEquals(place(root, "Y"), 7)
    assertEquals(place(root, "Z"), -1)
    intercept[NoSuchElementException](depth(root, "missing"))
  }

  test("every contract violation is an AssertionError") {
    def observing(word: String, root: FakeNode, result: FakeResult, previous: Vector[(String, FakeNode, FakeResult)] = Vector.empty): Unit = {
      val audit = new ContractAudit
      previous.foreach { case (w, r, res) => audit.observe(new FakeSource(r), w, res) }
      audit.observe(new FakeSource(root), word, result)
    }
    // main: 3 * (R - C) <= 5 * lower fails with lower = 0.
    intercept[AssertionError](observing("aabaa", fake(10, scan, Map("C" -> (3, false), "R" -> (4, false), "L" -> (2, false)),
      Map("sp.lo" -> (0, 0), "g.rad" -> (3, 1))), FakeResult()))
    // main: the interval L..R (odd cells a a b a b) must be a palindrome.
    intercept[AssertionError](observing("aabab", fake(10, scan, Map("C" -> (3, false), "R" -> (5, false), "L" -> (1, false)),
      Map("sp.lo" -> (4, 0), "g.rad" -> (4, 0))), FakeResult()))
    // replay_start without a recorded move.
    intercept[AssertionError](observing("aabaa", steps(3)._2, FakeResult(replays = 1), steps.take(1)))
    // dp_found: h must be the least candidate (2 here).
    intercept[AssertionError](observing("ababa", fake(11, scan.updated("sp.mode", "found"),
      Map("C" -> (5, false), "R" -> (5, true)), Map("sp.lo" -> (1, 1)), Map("dp.t11.l" -> 1)), FakeResult(), steps.take(1)))
    // output: the answer must agree with the word.
    intercept[AssertionError](observing("ababa", fake(17, scan, Map("C" -> (3, false))), FakeResult(output = Some(0)), steps.take(1)))
    // output: a positive answer later than predictability ticks after the previous one.
    intercept[AssertionError](observing("ababababa", fake(40, scan, Map("C" -> (5, false))), FakeResult(output = Some(1)), steps.take(9)))
  }
}
