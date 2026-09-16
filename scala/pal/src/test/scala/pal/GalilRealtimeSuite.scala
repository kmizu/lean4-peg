package pal

import ScaffoldGalil.{Events, OnlineSource, OnlineStep}
import GalilRealtime.{BufferedSource, RealtimeGalil}

/** Port of `test_galil_realtime.py`: FIFO deadline and source event tests,
  * including postponed negatives. The buffered controller is also driven in Python
  * on the same words and its answers and counters compared line by line.
  */
class GalilRealtimeSuite extends munit.FunSuite {
  import ScaffoldGalilFixture.prefixAnswers

  // drives the whole online controller on 36 words; the differential test also waits for python3
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  /** Test source with explicit read, emit and post-output preparation.
    *
    * Each script entry is `(remaining, answer, after)`: the number of transitions
    * until the answer is emitted, and the number of preparation transitions needed
    * after it before the next read.
    */
  private final class ScriptedSource(script: Seq[(Int, Int, Int)]) extends OnlineSource {
    private val entries = script.iterator
    var inputReady: Boolean = true
    private var preparation = 0
    private var remaining = 0
    private var answer = 0
    private var after = 0

    def read(char: String): OnlineStep = {
      assert(inputReady)
      val (r, a, p) = entries.next()
      remaining = r
      answer = a
      after = p
      inputReady = false
      work()
    }

    def work(): OnlineStep = {
      assert(!inputReady)
      var output: Option[Int] = None
      if (preparation != 0) {
        preparation -= 1
        inputReady = preparation == 0
      } else {
        remaining -= 1
        if (remaining == 0) {
          output = Some(answer)
          preparation = after
          inputReady = preparation == 0
        }
      }
      OnlineStep(output, inputReady, Events())
    }
  }

  test("fifo may postpone negative answers without missing positive") {
    // c=3, k=(0,2,1,0,0), d=(1,10,2,1,1) meet the predictability
    // inequalities. The second output is unavailable at its own deadline.
    val source = new ScriptedSource(Seq((1, 1, 0), (10, 0, 0), (2, 0, 0), (1, 0, 0), (1, 1, 0)))
    val machine = new BufferedSource(source, 6)
    val observed = Vector.newBuilder[Int]
    val completed = Vector.newBuilder[Boolean]
    for (char <- "ababa") {
      observed += machine.read(char.toString)
      completed += machine.lastCompleted
    }
    assertEquals(observed.result(), Vector(1, 0, 0, 0, 1))
    assert(!completed.result()(1))
    assertEquals(machine.outputs, 5)
  }

  test("completed answer survives post-output preparation") {
    val source = new ScriptedSource(Seq((1, 1, 3), (1, 0, 0)))
    val machine = new BufferedSource(source, 2)
    assertEquals(machine.read("a"), 1)
    assert(machine.lastCompleted)
    assert(!source.inputReady)
    assertEquals(machine.read("b"), 0)
    assert(!machine.lastCompleted)
    assertEquals(machine.reads, 1)
    assertEquals(machine.pending.toVector, Vector("b"))
  }

  test("a rejected source read does not count as a completed read") {
    val source = new OnlineSource {
      def inputReady: Boolean = true
      def read(char: String): OnlineStep = throw new IllegalArgumentException("rejected")
      def work(): OnlineStep = throw new AssertionError("unexpected work")
    }
    val machine = new BufferedSource(source, 1)
    interceptMessage[IllegalArgumentException]("rejected")(machine.read("a"))
    val actual = s"${machine.offered} ${machine.reads} ${machine.outputs} ${machine.transitions} ${machine.pending.size}\n"
    PyDiff.assertSameAsPython(actual, "-c",
      """from galil_realtime import BufferedSource
        |class RejectingSource:
        |  input_ready = True
        |  def read(self, char): raise ValueError("rejected")
        |m = BufferedSource(RejectingSource(), 1)
        |try: m.read("a")
        |except ValueError: pass
        |print(m.offered, m.reads, m.outputs, m.transitions, len(m.pending))
        |""".stripMargin)
  }

  private val longWords = Vector("a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12)

  test("derived schedule on binary prefixes and periodic breaks") {
    for (word <- Words.upTo("ab", 4).toVector ++ longWords) {
      val machine = RealtimeGalil()
      assert(machine.acceptsEmpty)
      val actual = word.map(char => machine.read(char.toString)).toVector
      assertEquals(actual, prefixAnswers(word), word)
    }
  }

  test("the buffered controller's answers and counters match python line by line") {
    def pyBool(b: Boolean): String = if (b) { "True" } else { "False" }
    val out = new StringBuilder
    for (word <- Words.upTo("ab", 3).toVector ++ longWords) {
      val m = RealtimeGalil()
      val answers = word.map(char => m.read(char.toString))
      out.append(s"'$word' ${answers.mkString("[", ", ", "]")} ${m.service} ${m.offered} ${m.reads} ${m.outputs} ${m.transitions} " +
        s"${m.maxPending} ${pyBool(m.lastCompleted)} ${m.galil.vm.t} ${m.pending.map(c => s"'$c'").mkString("[", ", ", "]")}\n")
    }
    PyDiff.assertSameAsPython(out.toString, "-c",
      """from itertools import product
        |from galil_realtime import RealtimeGalil
        |words = ["".join(c) for n in range(4) for c in product("ab", repeat=n)]
        |words += ["a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12]
        |for word in words:
        |  m = RealtimeGalil()
        |  answers = [m.read(c) for c in word]
        |  print(repr(word), answers, m.service, m.offered, m.reads, m.outputs, m.transitions, m.max_pending, m.last_completed, m.source.vm.t, list(m.pending))
        |""".stripMargin)
  }
}
