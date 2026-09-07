package pal

import scala.collection.mutable

import Expr.{SELF, old, symbol, pointer, read, both, either, negate, select}
import ScaffoldEventBuffer.{bufferSource, packService}

/** Local FIFO service and one-node rounds for an independently known language (port of `test_scaffold_event_buffer.py`). */
object ScaffoldEventBufferSuite {

  /** Read, compute/emit, prepare, read ... . The answer means the current
    * symbol is 'a'; a retained pointer supplies that symbol during compute.
    */
  def sourceFixture(): Scaffold = {
    val initial = Vector("ready" -> true, "busy" -> false, "prepare" -> false, "saved_a" -> false,
                         "event" -> false, "answer" -> false, "fault" -> false)
    val badEvent = either(both(old(Nil, "ready"), symbol('.')),
                          both(negate(old(Nil, "ready")), negate(symbol('.'))))
    val labels = Vector("ready" -> old(Nil, "prepare"), "busy" -> old(Nil, "ready"),
                        "prepare" -> old(Nil, "busy"),
                        "saved_a" -> either(both(old(Nil, "ready"), symbol('a')),
                                            both(negate(old(Nil, "ready")), old(Nil, "saved_a"))),
                        "event" -> old(Nil, "busy"),
                        "answer" -> both(old(Nil, "busy"), read(pointer(Seq("saved")), "saved_a")),
                        "fault" -> either(old(Nil, "fault"), badEvent))
    new Scaffold(initial, labels,
                 Vector("saved" -> select(old(Nil, "ready"), SELF, pointer(Seq("saved")))),
                 "answer", "ab.")
  }
}

class ScaffoldEventBufferSuite extends munit.FunSuite {

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")
  import ScaffoldEventBufferSuite.sourceFixture

  test("local queue service matches external event model") {
    val (_, machine) = bufferSource(sourceFixture(), "ready", "event", "answer")
    for (events <- Seq("a...", "b...", "ab......", "aab.........", "a" * 12 + "b" * 8 + "." * 70)) {
      var root = machine.initialNode()
      val pending = mutable.Queue.empty[Char]
      var mode = "ready"
      var saved = ' '
      var answer = true
      for (char <- events) {
        if (char != '.') {
          pending.enqueue(char)
          answer = false
        } else if (mode == "ready" && pending.nonEmpty) {
          saved = pending.dequeue()
          mode = "busy"
        } else if (mode == "busy") {
          mode = "prepare"
          if (pending.isEmpty) { answer = saved == 'a' }
        } else if (mode == "prepare") {
          mode = "ready"
        }
        root = machine.step(root, char).get
        assertEquals(root.labels(machine.accepting), answer, events)
        assert(!root.labels("source.fault"), events)
      }
    }
  }

  test("packed ordinary PEG needs only the original letters") {
    comparePacked(false)
  }

  test("demand packing keeps delayed outputs and cross-round queue cells") {
    comparePacked(true)
  }

  private def comparePacked(lazyRound: Boolean): Unit = {
    val (_, wrapper) = bufferSource(sourceFixture(), "ready", "event", "answer")
    val packed = packService(wrapper, 3, lazyRound = lazyRound)
    val grammar = new Grammar(packed.compile())
    assertEquals(packed.alphabet, "ab")
    for (word <- Words.upTo("ab", 4)) {
      val expected = word.isEmpty || word.last == 'a'
      assertEquals(packed.run(word), expected, word)
      assertEquals(grammar.accepts(word.reverse), expected, word)
    }
  }

  private val pythonScript =
    """from test_scaffold_event_buffer import source_fixture
      |from scaffold_event_buffer import buffer_source, pack_service
      |_, wrapper = buffer_source(source_fixture(), "ready", "event", "answer")
      |print(wrapper.compile(), end="")
      |print(pack_service(wrapper, 3).compile(), end="")
      |print(pack_service(wrapper, 3, lazy=True).compile(), end="")
      |""".stripMargin

  test("wrapper and packed rule lists match the Python event buffer") {
    val (_, wrapper) = bufferSource(sourceFixture(), "ready", "event", "answer")
    val out = new StringBuilder
    out.append(wrapper.compile())
    out.append(packService(wrapper, 3).compile())
    out.append(packService(wrapper, 3, lazyRound = true).compile())
    PyDiff.assertSameAsPython(out.toString, "-c", pythonScript)
  }
}
