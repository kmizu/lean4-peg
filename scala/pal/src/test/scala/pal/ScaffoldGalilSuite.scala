package pal

import Scavm.{Label, Node}
import ScaffoldGalil.{run, recognize, Events, FPP_QUANTUM, OnlineGalil, OnlineStep}
import FppFinite.Instruction.{Move, Read, Write}
import FppSubroutine.buildMarkedProgram
import DpFinite.buildDpProgram

/** Test helpers shared with `GalilContractsSuite`: coordinates decoded from the
  * immutable stacks of the online controller (never by the controller itself).
  */
object ScaffoldGalilFixture {

  /** Python `OnlineGalilTest.place(source, head)`: test-only coordinates recovered
    * from immutable stacks, never by A.
    */
  def place(source: OnlineGalil, head: String): Int = {
    val root: Node = source.vm.top.getOrElse(throw new IllegalStateException("no top node"))
    val name = head + ".l"
    var node = root.pointer(name + ".top")
    var creator = root.label(name + ".tname").asStr
    var slot = root.label(name + ".tslot").asInt
    var count = 0
    while (node.isDefined) {
      val key = s"$creator.$slot."
      val current = node.get
      creator = current.label(key + "bname").asStr
      slot = current.label(key + "bslot").asInt
      node = current.pointer(key + "below")
      count += 1
    }
    2 * count - (if (!root.label(head + ".gap").asBool) { 1 } else { 0 })
  }

  /** `int(word == word[::-1])` for every nonempty prefix. */
  def prefixAnswers(word: String): Vector[Int] = {
    (1 to word.length).map { i =>
      val prefix = word.take(i)
      if (prefix == prefix.reverse) { 1 } else { 0 }
    }.toVector
  }
}

/** Port of `test_scaffold_galil.py`: whole scaffold execution with actual DP,
  * periodic prediction and shifts (`ScaffoldGalilTest` and `OnlineGalilTest`).
  * The legacy `run` and the event interface are also driven in Python on the same
  * words and their reports, statistics, events and head places compared line by line.
  */
class ScaffoldGalilSuite extends munit.FunSuite {
  import ScaffoldGalilFixture.{place, prefixAnswers}

  // the whole controller runs thousands of scaffold ticks per letter, and the
  // differential test also waits for python3 (about 50 s on its own)
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  // ------------------------------------------------------------------ ScaffoldGalilTest

  test("quantum cannot overflow finite tape cell slots") {
    // Max-plus path analysis includes infeasible branch combinations, making
    // this a static upper bound rather than a sample of observed executions.
    for (program <- Seq(buildMarkedProgram("abs"), buildDpProgram("abs"))) {
      val code = program.instructions
      val successors: Vector[Vector[Int]] = code.map {
        case Read(_, choices) => choices.values.toVector
        case Move(_, _, next) => Vector(next)
        case Write(_, _, next) => Vector(next)
        case _ => Vector.empty
      }
      for (tape <- 0 until program.ntapes) {
        var counts = Vector.fill(code.size)(0)
        for (_ <- 0 until FPP_QUANTUM) {
          counts = code.zipWithIndex.map { case (row, i) =>
            val moves = row match {
              case Move(t, _, _) if t == tape => 1
              case _ => 0
            }
            moves + successors(i).map(counts).maxOption.getOrElse(0)
          }
        }
        assert(counts.max <= 32, (tape, counts.max))
      }
    }
  }

  test("fixed recognizer includes epsilon") {
    assert(recognize(""))
    assert(recognize("aba"))
    assert(!recognize("ab"))
    intercept[IllegalArgumentException](recognize("abc"))
  }

  test("all binary prefixes through length four") {
    for (word <- Words.upTo("ab", 4)) {
      assertEquals(run(word).reports, prefixAnswers(word), word)
    }
  }

  test("periodic inputs use real chain shifts") {
    for (word <- Seq("a" * 16, "ab" * 12, "abba" * 8)) {
      val result = run(word)
      assertEquals(result.reports, prefixAnswers(word), word)
      assert(result.events.chainShifts > 0, (word, result))
      assert(result.events.fppCalls < word.length, (word, result))
      assert(result.stats.radius <= 1024, result.stats)
      assert(result.stats.fields <= 1024, result.stats)
    }
  }

  test("outer match with broken period restarts search") {
    val word = "ab" + "a" * 20 + "ba"
    val result = run(word)
    assertEquals(result.reports, prefixAnswers(word))
    assert(result.events.searchRestarts > 0, result)
  }

  test("fixed budget executes the whole controller") {
    val word = "a" * 8
    val budget = 2048
    val result = run(word, Some(budget))
    assertEquals(result.reports, Vector.fill(word.length)(1))
    assertEquals(result.stats.steps, budget * word.length)
    assert(result.events.chainShifts > 0, result)
  }

  test("periodic breaks resume real search or fallback") {
    for (word <- Seq("a" * 12 + "b" + "a" * 12, "ab" * 10 + "bbaa" + "ab" * 8, "abba" * 6 + "bab" + "abba" * 5)) {
      assertEquals(run(word).reports, prefixAnswers(word), word)
    }
  }

  // ------------------------------------------------------------------ OnlineGalilTest

  /** Observe every output, including work after an answer was emitted. */
  private def drainToRead(source: OnlineGalil, first: OnlineStep): (Vector[Int], Events) = {
    val outputs = Vector.newBuilder[Int]
    var events = Events()
    var result = first
    var draining = true
    while (draining) {
      result.output.foreach(outputs += _)
      events = events + result.events
      if (result.inputReady) {
        draining = false
      } else {
        result = source.work()
        // Work has no input character, even after a positive answer. Input
        // heads must retain real arrival cells rather than use these work cells.
        assertEquals(source.vm.top.get.label("input"), Label.Null)
      }
    }
    (outputs.result(), events)
  }

  test("output does not authorize the next read") {
    val source = new OnlineGalil
    val waiting = intercept[IllegalArgumentException](source.work())
    assert(waiting.getMessage.contains("waiting"), waiting.getMessage)
    assertEquals(source.vm.t, -1)
    for (char <- Seq("", "ab", "c")) {
      val e = intercept[IllegalArgumentException](source.read(char))
      assert(e.getMessage.contains("one binary"), e.getMessage)
    }
    assertEquals(source.vm.t, -1)

    val result = source.read("a")
    assertEquals(result.output, Some(1))
    assert(!result.inputReady)
    val before = source.vm.t
    val notReady = intercept[IllegalArgumentException](source.read("b"))
    assert(notReady.getMessage.contains("not ready"), notReady.getMessage)
    assertEquals(source.vm.t, before)
    val (outputs, _) = drainToRead(source, result)
    assertEquals(outputs, Vector(1))
    assert(source.inputReady)
    assertEquals(place(source, "C"), 2)
    assertEquals(place(source, "R"), 2)
  }

  test("pending is distinct from a completed negative answer") {
    val source = new OnlineGalil
    drainToRead(source, source.read("a"))
    val result = source.read("b")
    assertEquals(result.output, None)
    assert(!result.inputReady)
    val before = source.vm.t
    val notReady = intercept[IllegalArgumentException](source.read("a"))
    assert(notReady.getMessage.contains("not ready"), notReady.getMessage)
    assertEquals(source.vm.t, before)
    val (negative, _) = drainToRead(source, result)
    assertEquals(negative, Vector(0))
    val (positive, _) = drainToRead(source, source.read("a"))
    assertEquals(positive, Vector(1))
  }

  test("prefix answers and proper suffix center through length five") {
    // The paper continues after a positive answer with the next tentative
    // center. At a read boundary this must be the longest proper palindromic
    // suffix (empty is allowed), not the just-reported whole prefix again.
    for (word <- Words.upTo("ab", 5)) {
      val source = new OnlineGalil
      for ((char, index) <- word.zipWithIndex) {
        val i = index + 1
        val prefix = word.take(i)
        val (outputs, _) = drainToRead(source, source.read(char.toString))
        assertEquals(outputs, prefixAnswers(prefix).takeRight(1), prefix)
        val size = (1 until i).filter { m =>
          val suffix = prefix.takeRight(m)
          suffix == suffix.reverse
        }.maxOption.getOrElse(0)
        assertEquals(place(source, "C"), 2 * i - size, prefix)
        assertEquals(place(source, "R"), 2 * i, prefix)
        assertEquals(place(source, "L"), 2 * (i - size), prefix)
      }
    }
  }

  test("chain continues after reporting without the next input") {
    val source = new OnlineGalil
    var shiftsAfterOutput = 0
    for (_ <- 0 until 12) {
      var result = source.read("a")
      val outputs = Vector.newBuilder[Int]
      var reported = false
      var draining = true
      while (draining) {
        result.output.foreach { value =>
          outputs += value
          reported = true
        }
        if (reported) {
          shiftsAfterOutput += result.events.chainShifts
        }
        if (result.inputReady) {
          draining = false
        } else {
          result = source.work()
        }
      }
      assertEquals(outputs.result(), Vector(1))
    }
    assert(shiftsAfterOutput > 0)
  }

  test("periodic breaks and replay preserve each output event") {
    for (word <- Seq("ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12)) {
      val source = new OnlineGalil
      var totals = Events()
      for ((char, index) <- word.zipWithIndex) {
        val prefix = word.take(index + 1)
        val (outputs, events) = drainToRead(source, source.read(char.toString))
        assertEquals(outputs, prefixAnswers(prefix).takeRight(1), prefix)
        totals = totals + events
      }
      assert(totals.chainShifts > 0, word)
      assert(totals.replays > 0, word)
    }
  }

  // ------------------------------------------------------------------ differential

  private def pyList(xs: Seq[Int]): String = xs.mkString("[", ", ", "]")

  private def pyBool(b: Boolean): String = if (b) { "True" } else { "False" }

  /** The event interface on `word`: every step with an output, a read boundary or an
    * event, plus the number of work steps per read (as the Python script prints).
    */
  private def onlineTrace(word: String, out: StringBuilder): Unit = {
    val source = new OnlineGalil
    for ((char, index) <- word.zipWithIndex) {
      val prefix = word.take(index + 1)
      var result = source.read(char.toString)
      var works = 0
      var draining = true
      while (draining) {
        if (result.output.isDefined || result.inputReady || result.events.toMap.values.exists(_ != 0)) {
          out.append(s"'$prefix' ${source.vm.t} ${result.output.fold("None")(_.toString)} ${pyBool(result.inputReady)} " +
            s"${pyList(result.events.toMap.values.toVector)} ${place(source, "C")} ${place(source, "R")} ${place(source, "L")}\n")
        }
        if (result.inputReady) {
          draining = false
        } else {
          result = source.work()
          works += 1
        }
      }
      out.append(s"'$prefix' works $works ${source.vm.t}\n")
    }
  }

  test("run, the budgeted run and the event interface match python line by line") {
    val out = new StringBuilder
    for (word <- Seq("", "a", "ab", "aba", "abba", "a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12)) {
      val result = run(word)
      out.append(s"'$word' ${pyList(result.reports)} ${result.pythonRepr}\n")
    }
    val budgeted = run("a" * 8, Some(2048))
    out.append(s"budget ${pyList(budgeted.reports)} ${budgeted.pythonRepr}\n")
    for (word <- Seq("ab" * 6, "abba" * 4, "aabaa", "ab" + "a" * 10 + "ba")) {
      onlineTrace(word, out)
    }
    PyDiff.assertSameAsPython(out.toString, "-c",
      """from scaffold_galil import run, OnlineGalil
        |def place(source, head):
        |  root = source.vm.top
        |  name = head + ".l"
        |  node = root.ptr[name + ".top"]
        |  creator, slot = root.label[name + ".tname"], root.label[name + ".tslot"]
        |  count = 0
        |  while node is not None:
        |    key = f"{creator}.{slot}."
        |    creator, slot = node.label[key + "bname"], node.label[key + "bslot"]
        |    node = node.ptr[key + "below"]
        |    count += 1
        |  return 2 * count - int(not root.label[head + ".gap"])
        |for word in ("", "a", "ab", "aba", "abba", "a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12):
        |  reports, stats = run(word); print(repr(word), reports, stats)
        |reports, stats = run("a" * 8, budget=2048); print("budget", reports, stats)
        |for word in ("ab" * 6, "abba" * 4, "aabaa", "ab" + "a" * 10 + "ba"):
        |  source = OnlineGalil()
        |  for i, char in enumerate(word, 1):
        |    result, works = source.read(char), 0
        |    while True:
        |      if result.output is not None or result.input_ready or any(result.events.values()):
        |        print(repr(word[:i]), source.vm.t, result.output, result.input_ready, list(result.events.values()), place(source, "C"), place(source, "R"), place(source, "L"))
        |      if result.input_ready: break
        |      result, works = source.work(), works + 1
        |    print(repr(word[:i]), "works", works, source.vm.t)
        |""".stripMargin)
  }
}
