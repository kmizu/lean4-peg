package pal

import Scavm.{Node, Self, Stats, VM}
import ScavmStructs.{Builder, CounterView, emit}
import ScaffoldInput.{InputHead, ReadonlyHead}
import ScaffoldPlaces.PlaceHead
import ScaffoldSearch.{Mode, SearchView}
import FppFinite.Instruction
import DpFinite.{buildDpProgram, OUTPUT}

/** Port of `test_scaffold_search.py`: paced doubling search uses real finite FPP
  * instructions on the scaffold. Every fixture is also run through the Python
  * `exercise` and the answer, visited modes and statistics compared line by line.
  */
class ScaffoldSearchSuite extends munit.FunSuite {

  private final case class Exercised(answer: Option[Int], modes: Set[Mode], stats: Stats, matchEvents: Int) {
    /** Python `print(answer, sorted(modes), {**vm.stats(), "match_events": n})`. */
    def pythonRepr: String = {
      val shownModes = modes.map(_.label).toVector.sorted.map(m => s"'$m'").mkString("[", ", ", "]")
      val shownStats = stats.pythonRepr.dropRight(1) + s", 'match_events': $matchEvents}"
      s"${answer.fold("None")(_.toString)} $shownModes $shownStats"
    }
  }

  /** The observer's decision to fire one synthetic match event (Python `schedule(job, events)`). */
  private type Schedule[H <: ReadonlyHead[H]] = (SearchView[H], Int) => Boolean

  /** Python `exercise(word, lower, pace, schedule, places)`.
    *
    * Explicit input and lower-bound fixtures. Three independent input heads
    * receive each real input; no index is used by the search transition. The
    * observer controls the pace of synthetic match events. It does not choose
    * the answer, stage span, scan position or candidate inside SearchView.
    */
  private def exercise[H <: ReadonlyHead[H]](
      word: String,
      lower: Int,
      pace: Option[Int],
      schedule: Option[Schedule[H]],
      places: Boolean,
      makeHead: (VM, Option[Node], Builder, String) => H
  ): Exercised = {
    val vm = new VM
    val kernel = buildDpProgram(if (places) { "abs" } else { "ab" })
    def heads(b: Builder): (H, H) = (makeHead(vm, vm.top, b, "c"), makeHead(vm, vm.top, b, "w"))
    for (symbol <- word) {
      vm.begin()
      val b = new Builder
      b.label("input") = symbol.toString
      val (center, walk) = heads(b)
      for (head <- Seq(center, walk)) {
        head.append(Self)
        head.right()
        if (places) {
          head.right()
        }
      }
      val radius = new CounterView(vm, vm.top, b, "radius")
      val bound = new CounterView(vm, vm.top, b, "bound")
      val job = new SearchView(vm, vm.top, b, kernel, center, walk, radius)
      center.finish()
      walk.finish()
      radius.finish()
      bound.finish()
      job.finish()
      emit(vm, b)
    }
    for (_ <- 0 until lower) {
      vm.begin()
      val b = new Builder
      b.label("input") = "a"
      val (center, walk) = heads(b)
      val radius = new CounterView(vm, vm.top, b, "radius")
      val bound = new CounterView(vm, vm.top, b, "bound")
      bound.inc()
      val job = new SearchView(vm, vm.top, b, kernel, center, walk, radius)
      center.finish()
      walk.finish()
      radius.finish()
      bound.finish()
      job.finish()
      emit(vm, b)
    }
    var modes = Set.empty[Mode]
    var matchEvents = 0
    var lastMode = Mode.Idle
    var finished = false
    var tick = 0
    val watchdog = 10000 * (word.length + lower + 1)
    while (!finished && tick < watchdog) {
      vm.begin()
      val b = new Builder
      b.label("input") = "a"
      val (center, walk) = heads(b)
      val radius = new CounterView(vm, vm.top, b, "radius")
      val bound = new CounterView(vm, vm.top, b, "bound")
      val job = new SearchView(vm, vm.top, b, kernel, center, walk, radius)
      if (tick == 0) {
        job.start(bound)
      }
      val advance = schedule match {
        case Some(decide) => decide(job, matchEvents)
        case None => (pace.isEmpty && job.mode == Mode.Wait) || pace.exists(p => tick % p == p - 1)
      }
      if (advance) {
        job.advanceMatch()
        matchEvents += 1
      }
      job.step()
      modes += job.mode
      lastMode = job.mode
      finished = job.mode == Mode.Found || job.mode == Mode.Missed
      center.finish()
      walk.finish()
      radius.finish()
      bound.finish()
      job.finish()
      emit(vm, b)
      tick += 1
    }
    if (!finished) {
      throw new AssertionError("search watchdog")
    }
    val found = lastMode == Mode.Found
    var answer = 0
    if (found) {
      // Decode unary OUTPUT only in the observer, one tape move per node.
      var decoding = true
      while (decoding) {
        vm.begin()
        val b = new Builder
        b.label("input") = "a"
        val (center, walk) = heads(b)
        val radius = new CounterView(vm, vm.top, b, "radius")
        val bound = new CounterView(vm, vm.top, b, "bound")
        val job = new SearchView(vm, vm.top, b, kernel, center, walk, radius)
        val tape = job.program.tapes(OUTPUT)
        if (tape.read() == "^") {
          decoding = false
        } else {
          answer += 1
          tape.move(-1)
          center.finish()
          walk.finish()
          radius.finish()
          bound.finish()
          job.finish()
          emit(vm, b)
        }
      }
    }
    Exercised(if (found) { Some(answer) } else { None }, modes, vm.stats, matchEvents)
  }

  private def onInput(word: String, lower: Int = 0, pace: Option[Int] = None, schedule: Option[Schedule[InputHead]] = None): Exercised = {
    exercise[InputHead](word, lower, pace, schedule, places = false, new InputHead(_, _, _, _))
  }

  private def onPlaces(word: String): Exercised = {
    exercise[PlaceHead](word, 0, None, None, places = true, new PlaceHead(_, _, _, _))
  }

  /** The least h in (lower, (n-1)/4] with palindromic suffixes of lengths 2h+1 and 4h+1. */
  private def doublePalindrome(view: String, lower: Int): Option[Int] = {
    (lower + 1 to (view.length - 1) / 4).find { h =>
      val short = view.takeRight(2 * h + 1)
      val long = view.takeRight(4 * h + 1)
      short == short.reverse && long == long.reverse
    }
  }

  private val definitionCases = Vector(("a", 0), ("abba", 0), ("aaaaa", 0), ("a" * 17, 2), ("abba" * 5, 0), ("abab" * 5, 1), ("a" * 17 + "b", 0))

  /** The schedule of the exact-deadline test: match at the first run step and at its halt, then at every wait. */
  private val exactDeadline: Schedule[InputHead] = (job, events) => {
    val atHalt = job.program.program.instruction(job.program.pc) == Instruction.Halt
    (job.mode == Mode.Run && (events == 0 || (events == 1 && atHalt))) || job.mode == Mode.Wait
  }

  test("search reads virtual places from unmodified binary input") {
    for (word <- Seq("aaaaaa", "ababababab", "abbabbabba")) {
      val view = word.flatMap(symbol => symbol.toString + "s")
      assertEquals(onPlaces(word).answer, doublePalindrome(view, 0), word)
    }
  }

  test("finite search matches the suffix double-palindrome definition") {
    for ((word, lower) <- definitionCases) {
      val result = onInput(word, lower)
      assertEquals(result.answer, doublePalindrome(word, lower), (word, lower))
      assert(result.stats.radius < 500, result.stats)
    }
  }

  test("missed stages wait for match before doubling") {
    val result = onInput("a" * 17 + "b")
    assertEquals(result.answer, None)
    assert(result.modes.contains(Mode.Wait))
    assert(result.modes.contains(Mode.Double))
  }

  test("search can overlap slow match steps") {
    val result = onInput("a" * 65, lower = 8, pace = Some(1024))
    assertEquals(result.answer, Some(9))
    assert(result.modes.contains(Mode.Run))
    assert(result.matchEvents > 0)
  }

  test("nonfinal miss on exact deadline starts doubling without extra wait") {
    val result = onInput("a" * 17 + "b", schedule = Some(exactDeadline))
    assertEquals(result.answer, None)
    assert(result.modes.contains(Mode.Double))
  }

  test("search rejects actual deadline overrun") {
    val e = intercept[IllegalStateException](onInput("a" * 17 + "b", pace = Some(1)))
    assert(e.getMessage.contains("stage deadline"), e.getMessage)
  }

  test("every fixture's answer, modes and statistics match the python exercise") {
    val out = new StringBuilder
    for (word <- Seq("aaaaaa", "ababababab", "abbabbabba")) {
      out.append(s"places '$word' ${onPlaces(word).pythonRepr}\n")
    }
    for ((word, lower) <- definitionCases) {
      out.append(s"lower '$word' $lower ${onInput(word, lower).pythonRepr}\n")
    }
    out.append(s"pace ${onInput("a" * 65, lower = 8, pace = Some(1024)).pythonRepr}\n")
    out.append(s"schedule ${onInput("a" * 17 + "b", schedule = Some(exactDeadline)).pythonRepr}\n")
    val e = intercept[IllegalStateException](onInput("a" * 17 + "b", pace = Some(1)))
    out.append(s"RuntimeError ${e.getMessage}\n")
    PyDiff.assertSameAsPython(out.toString, "-c",
      """from test_scaffold_search import exercise
        |for word in ("aaaaaa", "ababababab", "abbabbabba"):
        |  answer, modes, stats = exercise(word, places=True); print("places", repr(word), answer, sorted(modes), stats)
        |for word, lower in (("a", 0), ("abba", 0), ("aaaaa", 0), ("a" * 17, 2), ("abba" * 5, 0), ("abab" * 5, 1), ("a" * 17 + "b", 0)):
        |  answer, modes, stats = exercise(word, lower); print("lower", repr(word), lower, answer, sorted(modes), stats)
        |answer, modes, stats = exercise("a" * 65, lower=8, pace=1024); print("pace", answer, sorted(modes), stats)
        |def schedule(job, events):
        |  return ((job.mode == "run" and (events == 0 or (events == 1 and job.program.program.code[job.program.pc][0] == "halt"))) or job.mode == "wait")
        |answer, modes, stats = exercise("a" * 17 + "b", schedule=schedule); print("schedule", answer, sorted(modes), stats)
        |try:
        |  exercise("a" * 17 + "b", pace=1)
        |except RuntimeError as e:
        |  print("RuntimeError", e)
        |""".stripMargin)
  }
}
