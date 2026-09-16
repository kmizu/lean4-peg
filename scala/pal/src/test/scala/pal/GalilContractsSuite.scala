package pal

import scala.collection.mutable

import ScaffoldGalil.OnlineGalil

/** Port of `test_galil_contracts.py`: check source boundaries against
  * independently decoded words/coordinates. The pure decoding helpers are
  * additionally checked against Python directly.
  */
class GalilContractsSuite extends munit.FunSuite {
  import GalilContracts.{interval, palindrome, smallLivePeriod, ContractAudit}

  // audits the whole online controller on seven long words
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "min")

  test("main move replay and chain contracts") {
    val totals = mutable.LinkedHashMap.empty[String, Int]
    val transcript = new StringBuilder
    val words = Seq("a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12,
      "ab" * 10 + "bbaa" + "ab" * 8, "abba" * 6 + "bab" + "abba" * 5)
    for (word <- words) {
      val source = new OnlineGalil
      val audit = new ContractAudit
      var maxWork = 0
      println(s"GalilContracts audit starting word='$word'")
      for ((char, index) <- word.zipWithIndex) {
        val prefix = word.take(index + 1)
        var result = source.read(char.toString)
        var draining = true
        var works = 0
        def diagnostic: String = {
          val root = source.vm.top.get
          s"word='$word' prefix='$prefix' work=$works tick=${source.vm.t} " +
            s"mode=${root.label("g.mode").asStr} search=${root.label("sp.mode").asStr} chain=${root.label("ch.mode").asStr}"
        }
        while (draining) {
          audit.observe(source, prefix, result)
          if (result.inputReady) {
            draining = false
          } else {
            // A fixture watchdog, not a claimed real-time bound or an increased timeout.
            assert(works < 100000, s"source did not reach its next read boundary: $diagnostic")
            result = source.work()
            works += 1
            if (works % 10000 == 0) {
              println(s"GalilContracts audit progress $diagnostic")
            }
          }
        }
        maxWork = math.max(maxWork, works)
        transcript.append(s"'$word' prefix ${index + 1} work $works mode ${source.vm.top.get.label("g.mode").asStr}\n")
      }
      println(s"GalilContracts audit completed word='$word' ticks=${source.vm.t + 1} maxWork=$maxWork")
      def count(event: String): Int = audit.counts.getOrElse(event, 0)
      assertEquals(count("output"), word.length)
      assertEquals(count("move"), count("replay_return"))
      assertEquals(count("shift"), count("shift_return"))
      for (row <- audit.rows if row.event == "output") {
        for (size <- row("size") + 1 to math.min(word.length, row("size") + row("prediction"))) {
          assertNotEquals(word.take(size), word.take(size).reverse, row)
        }
      }
      for ((name, n) <- audit.counts) {
        totals(name) = totals.getOrElse(name, 0) + n
      }
      for (row <- audit.rows) {
        val values = row.values.map { case (key, value) => s"'$key': $value" }
        transcript.append(s"'$word' {'event': '${row.event}', 'tick': ${row.tick}, ${values.mkString(", ")}}\n")
      }
    }
    for (name <- Seq("main", "dp_found", "move", "replay_start", "replay_return", "shift", "shift_return")) {
      assert(totals.getOrElse(name, 0) > 0, name)
    }
    PyDiff.assertSameAsPython(transcript.toString, "-c",
      """from scaffold_galil import OnlineGalil
        |from galil_contracts import ContractAudit
        |words = ("a" * 16, "ab" * 12, "abba" * 8, "ab" + "a" * 20 + "ba", "a" * 12 + "b" + "a" * 12,
        |         "ab" * 10 + "bbaa" + "ab" * 8, "abba" * 6 + "bab" + "abba" * 5)
        |for word in words:
        |  source, audit = OnlineGalil(), ContractAudit()
        |  for i, char in enumerate(word, 1):
        |    result, works = source.read(char), 0
        |    while True:
        |      audit.observe(source, word[:i], result)
        |      if result.input_ready: break
        |      assert works < 100000, (word, word[:i], works, source.vm.t, source.vm.top.label["g.mode"], source.vm.top.label["sp.mode"], source.vm.top.label["ch.mode"])
        |      result = source.work()
        |      works += 1
        |    print(repr(word), "prefix", i, "work", works, "mode", source.vm.top.label["g.mode"])
        |  for row in audit.rows: print(repr(word), row)
        |""".stripMargin)
  }

  test("interval, palindrome and small_live_period agree with galil_contracts.py") {
    def show(cells: Vector[GalilContracts.Cell]): String = cells.map(_.getOrElse("None")).mkString(" ")
    val words = Vector("a", "ab", "abba", "aabaa", "ababab", "abaaba", "aaaaaaaa", "abbaabba")
    val lines = words.flatMap { word =>
      val size = 2 * word.length
      val intervals = Vector((0, size), (1, size), (size / 2, size), (1, 1))
        .map { case (left, right) => s"$word interval $left $right: ${show(interval(word, left, right))} ${palindrome(interval(word, left, right))}" }
      val witnesses = for (center <- 2 to size; lower <- 0 to 3; right <- center to size) yield {
        s"$word slp $center $lower $right: ${smallLivePeriod(word, center, lower, right).map(_.toString).getOrElse("None")}"
      }
      intervals ++ witnesses
    }
    PyDiff.assertSameAsPython(lines.mkString("", "\n", "\n"), "-c",
      "from galil_contracts import interval, palindrome, small_live_period\n" +
        "def show(cells): return ' '.join('None' if c is None else c for c in cells)\n" +
        "for word in ('a', 'ab', 'abba', 'aabaa', 'ababab', 'abaaba', 'aaaaaaaa', 'abbaabba'):\n" +
        "  size = 2 * len(word)\n" +
        "  for left, right in ((0, size), (1, size), (size // 2, size), (1, 1)):\n" +
        "    print(word, 'interval', left, right, end=': ')\n" +
        "    print(show(interval(word, left, right)), str(palindrome(interval(word, left, right))).lower())\n" +
        "  for center in range(2, size + 1):\n" +
        "    for lower in range(4):\n" +
        "      for right in range(center, size + 1):\n" +
        "        print(word, 'slp', center, lower, right, end=': ')\n" +
        "        print(small_live_period(word, center, lower, right))")
    intercept[AssertionError](interval("ab", 3, 2))
  }
}
