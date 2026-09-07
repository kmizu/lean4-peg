package pal

/** Port of `test_galil_contracts.py`.
  *
  * The Python test drives `scaffold_galil.OnlineGalil`, which is ported by a
  * later task (Task 3, SCAVM scaffolds). The end-to-end audit is therefore
  * left ignored below with its body written against the structural interfaces
  * of [[GalilContracts]]; the pure decoding helpers are checked against Python
  * directly.
  */
class GalilContractsSuite extends munit.FunSuite {
  import GalilContracts.{interval, palindrome, smallLivePeriod}

  test("main move replay and chain contracts (needs scaffold_galil.OnlineGalil)".ignore) {
    // TODO(Task 3): once `ScaffoldGalil.OnlineGalil` exists, adapt it to
    // `GalilContracts.Source`/`StepResult` and port the loop of
    // `test_galil_contracts.py`:
    //   for word in (...): source, audit = OnlineGalil(), ContractAudit()
    //     for i, char in enumerate(word, 1): result = source.read(char)
    //       loop: audit.observe(source, word[:i], result); break if result.input_ready; result = source.work()
    //     counts["output"] == len(word); counts["move"] == counts["replay_return"]; ...
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
