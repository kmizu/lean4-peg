package pal

/** Byte pins for circuit lowering: Python builds the same circuit and prints its verdicts and grammar.
  *
  * A script appended to `PREAMBLE` must end with `report(machine, words)`,
  * which prints one line of acceptance bits (`1`/`0` per word) followed by the
  * compiled grammar. The Scala side then compares both.
  */
object PyCircuit {

  val PREAMBLE: String =
    """from itertools import product
      |from scaffold_circuit import Circuit, Value, PREVIOUS, NEW, EMPTY, TRUE, FALSE, conjunction, disjunction, neg, choose
      |from scaffold_circuit_structs import StackPool, Stack, Tape, Counter, Queue
      |def words(alphabet, limit):
      |  return ["".join(w) for n in range(limit + 1) for w in product(alphabet, repeat=n)]
      |def report(m, ws):
      |  print("".join("1" if m.run(w) else "0" for w in ws)); print(m.compile(), end="")
      |""".stripMargin

  final case class Expected(bits: String, peg: String)

  /** Run `script` (after `PREAMBLE`) in docs/palindromes-in-peg and split its report. */
  def expected(script: String): Expected = {
    val output = PyDiff.python("-c", PREAMBLE + script)
    val newline = output.indexOf('\n')
    Expected(output.substring(0, newline), output.substring(newline + 1))
  }

  /** The acceptance bits of `machine` over `words`, in the same format as the Python report. */
  def acceptanceBits(machine: Scaffold, words: Iterable[String]): String = {
    words.iterator.map(word => if (machine.run(word)) { "1" } else { "0" }).mkString
  }
}
