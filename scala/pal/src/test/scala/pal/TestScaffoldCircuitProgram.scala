package pal

/** Test helpers of `test_scaffold_circuit_program.py` that other suites import.
  *
  * Only the helpers needed so far are ported here (`scalar`); the suite for
  * `scaffold_circuit_program` itself belongs to a later task and will extend
  * this object.
  */
object TestScaffoldCircuitProgram {

  /** Decode the finite scalar `key` stored in `node` from its label bits (Python `scalar`). */
  def scalar(circuit: Circuit, node: Node, key: String): Any = {
    val domain = circuit.domains(key)._1
    val bits = 0 until ScaffoldCircuit.bitWidth(domain.length)
    val index = bits.filter(bit => node.labels(circuit.labelIds((key, bit)))).map(bit => 1 << bit).sum
    domain(index)
  }
}
