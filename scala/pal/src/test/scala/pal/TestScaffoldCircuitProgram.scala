package pal

/** Shared fixtures and state observers from `test_scaffold_circuit_program.py`. */
object TestScaffoldCircuitProgram {

  def fixture(quantum: Int = 1, coarse: Boolean = false, sharedCells: Boolean = false):
      (Circuit, ScaffoldCircuitProgram.Program, Scaffold) = {
    val kernel = FppSubroutine.buildMarkedProgram("ab")
    val circuit = new Circuit("^ab$<!.")
    val lowered = new ScaffoldCircuitProgram.Program(circuit, kernel, "f", quantum = quantum + 1,
      coarse = coarse, sharedCells = sharedCells, extraMoves = 2)
    val char = circuit.input()
    val symbols = FppFinite.LEFT + "ab" + FppFinite.END
    val loading = ScaffoldCircuit.disjunction(symbols.map(char.eqTo).toVector*)
    lowered.tapes(FppSubroutine.SOURCE).write(Value(symbols.toVector.map(s => s.toString -> char.eqTo(s))), loading)
    lowered.tapes(FppSubroutine.SOURCE).move(1, loading)
    lowered.tapes(FppSubroutine.SOURCE).move(-1, char.eqTo('<'))
    lowered.start(char.eqTo('!'))
    for (_ <- 0 until quantum) { lowered.step(char.eqTo('.')) }
    lowered.commit()
    (circuit, lowered, circuit.machine(ScaffoldCircuit.conjunction(char.eqTo('.'), lowered.done)))
  }

  /** Decode the finite scalar `key` stored in `node` from its label bits (Python `scalar`). */
  def scalar(circuit: Circuit, node: Node, key: String): Any = {
    val domain = circuit.domains(key)._1
    val bits = 0 until ScaffoldCircuit.bitWidth(domain.length)
    val index = bits.filter(bit => node.labels(circuit.labelIds((key, bit)))).map(bit => 1 << bit).sum
    domain(index)
  }

  def stack(circuit: Circuit, node: Node, view: Stack): Vector[Any] = {
    var current = node.pointers(view.rootKey)
    var tag = scalar(circuit, node, view.tagKey).asInstanceOf[CellTag]
    val answer = Vector.newBuilder[Any]
    while (current.nonEmpty) {
      val cell = current.get
      answer += scalar(circuit, cell, view.pool.key(tag, "data"))
      val below = cell.pointers(view.pool.key(tag, "below"))
      tag = scalar(circuit, cell, view.pool.key(tag, "tag")).asInstanceOf[CellTag]
      current = below
    }
    answer.result()
  }
}
