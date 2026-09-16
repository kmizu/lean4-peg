package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import ScaffoldCircuit.conjunction

/** Head order tests against integer positions (port of `test_scaffold_head_distances.py`). */
object ScaffoldHeadDistancesSuite {

  sealed trait Action
  final case class Move(head: String, direction: Int) extends Action
  final case class Copy(target: String, source: String) extends Action

  val ACTIONS: VectorMap[Char, Action] = VectorMap(
    'a' -> Move("A", 1), 'b' -> Move("B", 1), 'c' -> Move("C", 1),
    'd' -> Copy("A", "B"), 'e' -> Copy("B", "C"), 'f' -> Copy("C", "A"),
    'g' -> Move("A", -1), 'h' -> Move("B", -1), 'i' -> Move("C", -1)
  )

  val actionChars: Vector[Char] = ACTIONS.keys.toVector

  /** Returns the machine and the label of every `eq`/`lt` observation. */
  def fixture(exclusiveMoves: Boolean = false): (Scaffold, VectorMap[(String, String, String), String]) = {
    val circuit = new Circuit(actionChars.mkString)
    val bank = new HeadDistances(circuit, Seq("A", "B", "C"), exclusiveMoves = exclusiveMoves)
    for ((char, action) <- ACTIONS) {
      val enabled = circuit.input().eqTo(char)
      action match {
        case Move(head, direction) => bank.move(head, direction, enabled)
        case Copy(target, source) => bank.copy(target, source, enabled)
      }
    }
    val observations = mutable.LinkedHashMap.empty[(String, String, String), String]
    for (left <- bank.names; right <- bank.names; relation <- Seq("eq", "lt")) {
      val test = if (relation == "eq") { bank.equal(left, right) } else { bank.less(left, right) }
      val key = s"$relation.$left.$right"
      circuit.put(key, Value.select(test, Value.constant(true), Value.constant(false)), Vector(false, true), relation == "eq")
      observations((relation, left, right)) = circuit.labelIds((key, 0))
    }
    bank.commit()
    (circuit.machine(conjunction(bank.equal("A", "B"), bank.less("B", "C"))), VectorMap.from(observations))
  }

  def apply(positions: mutable.Map[String, Int], char: Char): Unit = {
    ACTIONS(char) match {
      case Move(head, direction) => positions(head) = positions(head) + direction
      case Copy(target, source) => positions(target) = positions(source)
    }
  }

  def initialPositions(): mutable.Map[String, Int] = mutable.LinkedHashMap("A" -> 0, "B" -> 0, "C" -> 0)
}

class ScaffoldHeadDistancesSuite extends munit.FunSuite {
  import ScaffoldHeadDistancesSuite.*

  /** The Python cross-checks run python3 several times; allow for a loaded machine. */
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(600, "s")

  test("all pair orders after moves and copies") {
    compareCommands(false)
    compareCommands(true)
  }

  private def compareCommands(exclusiveMoves: Boolean): Unit = {
    val (machine, observations) = Expr.share { fixture(exclusiveMoves) }
    var root = machine.initialNode()
    val positions = initialPositions()
    val rng = new PyRandom(907)
    val word = "a" * 24 + "g" * 48 + "f" + "b" * 17 + "def" +
      Vector.fill(200)(rng.choice(actionChars)).mkString
    for (char <- word) {
      apply(positions, char)
      root = machine.step(root, char).get
      for (((relation, left, right), label) <- observations) {
        val expected = if (relation == "eq") { positions(left) == positions(right) } else { positions(left) < positions(right) }
        assertEquals(root.labels(label), expected, (char, positions, relation, left, right))
      }
    }
  }

  test("order test survives ordinary PEG translation") {
    val (machine, _) = Expr.share { fixture() }
    val grammar = new Grammar(machine.compile())
    val rng = new PyRandom(908)
    val samples = mutable.ArrayBuffer("", "c", "ac", "abc", "aadc", "cfa", "ahdfccc", "gigidec")
    for (_ <- 0 until 35) {
      val length = rng.randint(1, 15)
      samples += Vector.fill(length)(rng.choice(actionChars)).mkString
    }
    for (word <- samples) {
      val positions = initialPositions()
      for (char <- word) { apply(positions, char) }
      val expected = positions("A") == positions("B") && positions("B") < positions("C")
      assertEquals(grammar.accepts(word.reverse), expected, (word, positions))
    }
  }

  test("invalid bank and move") {
    intercept[IllegalArgumentException] { new HeadDistances(new Circuit(), Seq("A", "A")) }
    val bank = new HeadDistances(new Circuit(), Seq("A", "B"))
    intercept[IllegalArgumentException] { bank.move("A", 2) }
    intercept[IllegalArgumentException] { bank.copy("A", "Z") }
  }

  test("both fixtures' rule lists match the Python fixture") {
    val script =
      """from test_scaffold_head_distances import fixture
        |from symbolic_sca2peg import share_expressions
        |for exclusive in (False, True):
        |  with share_expressions():
        |    machine, _ = fixture(exclusive)
        |  print(machine.compile(), end="")
        |""".stripMargin
    val out = new StringBuilder
    for (exclusive <- Seq(false, true)) {
      val (machine, _) = Expr.share { fixture(exclusive) }
      out.append(machine.compile())
    }
    PyDiff.assertSameAsPython(out.toString, "-c", script)
  }
}
