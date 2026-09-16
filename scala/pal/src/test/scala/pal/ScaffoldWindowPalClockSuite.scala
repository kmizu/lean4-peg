package pal

import scala.collection.mutable
import Expr.{FALSE, TRUE}
import Ref.PREVIOUS
import ScaffoldCircuit.{conjunction as AND, neg}
import TestScaffoldCircuitProgram.scalar

class ScaffoldWindowPalClockSuite extends munit.FunSuite {
  override def munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(900, "s")

  private final class AlwaysMatching extends WindowWorkerLike {
    def output: Expr = TRUE
    def mode: Value[String] = Value.constant("idle")
    def flagPool: Option[FlagPackets] = None
    def flags: Option[FlagStack] = None
    def arrive(): Unit = ()
    def resetFlags(enabled: Expr): Unit = ()
    def start(enabled: Expr): Unit = ()
    def mark(enabled: Expr): Unit = ()
    def service(): Unit = ()
    def commit(): Unit = ()
  }

  private final class DeadlineFlags(val circuit: Circuit, val prefix: String) extends WindowWorkerLike {
    private val pool = new FlagPackets(circuit, 1, prefix + ".packets")
    private val stack = new FlagStack(pool, prefix + ".flags")
    val modeKey: String = prefix + ".mode"
    var mode: Value[String] = circuit.get(PREVIOUS, modeKey, Vector("idle", "run", "done"), "idle")
    private var remaining: Option[Stack] = None
    def output: Expr = FALSE
    def flagPool: Option[FlagPackets] = Some(pool)
    def flags: Option[FlagStack] = Some(stack)
    def attach(half: Stack): Unit = { remaining = Some(new Stack(half.pool, prefix + ".remaining", Some("cells"))) }
    def arrive(): Unit = ()
    def mark(enabled: Expr): Unit = ()
    def resetFlags(enabled: Expr): Unit = {
      stack.clear(enabled)
      mode = Value.select(enabled, Value.constant("idle"), mode)
    }
    def start(enabled: Expr): Unit = {
      circuit.require(neg(mode.eqTo("run")), enabled)
      remaining.get.copyFrom(attachedHalf, enabled)
      stack.clear(enabled)
      mode = Value.select(enabled, Value.constant("run"), mode)
    }
    private var attachedHalf: Stack = null
    def attachHalf(half: Stack): Unit = { attachedHalf = half; attach(half) }
    def service(): Unit = {
      val active = mode.eqTo("run")
      remaining.get.drop(active)
      new PacketWriter(stack).push(TRUE, active)
      mode = Value.select(AND(active, remaining.get.empty()), Value.constant("done"), mode)
    }
    def commit(): Unit = {
      remaining.get.commit()
      stack.commit()
      circuit.put(modeKey, mode)
    }
  }

  test("release capture and consumption through reused stages") {
    val created = mutable.ArrayBuffer.empty[DeadlineFlags]
    val (circuit, controller, machine) = Expr.share {
      val circuit = new Circuit("ab")
      val controller = new WindowPAL(circuit,
        matcherFactory = (_, _, _) => new AlwaysMatching,
        flagsFactory = (c, prefix, _) => { val worker = new DeadlineFlags(c, prefix); created += worker; worker })
      for ((stage, worker) <- controller.stages.zip(created)) { worker.attachHalf(stage.half) }
      controller.tick()
      for ((stage, index) <- controller.stages.zipWithIndex) {
        circuit.put(s"fixture.stage$index.answering",
          Value.select(stage.answering(), Value.constant(true), Value.constant(false)), Vector(false, true), false)
      }
      controller.commit()
      (circuit, controller, circuit.machine(controller.output, initialAccepting = true))
    }
    var node = machine.initialNode()
    val births = mutable.Map.empty[Int, Int]
    var slot = 0
    var word = ""
    for (now <- 1 to 130) {
      val char = "abbaba"((now - 1) % 6)
      word += char
      node = machine.step(node, char).get
      if (now >= 2 && (now & (now - 1)) == 0) { births(slot) = now; slot = 1 - slot }
      assertEquals(scalar(circuit, node, "circuit.fault"), false, now)
      assertEquals(node.labels(machine.accepting), now == 1 || now >= 4 || word.head == word.last, now)
      for ((stage, index) <- controller.stages.zipWithIndex) {
        assertEquals(scalar(circuit, node, stage.aliveKey), births.contains(index), now)
        births.get(index).foreach { width =>
          assertEquals(scalar(circuit, node, stage.intervalKey), (now - width) / (width / 2), now)
        }
      }
      if (now >= 4) {
        val active = controller.stages.indices.count { index =>
          scalar(circuit, node, s"fixture.stage$index.answering") == true
        }
        assertEquals(active, 1, s"unique answering stage at input $now")
      }
      if (Vector(4, 8, 16, 32).contains(now)) {
        assertEquals(births.values.toSet.max, now, s"stage slot reused at boundary $now")
      }
    }
    val grammar = new Grammar(machine.compile())
    for (candidate <- Vector("", "a", "ab", "aba", "abb", "aaaa", "abbaab", "a" * 17, "ab" * 17)) {
      assertEquals(grammar.accepts(candidate), candidate.length != 2 && candidate.length != 3 || candidate.head == candidate.last, candidate)
    }
  }

  test("complete source rejects rates below the derived service bounds") {
    val defaults = GsBatchClock.DEFAULT_BATCH
    val tooSlow = defaults.copy(matching = defaults.matching - 1)
    val error = intercept[IllegalArgumentException] { new WindowPAL(new Circuit("ab"), tooSlow) }
    assertEquals(error.getMessage, "the complete PAL source requires the derived k=8 service bounds")
  }
}
