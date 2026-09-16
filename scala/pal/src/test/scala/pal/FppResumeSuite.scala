package pal

import FppFinite.*

/** test_fpp_resume.py */
class FppResumeSuite extends munit.FunSuite {

  test("single instruction pauses preserve full result") {
    val p = buildProgram()
    val word = "abaababa"
    val z = Tape.bounded(word)
    val tapes = Array(z, z.copy, new Tape(Seq(0 -> "0", 1 -> "1", 2 -> "0")),
      new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)), new Tape(Seq(0 -> LEFT)))
    val e = p.execution(tapes, Array(0, 1, 0, 0, 0, 0, 0))
    while (!e.done) {
      val before = e.steps
      e.step()
      assertEquals(e.steps, before + 1)
    }
    val full = p.run(word)
    assertEquals(e.result(), full)
  }
}
