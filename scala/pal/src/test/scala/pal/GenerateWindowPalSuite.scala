package pal

import java.nio.file.Files

class GenerateWindowPalSuite extends munit.FunSuite {
  private def fixture(): Scaffold = {
    new Scaffold(Vector("answer" -> true, "constant" -> true),
      Vector("answer" -> Expr.symbol('a'), "constant" -> Expr.TRUE), Vector.empty, "answer")
  }

  test("saved source resumes without rebuilding") {
    val folder = Files.createTempDirectory("generate-window-pal-")
    val original = folder.resolve("original.peg")
    val resumed = folder.resolve("resumed.peg")
    val saved = folder.resolve("source.sca")
    val machine = fixture()
    GenerateWindowPal.run(GenerateWindowPal.Options(original, checkpoint = Some(saved)), () => machine)
    assertEquals(Files.readString(original), machine.compile())
    GenerateWindowPal.run(GenerateWindowPal.Options(resumed, resume = Some(saved)),
      () => fail("resume rebuilt the source"))
    assertEquals(Files.readString(resumed), machine.compile())
    GenerateWindowPal.run(GenerateWindowPal.Options(resumed, resume = Some(saved), skipOptimize = false),
      () => fail("resume rebuilt the source"))
    assertEquals(Files.readString(resumed), ScaffoldOptimize.optimize(machine)._1.compile())
  }

  test("small Python checkpoint emits byte-identical PEG") {
    val folder = Files.createTempDirectory("generate-window-pal-python-")
    val checkpoint = folder.resolve("source.sca")
    val expected = folder.resolve("python.peg")
    val actual = folder.resolve("scala.peg")
    val script =
      """from pathlib import Path
        |from gs_batch_clock import DEFAULT_BATCH
        |from scaffold_artifact import write
        |from symbolic_sca2peg import Scaffold, TRUE, symbol
        |machine = Scaffold({'answer': True, 'constant': True},
        |                   {'answer': symbol('a'), 'constant': TRUE}, {}, 'answer')
        |metadata = dict(kind='window-pal', k=DEFAULT_BATCH.k,
        |                matching=DEFAULT_BATCH.matching, flags=DEFAULT_BATCH.flags)
        |write(machine, Path(__import__('sys').argv[1]), metadata)
        |Path(__import__('sys').argv[2]).write_text(machine.compile(), encoding='utf-8')
        |""".stripMargin
    PyDiff.python("-c", script, checkpoint.toString, expected.toString)
    GenerateWindowPal.run(GenerateWindowPal.Options(actual, resume = Some(checkpoint)))
    assertEquals(Files.readAllBytes(actual).toVector, Files.readAllBytes(expected).toVector)
  }

  test("CLI option parsing preserves direct emission default") {
    val output = Files.createTempFile("window-pal-options-", ".peg")
    assert(GenerateWindowPal.parse(Array(output.toString)).skipOptimize)
    assert(!GenerateWindowPal.parse(Array(output.toString, "--optimize")).skipOptimize)
    intercept[IllegalArgumentException] {
      GenerateWindowPal.parse(Array("--optimize", output.toString, "--skip-optimize"))
    }
  }
}
