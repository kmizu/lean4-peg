package pal

/** The eight checked-in controller tables must be reproduced byte for byte. */
class ControllerArtifactsSuite extends munit.FunSuite {

  for ((name, generate) <- ControllerArtifacts.all) {
    test(s"generated/$name-controller.json is reproduced byte for byte") {
      val actual = generate()
      val golden = PyDiff.readGolden(s"generated/$name-controller.json")
      if (actual != golden) {
        fail(PyDiff.firstDifference(actual, golden, name))
      }
    }
  }

  test("instruction JSON round-trips") {
    val p = ChainFinite.buildChainProgram("abs")
    for (row <- p.instructions) {
      assertEquals(ControllerArtifacts.instructionFromJson(ControllerArtifacts.instructionJson(row)), row)
    }
  }

  test("the default body-symbol order builds the same search behaviour as the golden order") {
    val golden = ControllerArtifacts.load(PyDiff.readGolden("generated/dp-search-controller.json"))
    val default = DpSearchFinite.buildSearchProgram("abs")
    assertEquals(default.code.size, golden.code.size)
    for ((prefix, lower) <- Seq(("asasa", 0), ("as" * 35, 3), ("aabasbbbs" * 12, 0), ("b", 1))) {
      val (h1, r1, _) = DpSearchFiniteSuite.execute(default, prefix, "babas", lower)
      val (h2, r2, _) = DpSearchFiniteSuite.execute(golden, prefix, "babas", lower)
      assertEquals(h1, h2)
      assertEquals(r1.steps, r2.steps)
    }
  }

  test("Json.dumps matches json.dumps(indent=2) on a mixed value") {
    val value = Json.obj(
      "a" -> Json.arr(Json.Num(1), Json.Str("x\"y\\z\n"), Json.obj(), Json.arr()),
      "b" -> Json.Obj(Vector("k" -> Json.Null, "é" -> Json.Bool(true))))
    PyDiff.assertSameAsPython(Json.dumps(value) + "\n", "-c",
      "import json; print(json.dumps({'a': [1, 'x\"y\\\\z\\n', {}, []], 'b': {'k': None, '\\u00e9': True}}, indent=2))")
    assertEquals(Json.parse(Json.dumps(value)), value)
  }
}
