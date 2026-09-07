package pal

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Checks that every Python source has a Scala source/test counterpart.
  *
  * This is intentionally a filesystem inventory rather than a fixed count:
  * adding a Python module automatically adds one more item to inspect.
  */
class PortCoverageSuite extends munit.FunSuite {

  private val scalaMain = PyDiff.pyDir.getParent.getParent.resolve("scala/pal/src/main/scala/pal")
  private val scalaTest = PyDiff.pyDir.getParent.getParent.resolve("scala/pal/src/test/scala/pal")

  private def pythonFiles(test: Boolean): Vector[Path] = {
    val stream = Files.walk(PyDiff.pyDir)
    try {
      stream.iterator().asScala
        .filter(Files.isRegularFile(_))
        .filter(_.getFileName.toString.endsWith(".py"))
        .filter(path => path.getFileName.toString.startsWith("test_") == test)
        .toVector
        .sortBy(_.toString)
    } finally {
      stream.close()
    }
  }

  private def pascal(stem: String): String = {
    val name = stem.split('_').toVector.map(part => s"${part.head.toUpper}${part.tail}").mkString
    name.replace("Sca2peg", "Sca2Peg").replace("Tm2peg", "Tm2Peg")
  }

  private def testTarget(stem: String): Path = {
    // This test imports a shared helper object rather than defining a Suite.
    val file = if (stem == "scaffold_circuit_program") {
      "TestScaffoldCircuitProgram.scala"
    } else {
      pascal(stem) + "Suite.scala"
    }
    scalaTest.resolve(file)
  }

  test("every Python module and test has a Scala counterpart") {
    val modules = pythonFiles(test = false)
    val tests = pythonFiles(test = true)
    assert(modules.nonEmpty, "no Python modules found")
    assert(tests.nonEmpty, "no Python tests found")

    val missingModules = modules.flatMap { path =>
      val stem = path.getFileName.toString.stripSuffix(".py")
      val target = scalaMain.resolve(pascal(stem) + ".scala")
      if (Files.isRegularFile(target)) { None } else { Some(s"$stem.py -> ${target.getFileName}") }
    }
    val missingTests = tests.flatMap { path =>
      val stem = path.getFileName.toString.stripSuffix(".py").stripPrefix("test_")
      val target = testTarget(stem)
      if (Files.isRegularFile(target)) { None } else { Some(s"test_$stem.py -> ${target.getFileName}") }
    }
    val missing = missingModules ++ missingTests
    assert(missing.isEmpty,
      s"Python modules=${modules.size}, tests=${tests.size}; missing Scala counterparts:\n${missing.mkString("\n")}")
  }
}
