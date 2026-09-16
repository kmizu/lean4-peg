package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import Expr.{SELF, both, either, exists, negate, old, pointer, select, symbol}

/** Regenerate ordinary PEG examples from symbolic scaffold equations.
  *
  * Port of `generate_scaffold_examples.py`. `main` takes an optional
  * `docs/palindromes-in-peg` directory argument; by default it is located by
  * walking up from the working directory.
  */
object GenerateScaffoldExamples {

  def markedPalindrome(): Scaffold = {
    val right = old(Nil, "right")
    val matched = either(both(symbol('a'), old(Seq("top"), "a")),
                         both(symbol('b'), old(Seq("top"), "b")))
    val live = both(old(Nil, "live"), either(negate(right), matched))
    new Scaffold(
      Vector("a" -> false, "b" -> false, "right" -> false, "live" -> true, "out" -> false),
      Vector("a" -> symbol('a'), "b" -> symbol('b'),
             "right" -> either(right, symbol('#')), "live" -> live,
             "out" -> both(live, either(
               both(negate(right), symbol('#'), negate(exists(Seq("top")))),
               both(right, matched, negate(exists(Seq("top", "next"))))))),
      Vector("top" -> select(right, pointer(Seq("top", "next")),
                             select(symbol('#'), pointer(Seq("top")), SELF)),
             "next" -> pointer(Seq("top"))),
      "out", "ab#")
  }

  /** Python `Path(__file__).parent`: the docs/palindromes-in-peg directory. */
  def locateDirectory(args: Array[String]): Path = {
    args.headOption.map(Paths.get(_)) match {
      case Some(explicit) => explicit
      case None =>
        val here = Paths.get("").toAbsolutePath
        Iterator.iterate(here)(_.getParent).takeWhile(_ != null)
          .map(_.resolve("docs/palindromes-in-peg"))
          .find(Files.isDirectory(_))
          .getOrElse(throw new IllegalStateException(s"docs/palindromes-in-peg not found above $here"))
    }
  }

  /** Python `f"{len(output.splitlines())} rules, {len(output.encode())} bytes"`. */
  def summary(output: String): String = {
    s"${output.linesIterator.length} rules, ${output.getBytes(StandardCharsets.UTF_8).length} bytes"
  }

  def main(args: Array[String]): Unit = {
    val output = markedPalindrome().compile()
    val target = locateDirectory(args).resolve("generated").resolve("scaffold_marked_palindrome.peg")
    Files.write(target, output.getBytes(StandardCharsets.UTF_8))
    println(summary(output))
  }
}
