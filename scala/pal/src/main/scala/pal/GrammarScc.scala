package pal

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.mutable

/** Well-formedness style analysis of a huge plain PEG.
  * （Python 版: `docs/palindromes-in-peg/analysis/grammar_scc.py`。フラットな `pal`
  * パッケージに置く。）
  *
  * Pass A: parse each rule body into prefix bytecode (ints).  Pass B: greatest fixpoint of
  * C = { rules that consume >= 1 char whenever they succeed }.  Pass C: tag every reference
  * edge as 'guarded' iff some element earlier in its enclosing sequence must consume; then
  * test the graph of UNGUARDED edges (reachable from S) for a cycle.
  *
  * The script prints progress lines with elapsed wall-clock seconds; `run` takes the clock
  * as a parameter so tests can pin the text.
  */
object GrammarScc {

  private val TOK = "\"(?:[^\"\\\\]|\\\\.)*\"|\\[(?:[^\\]\\\\]|\\\\.)*\\]|[A-Za-z_][A-Za-z0-9_]*|[()/&!*+?.]".r

  // opcodes
  private val LIT = 0
  private val EMPTY = 1
  private val REF = 2
  private val STAR = 3
  private val PLUS = 4
  private val OPT = 5
  private val AND = 6
  private val NOT = 7
  private val SEQ = 8
  private val ALT = 9

  /** Prefix bytecode: op [arg]; SEQ/ALT are binary: SEQ a b. */
  private final class Parser(tokens: IndexedSeq[String], ids: Map[String, Int]) {
    private var pos = 0
    private def peek(): Option[String] = if (pos < tokens.length) Some(tokens(pos)) else None
    private def take(): String = { val t = tokens(pos); pos += 1; t }

    private def primary(): Vector[Int] = {
      val t = take()
      if (t == "(") {
        val e = choice()
        require(take() == ")")
        e
      } else if (t == "&") { AND +: primarySuffixed() }
      else if (t == "!") { NOT +: primarySuffixed() }
      else if (t == ".") { Vector(LIT) }
      else if (t.startsWith("\"")) { if (t == "\"\"") Vector(EMPTY) else Vector(LIT) }
      else if (t.startsWith("[")) { Vector(LIT) }
      else { Vector(REF, ids(t)) }
    }

    private def primarySuffixed(): Vector[Int] = {
      var e = primary()
      while (peek().exists(s => s == "*" || s == "+" || s == "?")) {
        val op = take() match {
          case "*" => STAR
          case "+" => PLUS
          case _   => OPT
        }
        e = op +: e
      }
      e
    }

    private def seq(): Vector[Int] = {
      var e = primarySuffixed()
      while (peek().exists(s => s != "/" && s != ")")) {
        e = (SEQ +: e) ++ primarySuffixed()
      }
      e
    }

    private def choice(): Vector[Int] = {
      var e = seq()
      while (peek().contains("/")) {
        take()
        e = (ALT +: e) ++ seq()
      }
      e
    }

    def parse(): Vector[Int] = {
      val e = choice()
      require(pos == tokens.length, tokens.slice(pos, pos + 3).mkString(" "))
      e
    }
  }

  /** The grammar as prefix bytecode plus the rule name table. */
  final class Grammar(val names: Vector[String], val code: Array[Int], val start: Array[Int]) {
    val n: Int = names.length
    val ids: Map[String, Int] = names.zipWithIndex.toMap
  }

  /** Python の `line.split(b' = ', 1)` を通る行（規則行）だけを返す。 */
  private def ruleLines(text: String): Iterator[(String, String)] = {
    text.split('\n').iterator.flatMap { line =>
      val split = line.indexOf(" = ")
      if (split < 0) None else Some((line.substring(0, split).trim, line.substring(split + 3)))
    }
  }

  /** Pass A over the file text (Latin-1: one char per byte). */
  def load(text: String, log: String => Unit): Grammar = {
    val ids = mutable.LinkedHashMap.empty[String, Int]
    ruleLines(text).foreach { case (name, _) =>
      if (!ids.contains(name)) { ids(name) = ids.size }
    }
    val names = ids.keys.toVector
    val n = names.length
    log(s"rules $n")
    val idMap = ids.toMap
    val code = mutable.ArrayBuffer.empty[Int]
    val start = new Array[Int](n + 1)
    var i = 0
    ruleLines(text).foreach { case (_, body) =>
      val trimmed = body.reverse.dropWhile(c => c == ';' || c == '\r' || c == '\n' || c == ' ').reverse
      val tokens = TOK.findAllIn(trimmed).toVector
      start(i) = code.size
      code ++= new Parser(tokens, idMap).parse()
      i += 1
    }
    start(n) = code.size
    log(s"bytecode ints ${code.size}")
    new Grammar(names, code.toArray, start)
  }

  /** Compressed adjacency (CSR): `deg` holds offsets, `adj` the targets. */
  private final class Csr(val deg: Array[Int], val adj: Array[Int], val flags: Array[Byte])

  private def csr(n: Int, src: collection.IndexedSeq[Int], dst: collection.IndexedSeq[Int], flag: collection.IndexedSeq[Byte]): Csr = {
    val deg = new Array[Int](n + 1)
    src.foreach(s => deg(s + 1) += 1)
    for (i <- 0 until n) { deg(i + 1) += deg(i) }
    val pos = deg.take(n)
    val adj = new Array[Int](src.length)
    val flags = new Array[Byte](src.length)
    for (k <- src.indices) {
      val p = pos(src(k))
      adj(p) = dst(k)
      if (flag.nonEmpty) { flags(p) = flag(k) }
      pos(src(k)) = p + 1
    }
    new Csr(deg, adj, flags)
  }

  /** Result of the greatest-fixpoint pass. */
  final case class Consumption(consuming: Array[Boolean], evals: Int, flips: Int)

  /** must-consume of prefix bytecode code[lo:hi] under set C. */
  private def mustConsume(code: Array[Int], lo: Int, consuming: Array[Boolean]): Boolean = {
    def ev(k: Int): (Boolean, Int) = {
      val op = code(k)
      if (op == LIT) (true, k + 1)
      else if (op == EMPTY) (false, k + 1)
      else if (op == REF) (consuming(code(k + 1)), k + 2)
      else if (op == STAR || op == OPT || op == AND || op == NOT) { val (_, k2) = ev(k + 1); (false, k2) }
      else if (op == PLUS) ev(k + 1)
      else if (op == SEQ) { val (a, k2) = ev(k + 1); val (b, k3) = ev(k2); (a || b, k3) }
      else if (op == ALT) { val (a, k2) = ev(k + 1); val (b, k3) = ev(k2); (a && b, k3) }
      else throw new IllegalArgumentException(op.toString)
    }
    ev(lo)._1
  }

  /** Pass B: worklist greatest fixpoint over the reverse-dependency graph. */
  def consumption(g: Grammar, log: String => Unit): Consumption = {
    // reverse dependencies: for each rule, which rules reference it
    val rsrc = mutable.ArrayBuffer.empty[Int]
    val rdst = mutable.ArrayBuffer.empty[Int]
    for (r <- 0 until g.n) {
      var k = g.start(r)
      val hi = g.start(r + 1)
      while (k < hi) {
        if (g.code(k) == REF) { rsrc += g.code(k + 1); rdst += r; k += 2 }
        else { k += 1 }
      }
    }
    val reverse = csr(g.n, rsrc, rdst, Vector.empty)
    log(s"reverse edges ${rsrc.size}")
    val consuming = Array.fill(g.n)(true)
    val queued = Array.fill(g.n)(true)
    val work = mutable.ArrayBuffer.from(0 until g.n)
    var flips = 0
    var evals = 0
    while (work.nonEmpty) {
      val r = work.remove(work.size - 1)
      queued(r) = false
      evals += 1
      if (consuming(r) && !mustConsume(g.code, g.start(r), consuming)) {
        consuming(r) = false
        flips += 1
        for (i <- reverse.deg(r).until(reverse.deg(r + 1))) {
          val u = reverse.adj(i)
          if (consuming(u) && !queued(u)) { queued(u) = true; work += u }
        }
      }
    }
    log(s"worklist gfp: evals $evals, flips $flips, consuming rules ${consuming.count(identity)}")
    Consumption(consuming, evals, flips)
  }

  /** Result of the SCC pass. */
  final case class Sccs(reachable: Int, count: Int, nontrivial: Int, largest: Int,
      intraGuarded: Int, intraUnguarded: Int, largestSample: Vector[String])

  /** Pass C': full graph with per-edge consumption guard; SCCs; consuming edges inside SCCs. */
  def sccs(g: Grammar, consuming: Array[Boolean], log: String => Unit): Sccs = {
    val esrc = mutable.ArrayBuffer.empty[Int]
    val edst = mutable.ArrayBuffer.empty[Int]
    val eg = mutable.ArrayBuffer.empty[Byte]
    def walk(k: Int, pre: Boolean, r: Int): (Boolean, Int) = {
      val op = g.code(k)
      if (op == LIT) (true, k + 1)
      else if (op == EMPTY) (false, k + 1)
      else if (op == REF) {
        val d = g.code(k + 1)
        esrc += r; edst += d; eg += (if (pre) 1 else 0).toByte
        (consuming(d), k + 2)
      }
      else if (op == STAR || op == OPT || op == AND || op == NOT) { val (_, k2) = walk(k + 1, pre, r); (false, k2) }
      else if (op == PLUS) walk(k + 1, pre, r)
      else if (op == SEQ) { val (a, k2) = walk(k + 1, pre, r); val (b, k3) = walk(k2, pre || a, r); (a || b, k3) }
      else { val (a, k2) = walk(k + 1, pre, r); val (b, k3) = walk(k2, pre, r); (a && b, k3) }
    }
    for (r <- 0 until g.n) { walk(g.start(r), pre = false, r) }
    val edges = esrc.size
    log(s"edges $edges, guarded by consumption ${eg.count(_ == 1)}")
    val graph = csr(g.n, esrc, edst, eg)
    val tarjan = new Tarjan(g.n, graph)
    tarjan.run(g.ids("S"))
    val comp = tarjan.comp
    val compsize = tarjan.compsize
    val nontrivial = compsize.count(_ > 1)
    var intraG = 0
    var intraU = 0
    for (v <- 0 until g.n if tarjan.index(v) != -1; i <- graph.deg(v).until(graph.deg(v + 1))) {
      val w = graph.adj(i)
      if (comp(w) == comp(v)) {
        if (graph.flags(i) != 0) { intraG += 1 } else { intraU += 1 }
      }
    }
    val big = compsize.indices.maxBy(c => compsize(c)) // first maximum, as Python's max()
    val sample = (0 until g.n).filter(v => comp(v) == big).take(6).map(g.names).toVector
    Sccs(tarjan.reach, compsize.size, nontrivial, compsize.max, intraG, intraU, sample)
  }

  /** Iterative Tarjan restricted to nodes reachable from the start rule. */
  private final class Tarjan(n: Int, graph: Csr) {
    val index: Array[Int] = Array.fill(n)(-1)
    val low: Array[Int] = new Array[Int](n)
    val onStack: Array[Boolean] = new Array[Boolean](n)
    val comp: Array[Int] = Array.fill(n)(-1)
    val compsize: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty
    var reach: Int = 0

    def run(s: Int): Unit = {
      val stack = mutable.ArrayBuffer.empty[Int]
      var idx = 0
      var ncomp = 0
      val work = mutable.ArrayBuffer[(Int, Int)]((s, graph.deg(s)))
      index(s) = idx; low(s) = idx; idx += 1; stack += s; onStack(s) = true
      while (work.nonEmpty) {
        val (v, i) = work(work.size - 1)
        if (i < graph.deg(v + 1)) {
          work(work.size - 1) = (v, i + 1)
          val w = graph.adj(i)
          if (index(w) == -1) {
            index(w) = idx; low(w) = idx; idx += 1; stack += w; onStack(w) = true
            work += ((w, graph.deg(w)))
          } else if (onStack(w) && index(w) < low(v)) {
            low(v) = index(w)
          }
        } else {
          work.remove(work.size - 1)
          if (work.nonEmpty) {
            val u = work(work.size - 1)._1
            if (low(v) < low(u)) { low(u) = low(v) }
          }
          if (low(v) == index(v)) {
            var size = 0
            var more = true
            while (more) {
              val w = stack.remove(stack.size - 1)
              onStack(w) = false
              comp(w) = ncomp
              size += 1
              if (w == v) { more = false }
            }
            compsize += size
            ncomp += 1
          }
        }
      }
      reach = idx
    }
  }

  /** Run the whole script on a file; returns the text it prints.  `now` is the clock in
    * seconds (defaults to wall-clock time, as `time.time()`).
    */
  def run(path: Path, now: () => Double = () => System.currentTimeMillis() / 1000.0): String = {
    val t0 = now()
    val out = new StringBuilder
    def timed(line: String): Unit = { out.append(s"$line ${PyFormat.fixed(now() - t0, 0)}s\n") }
    val text = new String(Files.readAllBytes(path), StandardCharsets.ISO_8859_1)
    val g = load(text, timed)
    val Consumption(consuming, _, _) = consumption(g, timed)
    val result = sccs(g, consuming, timed)
    out.append(s"reachable from S: ${result.reachable} rules; SCCs: ${result.count}, " +
      s"nontrivial (size>1): ${result.nontrivial}, largest: ${result.largest}\n")
    timed(s"edges inside SCCs: consuming-guarded ${result.intraGuarded}, unguarded ${result.intraUnguarded}")
    out.append(s"sample rules of the largest SCC: ${PyFormat.listRepr(result.largestSample.map(PyFormat.strRepr))}\n")
    out.toString
  }

  def main(args: Array[String]): Unit = {
    print(run(Path.of(args(0))))
  }
}
