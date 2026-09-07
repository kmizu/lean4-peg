package pal

import java.nio.file.Path

import GrammarTools.{ByteLines, ByteVec, IntVec, StringIndex}

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
  *
  * ==規模==
  *
  * 実物の文法は 13,248,052 規則・672 MB（bytecode 210,830,100 int、辺 72,376,872 本）。
  * Python 版と同じく、ファイルは 2 回逐次に読み（名前表 → bytecode）、bytecode と辺は
  * ボクシングしない配列（`GrammarTools.IntVec` = `array('i')`）に置く。Python は
  * `sys.setrecursionlimit(100000)` で再帰評価するが、ここでは明示的なスタックで反復する
  * （`Evaluator`）ので、長い列（SEQ の左結合で深く入れ子になる）でもスタックを使わない。
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

  /** Prefix bytecode: op [arg]; SEQ/ALT are binary: SEQ a b.
    *
    * Python builds each rule as a list by prepending (`[SEQ] + e + f`); here the same
    * layout is produced in a reusable scratch vector by inserting the operator at the
    * start of the operand it wraps, so parsing allocates nothing per rule but the tokens.
    */
  private final class Parser(index: StringIndex) {
    private var tokens: Array[String] = Array.empty
    private var pos = 0
    private val out = new IntVec(64)

    private def peek(): String = if (pos < tokens.length) tokens(pos) else null
    private def take(): String = { val t = tokens(pos); pos += 1; t }

    private def primary(): Unit = {
      val t = take()
      if (t == "(") {
        choice()
        assert(take() == ")")
      } else if (t == "&") {
        val at = out.size
        primarySuffixed()
        out.insert(at, AND)
      } else if (t == "!") {
        val at = out.size
        primarySuffixed()
        out.insert(at, NOT)
      } else if (t == ".") { out += LIT }
      else if (t.charAt(0) == '"') { out += (if (t == "\"\"") EMPTY else LIT) }
      else if (t.charAt(0) == '[') { out += LIT }
      else { out += REF; out += index(t) }
    }

    private def primarySuffixed(): Unit = {
      val at = out.size
      primary()
      var suffix = peek()
      while (suffix == "*" || suffix == "+" || suffix == "?") {
        take()
        out.insert(at, if (suffix == "*") STAR else if (suffix == "+") PLUS else OPT)
        suffix = peek()
      }
    }

    /** `[SEQ] + e + f`, left-nested, is `SEQ` × (m-1) followed by the m elements: one
      * shift per sequence instead of one per element (Python's list concatenation is
      * quadratic in the sequence length; the real grammar has long sequences).
      */
    private def seq(): Unit = {
      val at = out.size
      primarySuffixed()
      var elements = 1
      var next = peek()
      while (next != null && next != "/" && next != ")") {
        primarySuffixed()
        elements += 1
        next = peek()
      }
      if (elements > 1) { out.insertRepeated(at, SEQ, elements - 1) }
    }

    private def choice(): Unit = {
      val at = out.size
      seq()
      var alternatives = 1
      while (peek() == "/") {
        take()
        seq()
        alternatives += 1
      }
      if (alternatives > 1) { out.insertRepeated(at, ALT, alternatives - 1) }
    }

    /** Parse one rule body; the result is valid until the next call. */
    def parse(bodyTokens: Array[String]): IntVec = {
      tokens = bodyTokens
      pos = 0
      out.clear()
      choice()
      assert(pos == tokens.length, tokens.slice(pos, pos + 3).mkString(" "))
      out
    }
  }

  /** The grammar as prefix bytecode plus the rule name table (`ids` / `names`). */
  final class Grammar(val index: StringIndex, val code: IntVec, val start: Array[Int]) {
    val n: Int = index.size
    def name(id: Int): String = index.name(id)
    def id(name: String): Int = index(name)
  }

  /** `line.split(b' = ', 1)`: the (name, body) of a rule line, or null. */
  private def splitRule(line: String): (String, String) = {
    val at = line.indexOf(" = ")
    if (at < 0) null else (line.substring(0, at).trim, line.substring(at + 3))
  }

  /** `body.rstrip(b';\r\n ')` */
  private def rstripBody(body: String): String = {
    var end = body.length
    while (end > 0 && { val c = body.charAt(end - 1); c == ';' || c == '\r' || c == '\n' || c == ' ' }) { end -= 1 }
    body.substring(0, end)
  }

  /** Pass A: two streaming passes over the file — the name table, then the bytecode. */
  def load(path: Path, log: String => Unit): Grammar = {
    val index = new StringIndex()
    ByteLines.foreach(path) { line =>
      val rule = splitRule(line)
      if (rule != null) { index.intern(rule._1) }
    }
    val n = index.size
    log(s"rules $n")
    val code = new IntVec(1 << 20)
    val start = new Array[Int](n + 1)
    val parser = new Parser(index)
    var i = 0
    ByteLines.foreach(path) { line =>
      val rule = splitRule(line)
      if (rule != null) {
        val tokens = TOK.findAllIn(rstripBody(rule._2)).toArray
        start(i) = code.size
        code ++= parser.parse(tokens)
        i += 1
      }
    }
    start(n) = code.size
    log(s"bytecode ints ${code.size}")
    new Grammar(index, code, start)
  }

  /** Compressed adjacency (CSR): `deg` holds offsets, `adj` the targets, `flags` the
    * per-edge guard (empty for the reverse graph).
    */
  private final class Csr(val deg: Array[Int], val adj: Array[Int], val flags: Array[Byte])

  private def csr(n: Int, src: IntVec, dst: IntVec, flag: ByteVec): Csr = {
    val deg = new Array[Int](n + 1)
    var k = 0
    while (k < src.size) { deg(src(k) + 1) += 1; k += 1 }
    var i = 0
    while (i < n) { deg(i + 1) += deg(i); i += 1 }
    val pos = java.util.Arrays.copyOf(deg, n)
    val adj = new Array[Int](src.size)
    val flags = if (flag == null) Array.empty[Byte] else new Array[Byte](src.size)
    k = 0
    while (k < src.size) {
      val p = pos(src(k))
      adj(p) = dst(k)
      if (flag != null) { flags(p) = flag(k) }
      pos(src(k)) = p + 1
      k += 1
    }
    new Csr(deg, adj, flags)
  }

  /** Iterative evaluation of prefix bytecode with an explicit frame stack (Python's `ev`
    * and `walk` are recursive under `sys.setrecursionlimit(100000)`).
    *
    * Semantics: LIT = true, EMPTY = false, REF = C[target]; STAR/OPT/AND/NOT = false,
    * PLUS = child, SEQ = a or b, ALT = a and b.  `walk` additionally records every REF as
    * an edge tagged with `pre` = "something earlier in the enclosing sequence must
    * consume" (the second operand of SEQ sees `pre or a`).
    */
  private final class Evaluator(code: IntVec, consuming: Array[Boolean]) {
    private val ops = new IntVec(64)
    private val firstValues = new IntVec(64) // -1 while the first operand is being evaluated
    private val pres = new IntVec(64) // the `pre` in force when the frame was pushed

    /** Edge sinks used by `walk`; null for `mustConsume`. */
    var edgeSrc: IntVec = null
    var edgeDst: IntVec = null
    var edgeGuard: ByteVec = null

    /** must-consume of the expression starting at `lo`. */
    def mustConsume(lo: Int): Boolean = run(lo, -1)

    /** Like `mustConsume`, recording the reference edges of rule `r`. */
    def walk(lo: Int, r: Int): Boolean = run(lo, r)

    private def isUnary(op: Int): Boolean = op == STAR || op == OPT || op == AND || op == NOT || op == PLUS

    /** The `pre` for the operand about to be evaluated under the top frame. */
    private def currentPre(): Boolean = {
      if (ops.isEmpty) { false }
      else {
        val framePre = pres.last == 1
        if (ops.last == SEQ && firstValues.last != -1) framePre || firstValues.last == 1 else framePre
      }
    }

    private def run(lo: Int, rule: Int): Boolean = {
      ops.clear(); firstValues.clear(); pres.clear()
      var k = lo
      var pre = false
      var value = false
      var result = false
      var done = false
      while (!done) {
        val op = code(k)
        var haveValue = true
        if (op == LIT) { value = true; k += 1 }
        else if (op == EMPTY) { value = false; k += 1 }
        else if (op == REF) {
          val d = code(k + 1)
          if (rule >= 0) { edgeSrc += rule; edgeDst += d; edgeGuard += (if (pre) 1 else 0).toByte }
          value = consuming(d)
          k += 2
        } else if (isUnary(op) || op == SEQ || op == ALT) {
          ops += op; firstValues += -1; pres += (if (pre) 1 else 0)
          k += 1
          haveValue = false
        } else { throw new IllegalArgumentException(op.toString) }
        // unwind: hand the value to the enclosing frames
        while (haveValue) {
          if (ops.isEmpty) { result = value; done = true; haveValue = false }
          else {
            val top = ops.last
            if (isUnary(top)) {
              ops.pop(); firstValues.pop(); pres.pop()
              if (top != PLUS) { value = false }
            } else if (firstValues.last == -1) { // first operand done: evaluate the second
              firstValues(firstValues.size - 1) = if (value) 1 else 0
              haveValue = false
            } else {
              val a = firstValues.last == 1
              ops.pop(); firstValues.pop(); pres.pop()
              value = if (top == SEQ) a || value else a && value
            }
          }
        }
        pre = currentPre()
      }
      result
    }
  }

  /** Result of the greatest-fixpoint pass. */
  final case class Consumption(consuming: Array[Boolean], evals: Int, flips: Int)

  /** Reverse dependencies: for each rule, which rules reference it (edge lists are
    * dropped once the CSR form exists, like Python's `del rsrc, rdst`).
    */
  private def reverseGraph(g: Grammar): (Csr, Int) = {
    val rsrc = new IntVec(1 << 20)
    val rdst = new IntVec(1 << 20)
    var r = 0
    while (r < g.n) {
      var k = g.start(r)
      val hi = g.start(r + 1)
      while (k < hi) {
        if (g.code(k) == REF) { rsrc += g.code(k + 1); rdst += r; k += 2 }
        else { k += 1 }
      }
      r += 1
    }
    (csr(g.n, rsrc, rdst, null), rsrc.size)
  }

  /** Pass B: worklist greatest fixpoint over the reverse-dependency graph. */
  def consumption(g: Grammar, log: String => Unit): Consumption = {
    val (reverse, reverseEdges) = reverseGraph(g)
    log(s"reverse edges $reverseEdges")
    val consuming = Array.fill(g.n)(true)
    val queued = Array.fill(g.n)(true)
    val work = new IntVec(g.n)
    var r = 0
    while (r < g.n) { work += r; r += 1 }
    val evaluator = new Evaluator(g.code, consuming)
    var flips = 0
    var evals = 0
    while (work.nonEmpty) {
      val rule = work.pop()
      queued(rule) = false
      evals += 1
      if (consuming(rule) && !evaluator.mustConsume(g.start(rule))) {
        consuming(rule) = false
        flips += 1
        var i = reverse.deg(rule)
        while (i < reverse.deg(rule + 1)) {
          val u = reverse.adj(i)
          if (consuming(u) && !queued(u)) { queued(u) = true; work += u }
          i += 1
        }
      }
    }
    log(s"worklist gfp: evals $evals, flips $flips, consuming rules ${consuming.count(identity)}")
    Consumption(consuming, evals, flips)
  }

  /** Result of the SCC pass. */
  final case class Sccs(reachable: Int, count: Int, nontrivial: Int, largest: Int,
      intraGuarded: Int, intraUnguarded: Int, largestSample: Vector[String])

  /** Full graph with per-edge consumption guard; the edge lists die with this call. */
  private def forwardGraph(g: Grammar, consuming: Array[Boolean], log: String => Unit): Csr = {
    val evaluator = new Evaluator(g.code, consuming)
    evaluator.edgeSrc = new IntVec(1 << 20)
    evaluator.edgeDst = new IntVec(1 << 20)
    evaluator.edgeGuard = new ByteVec(1 << 20)
    var r = 0
    while (r < g.n) { evaluator.walk(g.start(r), r); r += 1 }
    log(s"edges ${evaluator.edgeSrc.size}, guarded by consumption ${evaluator.edgeGuard.countNonZero}")
    csr(g.n, evaluator.edgeSrc, evaluator.edgeDst, evaluator.edgeGuard)
  }

  /** Pass C': SCCs of the graph reachable from S; consuming edges inside SCCs. */
  def sccs(g: Grammar, consuming: Array[Boolean], log: String => Unit): Sccs = {
    val graph = forwardGraph(g, consuming, log)
    val tarjan = new Tarjan(g.n, graph)
    tarjan.run(g.id("S"))
    val comp = tarjan.comp
    val compsize = tarjan.compsize
    var nontrivial = 0
    var largest = 0
    var big = 0
    var c = 0
    while (c < compsize.size) {
      if (compsize(c) > 1) { nontrivial += 1 }
      if (compsize(c) > largest) { largest = compsize(c); big = c } // first maximum, as Python's max()
      c += 1
    }
    var intraG = 0
    var intraU = 0
    var v = 0
    while (v < g.n) {
      if (tarjan.index(v) != -1) {
        var i = graph.deg(v)
        while (i < graph.deg(v + 1)) {
          if (comp(graph.adj(i)) == comp(v)) {
            if (graph.flags(i) != 0) { intraG += 1 } else { intraU += 1 }
          }
          i += 1
        }
      }
      v += 1
    }
    val sample = Vector.newBuilder[String]
    v = 0
    var taken = 0
    while (v < g.n && taken < 6) {
      if (comp(v) == big) { sample += g.name(v); taken += 1 }
      v += 1
    }
    Sccs(tarjan.reach, compsize.size, nontrivial, largest, intraG, intraU, sample.result())
  }

  /** Iterative Tarjan restricted to nodes reachable from the start rule. */
  private final class Tarjan(n: Int, graph: Csr) {
    val index: Array[Int] = Array.fill(n)(-1)
    val low: Array[Int] = new Array[Int](n)
    val onStack: Array[Boolean] = new Array[Boolean](n)
    val comp: Array[Int] = Array.fill(n)(-1)
    val compsize: IntVec = new IntVec(1 << 16)
    var reach: Int = 0

    def run(s: Int): Unit = {
      val stack = new IntVec(1 << 16)
      val workNode = new IntVec(1 << 16) // the DFS stack as two parallel vectors: (v, i)
      val workEdge = new IntVec(1 << 16)
      var idx = 0
      var ncomp = 0
      workNode += s; workEdge += graph.deg(s)
      index(s) = idx; low(s) = idx; idx += 1; stack += s; onStack(s) = true
      while (workNode.nonEmpty) {
        val v = workNode.last
        val i = workEdge.last
        if (i < graph.deg(v + 1)) {
          workEdge(workEdge.size - 1) = i + 1
          val w = graph.adj(i)
          if (index(w) == -1) {
            index(w) = idx; low(w) = idx; idx += 1; stack += w; onStack(w) = true
            workNode += w; workEdge += graph.deg(w)
          } else if (onStack(w) && index(w) < low(v)) {
            low(v) = index(w)
          }
        } else {
          workNode.pop(); workEdge.pop()
          if (workNode.nonEmpty) {
            val u = workNode.last
            if (low(v) < low(u)) { low(u) = low(v) }
          }
          if (low(v) == index(v)) {
            var size = 0
            var more = true
            while (more) {
              val w = stack.pop()
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

  /** The whole script: the lines it prints are handed to `emit` as they are produced
    * (Python prints with `flush=True`); `now` is the clock in seconds (`time.time()`).
    */
  def analyze(path: Path, now: () => Double, emit: String => Unit): Unit = {
    val t0 = now()
    def timed(line: String): Unit = { emit(s"$line ${PyFormat.fixed(now() - t0, 0)}s") }
    val g = load(path, timed)
    val Consumption(consuming, _, _) = consumption(g, timed)
    val result = sccs(g, consuming, timed)
    emit(s"reachable from S: ${result.reachable} rules; SCCs: ${result.count}, " +
      s"nontrivial (size>1): ${result.nontrivial}, largest: ${result.largest}")
    timed(s"edges inside SCCs: consuming-guarded ${result.intraGuarded}, unguarded ${result.intraUnguarded}")
    emit(s"sample rules of the largest SCC: ${PyFormat.listRepr(result.largestSample.map(PyFormat.strRepr))}")
  }

  /** Run the whole script on a file; returns the text it prints. */
  def run(path: Path, now: () => Double = () => System.currentTimeMillis() / 1000.0): String = {
    val out = new StringBuilder
    analyze(path, now, line => { out.append(line).append('\n'); () })
    out.toString
  }

  def main(args: Array[String]): Unit = {
    analyze(Path.of(args(0)), () => System.currentTimeMillis() / 1000.0, println)
  }
}
