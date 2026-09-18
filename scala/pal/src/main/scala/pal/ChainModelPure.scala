package pal

/** 純関数版のチェーン参照モデル。
  *
  * `ScaffoldChain.ChainView` は回路を組み立てる手続き型の実装で、`mode` や 7 本の
  * カウンタを破壊的に更新する。Lean 側（`lean-pal/PalPeg/GalilScaffoldTopChainVM.lean`）は
  * それを帰納的な**関係** `ChainStep` / `ChainMatched` で写している。
  *
  * この非対称が原因でモデル欠陥が 2 件出た（2026-09-18〜19）:
  *
  *   - `M-periodOnly` — `start()` の `periodOnly = false` と `cycle.reset()` が Lean に無い。
  *   - `M-watchBreak` — `step()` の `case Mode.Watch if lag.sign > 0 => if (consume()) …` で
  *     `consume()` が不一致なら `mode = Mode.Broken` にする経路が `ChainStep` に無い。
  *     その穴を埋めるために `WatchOk.good`（＝予測は常に当たる）という**偽の仮定**が
  *     書かれていた（`PalPeg.WatchOkRefute.watchOk_false` で反証済み）。
  *
  * **関係は構成子を 1 つ忘れても型検査を通る。全域関数は網羅性検査で落ちる。**
  * だから遷移をまず純関数として書き、Lean へは丸写しし、関係はその関数から導く。
  *
  * このファイルは Lean の型と**同じ形**に作ってある（`Ctr` ↔ `Counter`、`Token` ↔
  * `GalilScaffoldChainPeriod.Token`、`Tape` ↔ `…Period.Tape`、`Consume` ↔
  * `GalilScaffoldChainConsume`、`Chain` ↔ `ChainVM`）。写すときに形を変えない。
  *
  * 入力ヘッドは抽象化してある: チェーンが読むのは「動かした verifier の下の記号」
  * （`Option[Int]`、`None` は入力の終端）と「walker の下の DP 一進答」だけなので、
  * それを引数として受ける。こうすると `step` は入力テープの表現に依存しない全域関数になる。
  */
object ChainModelPure {

  /** 双スタック一進カウンタ。Lean の `Counter` は `List Unit` 2 本だが、
    * `List Unit` は自然数と同型なので長さで写す。 */
  final case class Ctr(pos: Int, neg: Int) {
    def value: Int = pos - neg
    def inc: Ctr = if (neg > 0) { Ctr(pos, neg - 1) } else { Ctr(pos + 1, neg) }
    def dec: Ctr = if (pos > 0) { Ctr(pos - 1, neg) } else { Ctr(pos, neg + 1) }
    /** Lean の `positive`: 正側スタックが空でない。 */
    def positive: Boolean = pos > 0
    /** Lean の `zero`: 両側が空。 */
    def isZero: Boolean = pos == 0 && neg == 0
    def negative: Boolean = neg > 0
    /** Lean の `Canonical`: 片側が空。 */
    def canonical: Boolean = pos == 0 || neg == 0
    def decFour: Ctr = dec.dec.dec.dec
  }

  object Ctr {
    val reset: Ctr = Ctr(0, 0)
    def ofNat(n: Int): Ctr = Ctr(n, 0)
  }

  /** period テープの記号。Lean の `GalilScaffoldChainPeriod.Token`。 */
  enum Token {
    case Blank
    case Left
    case Plain(a: Int)
    case First(a: Int)
    case Last(a: Int)
  }

  object Token {
    /** Lean の `symbol`: 記号を持つ token だけが `Some`。 */
    def symbol(t: Token): Option[Int] = t match {
      case Token.Plain(a) => Some(a)
      case Token.First(a) => Some(a)
      case Token.Last(a) => Some(a)
      case Token.Blank => None
      case Token.Left => None
    }
    def isFirst(t: Token): Boolean = t match {
      case Token.First(_) => true
      case _ => false
    }
    def isLast(t: Token): Boolean = t match {
      case Token.Last(_) => true
      case _ => false
    }
  }

  /** 焦点つきの period テープ。Lean の `…Period.Tape`。 */
  final case class Tape(left: List[Token], focus: Token, right: List[Token]) {
    def moveRight: Tape = right match {
      case Nil => Tape(focus :: left, Token.Blank, Nil)
      case t :: ts => Tape(focus :: left, t, ts)
    }
    def moveLeft: Tape = left match {
      case Nil => Tape(Nil, Token.Blank, focus :: right)
      case t :: ts => Tape(ts, t, focus :: right)
    }
    /** `period.write(x)`: 焦点を書き換える。 */
    def write(t: Token): Tape = Tape(left, t, right)
  }

  object Tape {
    /** `start()` の直後: 中心の記号を `First` として置く。 */
    def start(c: Int): Tape = Tape(Nil, Token.First(c), Nil)
  }

  /** consume の制御状態。Lean の `GalilScaffoldChainConsume.State`。 */
  final case class Consume(
      period: Tape,
      distance: Ctr,
      boundary: Ctr,
      last: Ctr,
      phase: Int,
      forward: Boolean,
      broken: Boolean
  )

  object Consume {
    def advancePhase(p: Int): Int = if (p + 1 < 4) { p + 1 } else { 4 }

    /** **Scala 正本 `ScaffoldChain.consume()` の純関数版。**
      *
      * 手続き型の `consume()` は `verifier.right()` を先に済ませてから
      * `verifier.read()` と `period.read()` を比べ、食い違えば `mode = Mode.Broken` にして
      * `false` を返す。ここでは `seen` が「動かした verifier の下の記号」。
      *
      * 返り値の `broken` が `true` のときが「`false` を返した」場合にあたる。
      */
    def step(s: Consume, seen: Option[Int]): Consume = {
      val same = Token.symbol(s.period.focus) match {
        case None => false
        case Some(a) => seen == Some(a)
      }
      if (same) {
        val distance = s.distance.inc
        val boundaryEvent = Token.isFirst(s.period.focus) || Token.isLast(s.period.focus)
        val forward = if (boundaryEvent) { Token.isFirst(s.period.focus) } else { s.forward }
        Consume(
          period = if (forward) { s.period.moveRight } else { s.period.moveLeft },
          distance = distance,
          boundary = if (boundaryEvent) { distance } else { s.boundary },
          last = if (boundaryEvent) { s.boundary } else { s.last },
          phase = if (boundaryEvent) { advancePhase(s.phase) } else { s.phase },
          forward = forward,
          broken = s.broken
        )
      } else {
        s.copy(broken = true)
      }
    }
  }

  /** watch 相の状態。Lean の `GalilScaffoldChainWatch.State`（`machine` の verifier は
    * 抽象化して外に出してある）。 */
  final case class Watch(control: Consume, lag: Ctr, margin: Ctr)

  /** チェーン全体。Lean の `ChainVM` と同じ 5 構成子。 */
  enum Chain {
    case Idle
    case Copy(h: Ctr, period: Tape, lag: Ctr, margin: Ctr)
    case Back(period: Tape, h: Ctr, lag: Ctr, margin: Ctr)
    case Watching(w: Watch)
    case Broken(w: Watch)
  }

  /** `watchControl`: Back の終わりに入る watch の制御。Lean の `watchControl` と同形。 */
  def watchControl(period: Tape): Consume =
    Consume(period.moveRight, Ctr.reset, Ctr.reset, Ctr.reset, 0, true, false)

  /** `chain.start()`。`periodOnly = false` と `cycle.reset()` は呼び出し側（VM）が持つので
    * ここには現れない（`M-periodOnly` の在り処）。 */
  def start(c: Int, radius: Ctr): Chain =
    Chain.Copy(Ctr.reset, Tape.start(c), radius, radius)

  /** copy 相で読む DP 一進答。`One` が `"1"`、`LeftMark` が `LEFT`。 */
  enum Answer {
    case One(sym: Int)
    case LeftMark
  }

  /** **`ScaffoldChain.step(answer)` の純関数版。**
    *
    * `answer` は copy 相でのみ参照され、`seen` は watch 相でのみ参照される。
    * `None` を渡した相で使われることはない（`Left` で返す）。
    *
    * **この関数が全域であることが眼目。** 5 構成子 × 相ごとの条件をすべて列挙するので、
    * Lean 側で `ChainStep` を書くときに場合を落とせない。`M-watchBreak` はまさに
    * `Watching` かつ正 lag かつ不一致の枝が落ちていた欠陥だった。
    */
  def step(
      x: Chain,
      answer: Option[Answer],
      seen: Option[Int]
  ): Either[String, Chain] = x match {
    case Chain.Idle => Right(Chain.Idle)
    case Chain.Broken(w) => Right(Chain.Broken(w))
    case Chain.Copy(h, period, lag, margin) =>
      answer match {
        case Some(Answer.One(sym)) =>
          // walker.left(); period.move(1); period.write(symbol)
          Right(Chain.Copy(h.inc, period.moveRight.write(Token.Plain(sym)), lag, margin.decFour))
        case Some(Answer.LeftMark) =>
          if (h.positive) {
            // period.write(TAIL_MARK + period.read()); mode = Back
            val tail = Token.symbol(period.focus) match {
              case Some(a) => Token.Last(a)
              case None => Token.Blank
            }
            Right(Chain.Back(period.write(tail), h, lag, margin))
          } else {
            Left("positive unary DP answer required")
          }
        case None => Left("copy phase needs the DP answer")
      }
    case Chain.Back(period, h, lag, margin) =>
      if (Token.isFirst(period.focus)) {
        // period.move(1); mode = Watch
        Right(Chain.Watching(Watch(watchControl(period), lag, margin)))
      } else {
        Right(Chain.Back(period.moveLeft, h, lag, margin))
      }
    case Chain.Watching(w) =>
      if (w.lag.positive) {
        seen match {
          case None => Left("watch phase needs the verifier symbol")
          case Some(_) =>
            val c = Consume.step(w.control, seen)
            if (c.broken && !w.control.broken) {
              // consume() が false を返した: mode = Broken、lag.dec() は飛ぶ
              Right(Chain.Broken(Watch(c, w.lag, w.margin)))
            } else {
              // consume() が true を返した: lag.dec()
              Right(Chain.Watching(Watch(c, w.lag.dec, w.margin)))
            }
        }
      } else {
        // `case Mode.Idle | Mode.Watch | Mode.Broken => ()`
        Right(Chain.Watching(w))
      }
  }

  /** **`ScaffoldChain.matched()` の純関数版。** 新しい place が合流したとき。
    *
    * `margin.inc()` は**相に関係なく**行われ、`mode == Watch && lag.sign == 0` のときだけ
    * `consume()` を呼び、さもなくば `lag.inc()`。`Broken` でもカウンタは動く
    * （Lean の `ChainMatched.brokenMatched` に対応。これも欠けていた）。
    *
    * `periodOnly` のときの `cycle.dec()` は VM 側が持つのでここには現れない。
    */
  def matched(x: Chain, seen: Option[Int]): Either[String, Chain] = x match {
    case Chain.Idle => Right(Chain.Idle)
    case Chain.Copy(h, period, lag, margin) =>
      Right(Chain.Copy(h, period, lag.inc, margin.inc))
    case Chain.Back(period, h, lag, margin) =>
      Right(Chain.Back(period, h, lag.inc, margin.inc))
    case Chain.Broken(w) =>
      Right(Chain.Broken(Watch(w.control, w.lag.inc, w.margin.inc)))
    case Chain.Watching(w) =>
      val margin = w.margin.inc
      if (w.lag.isZero) {
        seen match {
          case None => Left("matched at zero lag needs the verifier symbol")
          case Some(_) =>
            val c = Consume.step(w.control, seen)
            if (c.broken && !w.control.broken) {
              Right(Chain.Broken(Watch(c, w.lag, margin)))
            } else {
              Right(Chain.Watching(Watch(c, w.lag, margin)))
            }
        }
      } else {
        Right(Chain.Watching(Watch(w.control, w.lag.inc, margin)))
      }
  }

  /** `chain.shiftOne()`: 中心が 1 place 動いたときの相対カウンタ補正。
    * `cycle.inc()` 2 回は VM 側。 */
  def shiftOne(x: Chain): Chain = x match {
    case Chain.Idle => Chain.Idle
    case Chain.Copy(h, period, lag, margin) => Chain.Copy(h, period, lag, margin.dec)
    case Chain.Back(period, h, lag, margin) => Chain.Back(period, h, lag, margin.dec)
    case Chain.Watching(w) =>
      Chain.Watching(
        Watch(
          w.control.copy(
            distance = w.control.distance.dec,
            boundary = w.control.boundary.dec,
            last = w.control.last.dec
          ),
          w.lag,
          w.margin.dec
        )
      )
    case Chain.Broken(w) =>
      Chain.Broken(
        Watch(
          w.control.copy(
            distance = w.control.distance.dec,
            boundary = w.control.boundary.dec,
            last = w.control.last.dec
          ),
          w.lag,
          w.margin.dec
        )
      )
  }

  /** `prediction()`: watch で lag が 0 のときだけ予測記号を出す。 */
  def prediction(x: Chain): Option[Int] = x match {
    case Chain.Watching(w) if w.lag.isZero => Token.symbol(w.control.period.focus)
    case _ => None
  }

  /** `canShift` の相依存部分。`periodOnly` と `cycle` は VM 側が持つので、
    * ここでは `mode == Watch && lag.sign == 0 && phase == 4` だけを返す。 */
  def shiftReady(x: Chain): Boolean = x match {
    case Chain.Watching(w) => w.lag.isZero && w.control.phase == 4
    case _ => false
  }

  /** 相が生きているか（`ChainVM` が `Idle` でも `Broken` でもない）。 */
  def live(x: Chain): Boolean = x match {
    case Chain.Idle => false
    case Chain.Broken(_) => false
    case _ => true
  }
}
