package pal

import scala.collection.mutable

/** Fischer–Paterson Algorithm Y, with local heads and unary counters.
  *
  * Source: String-Matching and Other Products, MIT MAC TM-41 (1974),
  * section 3, printed pp. 6–11. This is an executable multihead-tape
  * experiment, NOT a single-head TM transition table or a PAL PEG.
  *
  * The array P stores border length minus one, with P(-1) = P(0) = -1.
  * Instead of storing P, Y holds 0 1^delta(-1) 0 1^delta(0) ...,
  * where delta(i) = 1 + P(i) - P(i+1). Its total size is linear.
  * The two Y heads share an append-only tape. No head address is read by
  * the algorithm; the final A address is decoded only by the result observer.
  * All reads, writes and unit moves are charged, including unary-counter
  * copy/reset work. Input loading is supplied offline, not charged here.
  *
  * Python 原典: `fpp_tape.py`。Python 版はテープ記号に `object()` の番兵と int 0/1 と
  * 入力文字を混在させる。ここでは `Symbol` ADT で閉じる。
  */
object FppTape {

  final case class Result(border: Int, operations: Int, borders: Vector[Int] = Vector.empty)

  /** A cell content of any of the experiment's tapes. */
  sealed trait Symbol
  object Symbol {
    case object Left extends Symbol
    case object End extends Symbol
    case object Blank extends Symbol
    /** The unary/delta digits `0` and `1`. */
    final case class Bit(value: Int) extends Symbol
    /** One input character. */
    final case class Letter(char: Char) extends Symbol
    /** The fresh separator of `initial_palindromes` (Python's `object()`), equal to nothing else. */
    case object Separator extends Symbol
  }
  import Symbol.*

  val LEFT: Symbol = Left
  val END: Symbol = End
  val BLANK: Symbol = Blank
  val ZERO: Symbol = Bit(0)
  val ONE: Symbol = Bit(1)

  /** Python の `dict` テープ（局所ヘッドが共有できる）。 */
  type Cells = mutable.HashMap[Int, Symbol]

  def cells(pairs: (Int, Symbol)*): Cells = mutable.HashMap.from(pairs)

  final class Clock {
    var operations: Int = 0
  }

  /** VM implementation only: program control sees symbols, never positions. */
  final class Head(tape: Cells, val clock: Clock, private var position: Int = 0) {

    def read(): Symbol = {
      clock.operations += 1
      tape.getOrElse(position, Blank)
    }

    def write(symbol: Symbol): Unit = {
      clock.operations += 1
      tape.update(position, symbol)
    }

    def move(direction: Int): Unit = {
      assert(direction == -1 || direction == 1)
      clock.operations += 1
      position += direction
      assert(position >= 0)
    }

    /** Observer only (Python の `_position`): never consulted by machine control. */
    def observedPosition: Int = position
  }

  /** A unary counter on its own tape: `^ 1^k`, head at the top. */
  final class Unary(clock: Clock) {
    val head: Head = new Head(cells(0 -> Left), clock)

    def nonzero: Boolean = head.read() != Left

    def push(): Unit = {
      head.move(1)
      head.write(ONE)
    }

    def pop(): Unit = {
      assert(nonzero)
      head.write(Blank)
      head.move(-1)
    }

    def copyToEmpty(target: Unary): Unit = {
      assert(!target.nonzero)
      // Read backwards without erasing S; T's write head stays at its top.
      while (head.read() != Left) {
        target.push()
        head.move(-1)
      }
      // Restore S's head by scanning to the first blank and stepping back.
      head.move(1)
      while (head.read() != Blank) {
        head.move(1)
      }
      head.move(-1)
    }
  }

  /** Two independent single-head stacks; each entry transfers at most once. */
  final class TapeQueue(clock: Clock) {
    val back: Head = new Head(cells(0 -> Left), clock)
    val front: Head = new Head(cells(0 -> Left), clock)

    def append(symbol: Symbol): Unit = {
      back.move(1)
      back.write(symbol)
    }

    def take(): Symbol = {
      if (front.read() == Left) {
        while (back.read() != Left) {
          val symbol = back.read()
          back.write(Blank)
          back.move(-1)
          front.move(1)
          front.write(symbol)
        }
      }
      val symbol = front.read()
      assert(symbol != Left, "reader overtook the delta writer")
      front.write(Blank)
      front.move(-1)
      symbol
    }
  }

  /** Materialize the append stream only on first visiting a blank cell. */
  final class DeltaReader(clock: Clock, queue: TapeQueue) {
    val head: Head = new Head(cells(0 -> ZERO, 1 -> ONE, 2 -> ZERO), clock)

    def move(direction: Int): Unit = { head.move(direction) }

    def read(): Symbol = {
      var symbol = head.read()
      if (symbol == Blank) {
        symbol = queue.take()
        head.write(symbol)
      }
      symbol
    }
  }

  /** The delta stream reader (`c`) of either lowering: a head on the shared tape or a `DeltaReader`. */
  private trait Reader {
    def move(direction: Int): Unit
    def read(): Symbol
  }

  /** Python の `border_machine(word, collect_chain=False, *, _single_head=False)`。 */
  def borderMachine(word: Seq[Symbol], collectChain: Boolean, singleHead: Boolean): Result = {
    val clock = new Clock
    val z: Cells = mutable.HashMap.from((Left +: word :+ End).zipWithIndex.map(_.swap))
    val a = new Head(z, clock) // p = -1
    val b = new Head(if (singleHead) { z.clone() } else { z }, clock, 1) // i = 0
    val (c, append): (Reader, Symbol => Unit) = if (singleHead) {
      val queue = new TapeQueue(clock)
      val reader = new DeltaReader(clock, queue)
      (new Reader {
        def move(direction: Int): Unit = { reader.move(direction) }
        def read(): Symbol = reader.read()
      }, queue.append)
    } else {
      val y = cells(0 -> ZERO, 1 -> ONE, 2 -> ZERO) // delta(-1) = 1; pending d = 0
      val cHead = new Head(y, clock)
      val d = new Head(y, clock, 2)
      (new Reader {
        def move(direction: Int): Unit = { cHead.move(direction) }
        def read(): Symbol = cHead.read()
      }, (symbol: Symbol) => {
        d.move(1)
        d.write(symbol)
      })
    }
    val s = new Unary(clock)
    val t = new Unary(clock)
    if (b.read() == End) {
      return Result(0, clock.operations)
    }

    /** Fallback by OLD s zeros, subtracting intervening unary deltas from S.
      * Copying S is essential: S changes during the traversal.
      */
    def fallBack(onStep: () => Unit): Unit = {
      s.copyToEmpty(t)
      while (t.nonzero) {
        c.move(-1)
        while (c.read() == ONE) {
          s.pop()
          c.move(-1)
        }
        a.move(-1)
        onStep()
        t.pop()
      }
    }

    var scanning = true
    while (scanning) {
      b.move(1)
      val symbol = b.read()
      if (symbol == End) {
        scanning = false
      } else {
        var matching = true
        while (matching) {
          a.move(1)
          if (a.read() == symbol) {
            // Finalize delta(i) = d; carry s forward through delta(p).
            append(ZERO)
            c.move(1)
            while (c.read() == ONE) {
              s.push()
              c.move(1)
            }
            matching = false
          } else {
            a.move(-1)
            if (a.read() == Left) {
              // Finalize delta(i) = d + 1. p and s remain -1 and 0.
              append(ONE)
              append(ZERO)
              matching = false
            } else {
              fallBack(() => append(ONE))
            }
          }
        }
      }
    }

    // Observer only: a finite machine would return A positioned at the border.
    val longest = a.observedPosition
    val borders = mutable.ArrayBuffer.empty[Int]
    if (collectChain) {
      while (a.read() != Left) {
        borders += a.observedPosition
        fallBack(() => ())
      }
    }
    Result(longest, clock.operations, borders.toVector)
  }

  def borderMachine(word: String, collectChain: Boolean = false): Result =
    borderMachine(letters(word), collectChain, singleHead = false)

  /** Seven active single-head tapes; linear total local work, not real time.
    *
    * Two offline copies of the read-only input replace its two read heads.
    * A materialized delta prefix plus two queue stacks replaces the shared
    * append tape. The other two tapes are the original unary counters.
    */
  def singleHeadBorderMachine(word: String, collectChain: Boolean = false): Result =
    borderMachine(letters(word), collectChain, singleHead = true)

  /** Nonempty palindrome prefix lengths, decreasing (offline FPP).
    *
    * Preparation of word # reverse(word) is linear but external to the
    * counted kernel. The fresh symbol cannot occur in word. Output integers
    * are observer-decoded head positions, not machine registers.
    */
  def initialPalindromes(word: String, singleHead: Boolean = false): Result = {
    val symbols = letters(word)
    borderMachine((symbols :+ Separator) ++ symbols.reverse, collectChain = true, singleHead = singleHead)
  }

  def letters(word: String): Vector[Symbol] = word.map(Letter.apply).toVector
}
