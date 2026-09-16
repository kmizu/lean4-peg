package pal

import FppCost.bounds

/** Clock bounds derived from the finite program and source control structure.
  *
  * The instruction quantum is a compilation granularity, not an input budget.
  * Every positive quantum has a derived match interval. Predictability constants
  * are conditional on the source contracts documented in GALIL_CLOCK.md.
  *
  * Python 原典: `galil_clock.py`。
  */
object GalilClock {

  final case class Timing(
    quantum: Int,
    stageFactor: Int,
    matchDelay: Int,
    moveSlope: Int,
    intervalOverhead: Int,
    predictability: Int
  ) {
    def service: Int = 2 * predictability
  }

  /** Exact rational arithmetic standing in for Python's `fractions.Fraction`. */
  final case class Fraction(numerator: Long, denominator: Long) extends Ordered[Fraction] {
    require(denominator > 0)

    def +(that: Fraction): Fraction =
      Fraction.normalized(numerator * that.denominator + that.numerator * denominator, denominator * that.denominator)

    def compare(that: Fraction): Int =
      java.lang.Long.compare(numerator * that.denominator, that.numerator * denominator)

    /** Python の `math.ceil(fraction)`。 */
    def ceil: Int = Math.floorDiv(numerator + denominator - 1, denominator).toInt
  }

  object Fraction {
    def normalized(numerator: Long, denominator: Long): Fraction = {
      val g = gcd(math.abs(numerator), denominator)
      Fraction(numerator / g, denominator / g)
    }

    private def gcd(a: Long, b: Long): Long = if (b == 0) { math.max(a, 1) } else { gcd(b, a % b) }
  }

  /** Python の `derive(quantum=64)`。 */
  def derive(quantum: Int = 64): Timing = {
    if (quantum < 1) {
      throw new IllegalArgumentException("positive integral instruction quantum required")
    }
    val cost = bounds()
    val a = cost.dp.slope.toLong
    val b = cost.dp.intercept.toLong
    val q = quantum.toLong
    // First span is 8*max(r,1); subsequent spans double and are at least 16.
    val first = Fraction(19, 8) + Fraction(a, q) + Fraction(10, 8) + Fraction(a + b, 8 * q)
    val later = Fraction(11, 4) + Fraction(a, q) + Fraction(10, 16) + Fraction(a + b, 16 * q)
    val stage = (if (first >= later) { first } else { later }).ceil
    // Initial main slack is span/24. Eight also suffices to finish chain
    // copying/catch-up before the symmetric radius reaches 4h.
    val minimum = math.max(24 * stage, 8)
    val delay = 1 << bitLength(minimum - 1)
    // A move of delta has old radius <=4*delta and copied length <=8*delta.
    // Allow two match intervals per replayed place, including chain restart.
    val move = 8 * delay + 40 + Fraction(8L * cost.marked.slope, q).ceil
    val fallbackOverhead = 6 + Fraction(cost.marked.intercept.toLong, q).ceil
    val overhead = 4 * delay + 2 * fallbackOverhead + 2
    Timing(quantum, stage, delay, move, overhead, move + overhead)
  }

  /** Python の `int.bit_length()`（非負整数向け）。 */
  def bitLength(n: Int): Int = 32 - Integer.numberOfLeadingZeros(n)
}
