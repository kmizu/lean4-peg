package pal

/** An exact rational, standing in for Python's `fractions.Fraction` in the
  * service-rate derivations. Always normalized with a positive denominator.
  */
final case class Fraction private (numerator: BigInt, denominator: BigInt) {
  def +(other: Fraction): Fraction = {
    Fraction(numerator * other.denominator + other.numerator * denominator, denominator * other.denominator)
  }

  def *(other: Fraction): Fraction = Fraction(numerator * other.numerator, denominator * other.denominator)

  def <(other: Fraction): Boolean = numerator * other.denominator < other.numerator * denominator

  def >=(other: Fraction): Boolean = !(this < other)

  /** `math.ceil` of the exact value. */
  def ceil: Int = {
    // BigInt division truncates toward zero, which is already the ceiling for
    // negative values; positive remainders round up.
    val (quotient, remainder) = numerator /% denominator
    (if (remainder > 0) quotient + 1 else quotient).toInt
  }
}

object Fraction {
  def apply(numerator: BigInt, denominator: BigInt): Fraction = {
    if (denominator == 0) {
      throw new ArithmeticException("zero denominator")
    }
    val sign = denominator.signum
    val divisor = numerator.gcd(denominator)
    val reduced = if (divisor == 0) BigInt(1) else divisor
    new Fraction(numerator * sign / reduced, denominator * sign / reduced)
  }

  def apply(value: Int): Fraction = apply(BigInt(value), BigInt(1))
}

/** Selected per-arrival service rates (physical transitions). */
final case class Rates(k: Int, decomposition: Int, flagView: Int, matching: Int, flags: Int, overhead: Int = 39) {
  def round: Int = flags + overhead
}

/** Conservative local-head/queue service rates, not sampled maxima.
  *
  * See `GS_LOCAL_CLOCK.md`. A logical head instruction uses at most one queue pop;
  * its three explicitly scheduled maintenance units give a factor of four.
  * The final PAL compiler still has to fold this whole fixed input round.
  *
  * Port of `gs_local_clock.py`.
  */
object GsLocalClock {

  def powerTwoAtLeast(value: Int): Int = 1 << (32 - Integer.numberOfLeadingZeros(math.max(1, value) - 1))

  def derive(k: Int = 8): Rates = {
    if (k < 4) {
      throw new IllegalArgumentException("fixed integer k >= 4 required")
    }
    val failed = Fraction(44 * k + 31) + Fraction(13 * k, k - 2)
    val finalStage = Fraction(9 * k + 22) + Fraction(4, k)
    val decomposition = (finalStage + failed * Fraction(k - 2, k * (k - 3))).ceil + 5
    val borders = Fraction(decomposition + (7 * k + 15) + (4 * k + 6) + 23) * Fraction(k - 1, k - 3)
    val flagView = (borders + Fraction(6)).ceil + 5
    val matching = 4 * powerTwoAtLeast(decomposition + 32 * k + 16)
    // View length <=4K+1, K>=2: C(4K+1)+1 <= (4.5C+.5)K.
    // Four physical instructions per head instruction, over K/2 arrivals.
    val flagBound = (Fraction(8) * (Fraction(9, 2) * Fraction(flagView) + Fraction(1, 2))).ceil
    val flags = math.max(powerTwoAtLeast(flagBound), matching)
    Rates(k, decomposition, flagView, matching, flags)
  }

  val DEFAULT: Rates = derive()

  /** The two oriented views have length b each, without a 2b+1 view. */
  def deriveDual(k: Int = 8): Rates = {
    val source = derive(k)
    val flags = powerTwoAtLeast((Fraction(8) * (Fraction(2 * source.flagView) + Fraction(1, 2))).ceil)
    Rates(source.k, source.decomposition, source.flagView, source.matching,
      math.max(flags, source.matching), source.overhead)
  }

  val DEFAULT_DUAL: Rates = deriveDual()
}
