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
