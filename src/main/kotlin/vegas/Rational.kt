package vegas

import kotlin.math.abs

data class Rational(val numerator: Int, val denominator: Int = 1) {
    init {
        require(denominator != 0) { "Rational denominator cannot be zero" }
    }

    // Always store in reduced, canonical form: denom > 0; gcd-reduced
    private fun normalize(): Rational {
        var n = numerator
        var d = denominator
        if (d < 0) { n = -n; d = -d }
        val g = gcd(abs(n), d)
        return Rational(n / g, d / g, normalized = true)
    }

    // Secondary ctor to bypass double-normalization in private uses
    private constructor(n: Int, d: Int, normalized: Boolean) : this(n, d)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Rational) return false
        val a = this.normalize()
        val b = other.normalize()
        return a.numerator == b.numerator && a.denominator == b.denominator
    }

    override fun hashCode(): Int {
        val n = normalize()
        return 31 * n.numerator + n.denominator
    }

    override fun toString(): String {
        val n = normalize()
        return if (n.denominator == 1) "${n.numerator}" else "${n.numerator}/${n.denominator}"
    }

    operator fun plus(other: Rational): Rational =
        Rational(numerator * other.denominator + other.numerator * denominator, denominator * other.denominator).normalize()

    operator fun times(other: Rational): Rational =
        Rational(numerator * other.numerator, denominator * other.denominator).normalize()

    operator fun div(other: Rational): Rational {
        require(other.numerator != 0) { "Division by zero" }
        return Rational(numerator * other.denominator, denominator * other.numerator).normalize()
    }

    companion object {
        fun of(n: Int, d: Int): Rational = Rational(n, d).normalize()
        private tailrec fun gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)
    }
}
