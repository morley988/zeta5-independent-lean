"""Exact rational certificate accompanying the Stage 60 manuscripts.

Python 3, standard library only. No floating-point arithmetic is used.
The program verifies the final inequalities conditional on the local and
analytic lemmas proved in the manuscripts. It is not a formalization of them.
"""
from fractions import Fraction as F
from math import isqrt

S = F(1, 20)
RHO = F(5, 4)
DELTA = RHO - S
LEFT = F(1, 40)
RIGHT = F(9, 20)
ZERO = F(0)
PRECISION = 10**30


def floor_data(beta):
    q = 1 // beta
    epsilon = int(2 * (1 - q * beta) >= beta)
    degree = (2 * RHO) // beta
    return q, epsilon, degree


def rank_profile(beta):
    q, epsilon, degree = floor_data(beta)
    width = 1 - (q + F(epsilon, 2)) * beta
    return (4 + epsilon) * DELTA + min(DELTA, (degree + 1) * width)


def exact_arithmetic():
    points = {LEFT, RIGHT}
    for q in range(1, 41):
        points.update((F(1, q), F(2, 2 * q + 1)))
    for k in range(1, 102):
        points.add(2 * RHO / k)
    points = sorted(x for x in points if LEFT <= x <= RIGHT)
    pieces = []
    for a, b in zip(points, points[1:]):
        q, epsilon, degree = floor_data((a + b) / 2)
        crossing = ((degree + 1 - DELTA)
                    / ((degree + 1) * (q + F(epsilon, 2))))
        cuts = [a, crossing, b] if a < crossing < b else [a, b]
        for left, right in zip(cuts, cuts[1:]):
            mid = (left + right) / 2
            width = 1 - (q + F(epsilon, 2)) * mid
            if (degree + 1) * width >= DELTA:
                intercept, slope = (5 + epsilon) * DELTA, ZERO
            else:
                intercept = (4 + epsilon) * DELTA + degree + 1
                slope = -(degree + 1) * (q + F(epsilon, 2))
            assert intercept + slope * mid == rank_profile(mid)
            area = (right - left) * (intercept + slope * mid)
            pieces.append((left, right, intercept, slope, area))
    assert pieces[0][0] == LEFT and pieces[-1][1] == RIGHT
    assert all(a[1] == b[0] for a, b in zip(pieces, pieces[1:]))
    assert len(pieces) == 228
    upper_rows = [
        (F(9, 20), F(1, 2), F(81, 5), -24),
        (F(1, 2), F(21, 40), F(139, 10), -15),
        (F(21, 40), F(5, 8), F(16), -19),
        (F(5, 8), F(3, 4), F(27, 2), -15),
        (F(3, 4), F(5, 6), F(12), -13),
        (F(5, 6), F(19, 20), F(19, 2), -10),
        (F(19, 20), F(1), F(38, 5), -8),
    ]
    upper_area = sum(((b - a) * (c + d * (a + b) / 2)
                      for a, b, c, d in upper_rows), ZERO)
    assert upper_area == F(901, 600)
    small_tail = (4 * DELTA + RHO) * LEFT + LEFT**2 / 4
    large_primes = 3 * RHO**2 - 4 * RHO + F(3, 2)
    assert small_tail == F(969, 6400)
    assert large_primes == F(19, 16)
    total = small_tail + large_primes + upper_area
    total += sum((row[4] for row in pieces), ZERO)
    expected = F(
        191258319415140413215011151671222972968539453509572803845881093658106414835114844023,
        35352223433977492021442108242640841605890021236208954246644376534746108587827200000)
    assert total == expected
    assert total < F(54101, 10000)
    return total, len(pieces) + len(upper_rows)


def sqrt_bounds(x):
    """Outward rational square-root bounds of width 10^-30."""
    root = isqrt(x.numerator * PRECISION**2 // x.denominator)
    lower, upper = F(root, PRECISION), F(root + 1, PRECISION)
    assert lower * lower <= x <= upper * upper
    return lower, upper


def log_unit_lower(x, terms=24):
    """Positive atanh series with every operation rounded down."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    iz = z.numerator * PRECISION // z.denominator
    iz2 = iz * iz // PRECISION
    power, total = iz, 0
    for j in range(terms):
        total += 2 * power // (2 * j + 1)
        power = power * iz2 // PRECISION
    return F(total, PRECISION)


LOG_TWO_LOWER = log_unit_lower(F(2))


def log_lower(x):
    assert x >= 1
    exponent = 0
    while x > 2:
        x /= 2
        exponent += 1
    return log_unit_lower(x) + exponent * LOG_TWO_LOWER


def u_and_g_lower(b):
    if b == 0:
        return ZERO, ZERO, 4 * S * LOG_TWO_LOWER
    a_lower, a_upper = sqrt_bounds(1 + b * b)
    c_lower, c_upper = sqrt_bounds(S**2 + b * b)
    u_lower = (b + 1 - 2 * S - a_upper + 2 * c_lower) / 2
    u_upper = (b + 1 - 2 * S - a_lower + 2 * c_upper) / 2
    assert 0 < u_lower <= u_upper
    v_lower = S + u_lower
    g_lower = (4 * u_lower * log_lower(4 * v_lower / b)
               + 4 * S * log_lower(4 * v_lower / (S + c_upper))
               + 2 * log_lower((1 + a_lower) / 2))
    assert g_lower > 0
    return u_lower, u_upper, g_lower


def exact_analytic_lower():
    endpoint = F(96156889, 10**8)
    subdivisions = 2048
    _, previous_upper, previous_g = u_and_g_lower(ZERO)
    total = ZERO
    for j in range(1, subdivisions + 1):
        b = endpoint * F(j, subdivisions)
        u_lower, u_upper, g_lower = u_and_g_lower(b)
        width_lower = u_lower - previous_upper
        assert width_lower > 0
        total += width_lower * (g_lower + previous_g) / 2
        previous_upper, previous_g = u_upper, g_lower
    assert previous_upper < DELTA
    assert total > F(54133705070, 10**10)
    assert total > F(54133, 10000)
    return total


def main():
    arithmetic, pieces = exact_arithmetic()
    analytic_lower = exact_analytic_lower()
    assert analytic_lower - arithmetic > F(32, 10000)
    print("EXACT COMPARISON CERTIFICATE PASS")
    print("Arithmetic affine pieces:", pieces)
    print("Arithmetic exact:", arithmetic)
    print("Arithmetic < 54101/10000 = 5.4101")
    print("Analytic lower bound > 54133/10000 = 5.4133")
    print("Certified strict margin > 32/10000 = 0.0032")
    print("Analytic lower bound, rounded down at 10 decimal places:",
          analytic_lower.numerator * 10**10 // analytic_lower.denominator,
          "/ 10000000000")
    print("This checks the comparison, not the underlying mathematical lemmas.")


if __name__ == "__main__":
    main()

