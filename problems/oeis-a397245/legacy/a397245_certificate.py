"""Independent finite checks and symbolic identities for OEIS A397245 mod 3."""

import sympy as sp


def predicted(n: int) -> int:
    """Coefficient prescribed by the ternary classification in the proof."""
    value = n + 2
    ones = 0
    twos = 0
    while value:
        digit = value % 3
        value //= 3
        ones += digit == 1
        twos += digit == 2
    if (ones, twos) in {(1, 0), (0, 1)}:
        return 1
    if (ones, twos) == (2, 0):
        return 2
    return 0


# Exact-integer recurrence from Formula (6) on the OEIS page.
limit = 140
a = [1, 1]
c = [0, 1]
for n in range(2, limit + 1):
    c_n = 4 * a[n - 1]
    for j in range(2, n):
        c_n += (4 * j * j - 1) * c[j] * a[n - j]
    c.append(c_n)
    a.append(n * c_n)

assert a[:9] == [
    1,
    1,
    8,
    276,
    19216,
    2109180,
    327968280,
    68141519908,
    18217107336224,
]
assert all(a[n] % 3 == predicted(n) for n in range(limit + 1))


# Independent coefficient recursion from A = 1 + x*A^2 + x^3*A^3 over GF(3).
limit = 2000
algebraic = [0] * (limit + 1)
algebraic[0] = 1
for n in range(1, limit + 1):
    coefficient = sum(algebraic[i] * algebraic[n - 1 - i] for i in range(n))
    if n % 3 == 0:
        coefficient += algebraic[(n - 3) // 3]
    algebraic[n] = coefficient % 3
assert all(algebraic[n] == predicted(n) for n in range(limit + 1))


# Symbolic check of the differential identity used in the proof.
x, A = sp.symbols("x A")
A_prime = A**2 / (1 + x * A)
C = x + x * (A - 1) * A_prime / A
total_C_prime = sp.diff(C, x) + sp.diff(C, A) * A_prime
numerator = sp.together(x * total_C_prime - (A - 1)).as_numer_denom()[0]
conjecture_polynomial = A - 1 - x * A**2 - x**3 * A**3
remainder = sp.groebner([conjecture_polynomial], A, x, modulus=3).reduce(numerator)[1]
assert remainder == 0

print("A397245 certificate checks passed")
