#!/usr/bin/env python3
"""Independent checks and a symbolic identity check for OEIS A397245 mod 3."""

from __future__ import annotations

import sympy as sp


def predicted(n: int) -> int:
    """Coefficient prescribed by the proved ternary classification."""
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


def check_integer_recurrence() -> None:
    """Use Formula (6) from the OEIS page, with exact Python integers."""
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


def check_algebraic_recurrence() -> None:
    """Independently expand B=1+x*B^2+x^3*B^3 over GF(3)."""
    limit = 2000
    algebraic = [0] * (limit + 1)
    algebraic[0] = 1
    for n in range(1, limit + 1):
        coefficient = sum(
            algebraic[i] * algebraic[n - 1 - i] for i in range(n)
        )
        if n % 3 == 0:
            coefficient += algebraic[(n - 3) // 3]
        algebraic[n] = coefficient % 3
    assert all(algebraic[n] == predicted(n) for n in range(limit + 1))


def check_symbolic_differential_identity() -> None:
    """Reduce the proof's differential identity modulo its algebraic equation."""
    x, series = sp.symbols("x series")
    series_prime = series**2 / (1 + x * series)
    auxiliary = x + x * (series - 1) * series_prime / series
    total_derivative = (
        sp.diff(auxiliary, x) + sp.diff(auxiliary, series) * series_prime
    )
    numerator = sp.together(x * total_derivative - (series - 1)).as_numer_denom()[0]
    equation = series - 1 - x * series**2 - x**3 * series**3
    remainder = sp.groebner([equation], series, x, modulus=3).reduce(numerator)[1]
    assert remainder == 0


def main() -> None:
    check_integer_recurrence()
    check_algebraic_recurrence()
    check_symbolic_differential_identity()
    print("A397245 certificate: PASS")
    print("  exact integer recurrence: n=0..140")
    print("  independent GF(3) algebraic recurrence: n=0..2000")
    print("  symbolic differential identity: verified over GF(3)")


if __name__ == "__main__":
    main()
