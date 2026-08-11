#!/usr/bin/env python3
"""Independent exact certificate for the A072780 counterexample."""

from math import gcd, isqrt


def positive_divisors(n: int) -> list[int]:
    """Enumerate divisors in pairs, without using a factorization."""
    assert n > 0
    low: list[int] = []
    high: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            low.append(d)
            if d * d != n:
                high.append(n // d)
    return low + high[::-1]


def a_by_divisor_enumeration(n: int) -> tuple[int, int, int, int]:
    """Evaluate a(n) directly from divisors and a gcd-counting totient."""
    divisors = positive_divisors(n)
    sigma1 = sum(divisors)
    sigma2 = sum(d * d for d in divisors)
    phi = sum(gcd(k, n) == 1 for k in range(1, n + 1))
    return sigma2 + phi * sigma1 - 2 * n * n, sigma1, sigma2, phi


def factorization(n: int) -> dict[int, int]:
    """Trial-divide n; this is independent of positive_divisors."""
    factors: dict[int, int] = {}
    p = 2
    remaining = n
    while p * p <= remaining:
        while remaining % p == 0:
            factors[p] = factors.get(p, 0) + 1
            remaining //= p
        p = 3 if p == 2 else p + 2
    if remaining > 1:
        factors[remaining] = factors.get(remaining, 0) + 1
    return factors


def a_by_multiplicative_formulas(n: int) -> tuple[int, int, int, int]:
    """Evaluate sigma, sigma_2, and phi from the prime factorization."""
    sigma1 = 1
    sigma2 = 1
    phi = 1
    for p, exponent in factorization(n).items():
        sigma1 *= sum(p**j for j in range(exponent + 1))
        sigma2 *= sum(p ** (2 * j) for j in range(exponent + 1))
        phi *= (p - 1) * p ** (exponent - 1)
    return sigma2 + phi * sigma1 - 2 * n * n, sigma1, sigma2, phi


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d != 0 for d in range(3, isqrt(n) + 1, 2))


def main() -> None:
    m, r = 8, 7
    assert m > r
    n = m * m - r * r
    left, right = m - r, m + r

    direct = a_by_divisor_enumeration(n)
    multiplicative = a_by_multiplicative_formulas(n)

    assert n == 15
    assert left == 1 and right == 15 and left * right == n
    assert direct == (2, 24, 260, 8)
    assert multiplicative == direct
    assert not is_prime(left) and not is_prime(right)
    assert is_prime(3) and is_prime(5) and 3 != 5 and 3 * 5 == n

    print("A072780 counterexample certificate: PASS")
    print(f"m={m}, r={r}, m^2-r^2={n}, m-r={left}, m+r={right}")
    print(f"sigma_1({n})={direct[1]}, sigma_2({n})={direct[2]}, phi({n})={direct[3]}")
    print(f"a({n})={direct[0]}, while {left} and {right} are nonprime")


if __name__ == "__main__":
    main()
