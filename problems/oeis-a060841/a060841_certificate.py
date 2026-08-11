#!/usr/bin/env python3
"""Exact certificates for two claims attached to OEIS A060841.

For R(n) = product_{k=1}^n k^2 / phi(k), this script

* verifies the finite part of the integrality classification;
* checks the elementary 2-adic bound used for every n >= 91; and
* finds the first denominator having an odd prime factor (n = 1807).

Only Python integer and Fraction arithmetic is used.
"""

from fractions import Fraction
from math import isqrt


LIMIT = 1807


def totients(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for multiple in range(p, limit + 1, p):
                phi[multiple] -= phi[multiple] // p
    return phi


def primes(limit: int) -> list[int]:
    is_prime = bytearray(b"\1") * (limit + 1)
    if limit >= 0:
        is_prime[0] = 0
    if limit >= 1:
        is_prime[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if is_prime[p]:
            start = p * p
            is_prime[start::p] = b"\0" * (((limit - start) // p) + 1)
    return [p for p in range(2, limit + 1) if is_prime[p]]


def valuation(value: int, prime: int) -> int:
    result = 0
    while value % prime == 0 and value:
        result += 1
        value //= prime
    return result


def main() -> None:
    phi = totients(LIMIT)
    prime_list = primes(LIMIT)

    # Direct rational check of all small cases named in the conjecture.
    rational = Fraction(1)
    small_denominators: dict[int, int] = {}
    for n in range(1, 39):
        rational *= Fraction(n * n, phi[n])
        small_denominators[n] = rational.denominator
    expected_integral = set(range(1, 35)) | {36, 38}
    assert {n for n, den in small_denominators.items() if den == 1} == expected_integral
    assert small_denominators[35] == small_denominators[37] == 2

    # A second, direct route to the claimed minimal odd denominator.  This
    # deliberately constructs and reduces R(n) as a Fraction instead of using
    # the prime-valuation bookkeeping below.
    rational = Fraction(1)
    first_fraction_odd_denominator = None
    denominator_1806 = None
    denominator_1807 = None
    for n in range(1, LIMIT + 1):
        rational *= Fraction(n * n, phi[n])
        odd_part = rational.denominator
        while odd_part % 2 == 0:
            odd_part //= 2
        if odd_part > 1 and first_fraction_odd_denominator is None:
            first_fraction_odd_denominator = (n, odd_part)
        if n == 1806:
            denominator_1806 = rational.denominator
        if n == 1807:
            denominator_1807 = rational.denominator
    assert first_fraction_odd_denominator == (1807, 3)
    assert denominator_1806 == 2**2339
    assert denominator_1807 == 3 * 2**2342

    # Exact p-adic running exponents of R(n).
    v2 = 0
    v3 = 0
    running_valuations = {p: 0 for p in prime_list}
    nonnegative_v2_through_90: list[int] = []
    first_negative_v3 = None
    first_odd_denominator_prime = None
    for n in range(1, LIMIT + 1):
        v2 += 2 * valuation(n, 2) - valuation(phi[n], 2)
        v3 += 2 * valuation(n, 3) - valuation(phi[n], 3)
        for p in prime_list:
            if p > n:
                break
            running_valuations[p] += 2 * valuation(n, p) - valuation(phi[n], p)
        if n <= 90 and v2 >= 0:
            nonnegative_v2_through_90.append(n)
        if v3 < 0 and first_negative_v3 is None:
            first_negative_v3 = (n, v3)
        if first_odd_denominator_prime is None:
            for p in prime_list[1:]:
                if p > n:
                    break
                if running_valuations[p] < 0:
                    first_odd_denominator_prime = (n, p, running_valuations[p])
                    break

    assert set(nonnegative_v2_through_90) == expected_integral
    assert first_negative_v3 == (1807, -1)
    assert first_odd_denominator_prime == (1807, 3, -1)

    # For n >= 91, retain only odd primes p <= 79 in the negative term
    # of v_2(R(n)).  Their total weight is C > 15/8 and sum of weights is 34.
    weighted_primes = [(p, valuation(p - 1, 2)) for p in primes(79) if p != 2]
    coefficient = sum((Fraction(weight, p) for p, weight in weighted_primes), Fraction())
    weight_sum = sum(weight for _, weight in weighted_primes)
    assert coefficient > Fraction(15, 8)
    assert weight_sum == 34
    # Hence v_2(R(n)) <= 3n/2 - (n*C - 34) < 34 - 3n/8 < 0.
    assert Fraction(34) - Fraction(3 * 91, 8) < 0

    # Recover every denominator prime exponent at n=1807 without constructing
    # the enormous numerator.  No prime greater than n can occur in phi(k), k<=n.
    denominator_factorization: dict[int, int] = {}
    for p in prime_list:
        exponent = sum(
            2 * valuation(k, p) - valuation(phi[k], p)
            for k in range(1, LIMIT + 1)
        )
        if exponent < 0:
            denominator_factorization[p] = -exponent
    assert denominator_factorization == {2: 2342, 3: 1}

    print("integral n through 90:", nonnegative_v2_through_90)
    print("selected-prime coefficient:", coefficient, "> 15/8")
    print("selected-prime weight sum:", weight_sum)
    print("first negative 3-adic exponent:", first_negative_v3)
    print("first odd denominator prime:", first_odd_denominator_prime)
    print("direct Fraction first odd denominator:", first_fraction_odd_denominator)
    print("denominator factorization at n=1807:", denominator_factorization)


if __name__ == "__main__":
    main()
