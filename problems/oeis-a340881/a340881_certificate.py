#!/usr/bin/env python3
"""Executable checks accompanying the proof of the two A340881 conjectures.

This is not a finite-search substitute for the proof in PROOF.md.  It checks
the defining formula, the derived first-order recurrence, and the congruences
used by the proof over a reasonably broad collection of moduli.
"""

from __future__ import annotations

from math import gcd


OFFICIAL_TERMS = [
    1,
    3,
    17,
    183,
    3769,
    149607,
    11522393,
    1731779367,
    510323215321,
    295959535117863,
    338795401444537817,
    767301163051807117863,
    3444329717600807441325529,
    30688384795438974301695656487,
    543332627310980056832574442798553,
]


def triangular(k: int) -> int:
    return k * (k + 1) // 2


def a_from_definition(n: int, modulus: int | None = None) -> int:
    """Evaluate the OEIS sum directly (slow, but independent of recurrence)."""
    if n < 1:
        raise ValueError("A340881 is indexed from n=1")
    total = 0
    for k in range(n):
        term = pow(2, triangular(k), modulus) if modulus else 2 ** triangular(k)
        for j in range(k + 1, n):
            factor = (pow(2, j, modulus) - 1) if modulus else (2**j - 1)
            term *= factor
            if modulus:
                term %= modulus
        total += term
        if modulus:
            total %= modulus
    return total


def values_through(n_max: int, modulus: int | None = None) -> list[int | None]:
    """Use a(n+1)=(2^n-1)a(n)+2^(n(n+1)/2), with a(1)=1."""
    if n_max < 1:
        raise ValueError("n_max must be positive")
    values: list[int | None] = [None] * (n_max + 1)
    values[1] = 1 if modulus is None else 1 % modulus
    for n in range(1, n_max):
        assert values[n] is not None
        if modulus is None:
            values[n + 1] = (2**n - 1) * values[n] + 2 ** triangular(n)
        else:
            values[n + 1] = (
                (pow(2, n, modulus) - 1) * values[n]
                + pow(2, triangular(n), modulus)
            ) % modulus
    return values


def order_of_two(odd_modulus: int) -> int:
    if odd_modulus <= 1 or odd_modulus % 2 == 0 or gcd(2, odd_modulus) != 1:
        raise ValueError("the modulus must be odd and greater than one")
    residue = 1
    for order in range(1, odd_modulus + 1):
        residue = (2 * residue) % odd_modulus
        if residue == 1:
            return order
    raise AssertionError("multiplicative order was not found")


def two_adic_split(modulus: int) -> tuple[int, int]:
    """Return e,u such that modulus=2^e*u and u is odd."""
    e = 0
    u = modulus
    while u % 2 == 0:
        e += 1
        u //= 2
    return e, u


def triangular_threshold(e: int) -> int:
    """Least k with k(k+1)/2 >= e."""
    k = 0
    while triangular(k) < e:
        k += 1
    return k


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def check_definition_and_recurrence() -> None:
    exact = values_through(len(OFFICIAL_TERMS))
    assert exact[1:] == OFFICIAL_TERMS
    for n in range(1, 13):
        assert a_from_definition(n) == exact[n]
    for modulus in range(2, 80):
        modular = values_through(18, modulus)
        for n in range(1, 19):
            assert a_from_definition(n, modulus) == modular[n]


def check_odd_modulus_theorem() -> int:
    checks = 0
    for modulus in range(3, 300, 2):
        order = order_of_two(modulus)
        period = 2 * order
        values = values_through(3 * period + 12, modulus)
        for n in range(1, 2 * period + 12):
            assert values[n + period] == values[n]
            checks += 1
        # This is the exponent identity used after k -> k+period.
        for k in range(0, 20):
            exponent_difference = triangular(k + period) - triangular(k)
            assert exponent_difference % order == 0
    return checks


def check_prime_statement() -> int:
    checks = 0
    for prime in range(2, 252):
        if not is_prime(prime):
            continue
        advertised_period = 2 * (prime - 1)
        values = values_through(2 * advertised_period + 12, prime)
        for n in range(1, advertised_period + 12):
            assert values[n + advertised_period] == values[n]
            checks += 1
    return checks


def check_all_moduli_eventual_theorem() -> int:
    checks = 0
    for modulus in range(2, 301):
        e, odd_part = two_adic_split(modulus)
        start = max(1, e, triangular_threshold(e))
        period = 2 if odd_part == 1 else 2 * order_of_two(odd_part)
        values = values_through(start + 3 * period + 24, modulus)
        for n in range(start, start + 2 * period + 24):
            assert values[n + period] == values[n]
            checks += 1

        if e:
            power_of_two = 2**e
            two_values = values_through(start + 50, power_of_two)
            for n in range(start, start + 49):
                assert two_values[n + 1] == (-two_values[n]) % power_of_two
                checks += 1
    return checks


def main() -> None:
    check_definition_and_recurrence()
    odd_checks = check_odd_modulus_theorem()
    prime_checks = check_prime_statement()
    all_checks = check_all_moduli_eventual_theorem()
    print("A340881 certificate: PASS")
    print(f"  odd-modulus pure-period checks: {odd_checks}")
    print(f"  prime advertised-period checks: {prime_checks}")
    print(f"  general eventual-period/sign checks: {all_checks}")


if __name__ == "__main__":
    main()
