#!/usr/bin/env python3
"""Exact arithmetic checks for proposed Erdős problem #307 pairs."""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from functools import reduce
from operator import mul


def product(values: list[int] | tuple[int, ...]) -> int:
    return reduce(mul, values, 1)


def numerator_a(values: list[int] | tuple[int, ...]) -> int:
    m = product(values)
    return sum(m // value for value in values)


def reciprocal_sum(values: list[int] | tuple[int, ...]) -> Fraction:
    if not values:
        return Fraction(0)
    return Fraction(numerator_a(values), product(values))


def pairwise_coprime(values: list[int] | tuple[int, ...]) -> bool:
    return all(math.gcd(values[i], values[j]) == 1
               for i in range(len(values)) for j in range(i))


def is_prime(value: int) -> bool:
    """Exact trial-division primality test (intentionally dependency-free)."""
    if value < 2:
        return False
    if value in (2, 3):
        return True
    if value % 2 == 0 or value % 3 == 0:
        return False
    divisor = 5
    limit = math.isqrt(value)
    while divisor <= limit:
        if value % divisor == 0 or value % (divisor + 2) == 0:
            return False
        divisor += 6
    return True


def legendre(numerator: int, prime: int) -> int:
    if prime == 2 or not is_prime(prime):
        raise ValueError("Legendre denominator must be an odd prime")
    residue = numerator % prime
    if residue == 0:
        return 0
    result = pow(residue, (prime - 1) // 2, prime)
    return -1 if result == prime - 1 else result


def jacobi(numerator: int, denominator: int) -> int:
    """Jacobi symbol (numerator/denominator), for positive odd denominator."""
    if denominator <= 0 or denominator % 2 == 0:
        raise ValueError("Jacobi denominator must be positive and odd")
    a = numerator % denominator
    n = denominator
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def reciprocity_identity(values: list[int] | tuple[int, ...],
                         use_jacobi: bool = False) -> dict[str, int | bool]:
    """Check the raw pairwise quadratic-reciprocity product identity."""
    values = sorted(values)
    odd = [value for value in values if value != 2]
    if any(value <= 0 or value % 2 == 0 for value in odd):
        raise ValueError("only 2 may be even")
    if not pairwise_coprime(values):
        raise ValueError("values must be pairwise coprime")
    symbol = jacobi if use_jacobi else legendre
    lhs = 1
    for denominator in odd:
        lhs *= symbol(product([value for value in values
                              if value != denominator]), denominator)
    u = sum(value % 4 == 3 for value in odd)
    v = sum(value % 8 in (3, 5) for value in odd)
    exponent = u * (u - 1) // 2 + (v if 2 in values else 0)
    rhs = -1 if exponent % 2 else 1
    return {
        "lhs": lhs,
        "rhs": rhs,
        "u": u,
        "v": v,
        "exponent_mod_2": exponent % 2,
        "matches": lhs == rhs,
    }


def generalized_pair_report(p_values: list[int], q_values: list[int]) -> dict[str, object]:
    """For pairwise-coprime toy denominators, including composite ones."""
    mp, mq = product(p_values), product(q_values)
    ap, aq = numerator_a(p_values), numerator_a(q_values)
    sigma_p, sigma_q = reciprocal_sum(p_values), reciprocal_sum(q_values)
    return {
        "P": p_values,
        "Q": q_values,
        "P_pairwise_coprime": pairwise_coprime(p_values),
        "Q_pairwise_coprime": pairwise_coprime(q_values),
        "cross_pairwise_coprime": pairwise_coprime(p_values + q_values),
        "M_P": mp,
        "A_P": ap,
        "M_Q": mq,
        "A_Q": aq,
        "gcd_A_M": [math.gcd(ap, mp), math.gcd(aq, mq)],
        "forcing_identities": ap == mq and aq == mp,
        "product_equals_one": sigma_p * sigma_q == 1,
        "sigma_P": f"{sigma_p.numerator}/{sigma_p.denominator}",
        "sigma_Q": f"{sigma_q.numerator}/{sigma_q.denominator}",
    }


def prime_pair_report(p_values: list[int], q_values: list[int]) -> dict[str, object]:
    if len(set(p_values)) != len(p_values) or len(set(q_values)) != len(q_values):
        raise ValueError("each input must be a set")
    if not all(is_prime(value) for value in p_values + q_values):
        raise ValueError("all entries must be prime")

    p_values = sorted(p_values)
    q_values = sorted(q_values)
    mp, mq = product(p_values), product(q_values)
    ap, aq = numerator_a(p_values), numerator_a(q_values)
    sigma_p, sigma_q = reciprocal_sum(p_values), reciprocal_sum(q_values)
    equation = sigma_p * sigma_q == 1
    forcing = ap == mq and aq == mp
    disjoint = set(p_values).isdisjoint(q_values)
    union = sorted(set(p_values) | set(q_values))
    n = product(union)

    cross_congruences: list[dict[str, int | bool | str]] = []
    if disjoint:
        for side, own, other, m_own, m_other in (
            ("P", p_values, q_values, mp, mq),
            ("Q", q_values, p_values, mq, mp),
        ):
            for prime in own:
                cross_congruences.append({
                    "side": side,
                    "prime": prime,
                    "opposite_product_mod_prime": m_other % prime,
                    "own_cofactor_mod_prime": (m_own // prime) % prime,
                    "matches": m_other % prime == (m_own // prime) % prime,
                })

    local_symbols: list[dict[str, int | bool | str]] = []
    if disjoint:
        for prime in union:
            if prime == 2:
                local_symbols.append({
                    "prime": 2,
                    "symbol": "not defined",
                    "mod_2_congruence_is_tautological": (n // 2) % 2 == 1,
                })
            else:
                value = legendre(n // prime, prime)
                local_symbols.append({
                    "prime": prime,
                    "symbol": value,
                    "is_quadratic_residue": value == 1,
                })

    odd = [prime for prime in union if prime != 2]
    u = sum(prime % 4 == 3 for prime in odd)
    v = sum(prime % 8 in (3, 5) for prime in odd)
    reciprocity_exponent = u * (u - 1) // 2 + (v if 2 in union else 0)
    aggregate_condition = reciprocity_exponent % 2 == 0
    raw_reciprocity = reciprocity_identity(union) if union else None

    t = product(odd) % 8
    s = sum(odd) % 8
    if 2 not in union:
        union_mod8 = (s - 2 * t) % 8 == 0
    else:
        union_mod8 = (2 * s - (5 * t - 1)) % 8 == 0

    partition_mod8 = False
    if disjoint:
        if 2 not in union:
            partition_mod8 = (sum(p_values) - t) % 8 == 0 and (
                sum(q_values) - t) % 8 == 0
        else:
            containing = p_values if 2 in p_values else q_values
            opposite = q_values if 2 in p_values else p_values
            partition_mod8 = ((sum(opposite) - 2 * t) % 8 == 0 and
                              (1 + 2 * sum(value for value in containing
                                         if value != 2) - t) % 8 == 0)

    union_mod24: bool | None = None
    partition_mod24: bool | None = None
    if 3 not in union:
        t24 = product(odd) % 24
        s24 = sum(odd) % 24
        if 2 not in union:
            union_mod24 = (s24 - 2 * t24) % 24 == 0
            if disjoint:
                partition_mod24 = ((sum(p_values) - t24) % 24 == 0 and
                                   (sum(q_values) - t24) % 24 == 0)
        else:
            union_mod24 = (1 + 2 * s24 - 5 * t24) % 24 == 0
            if disjoint:
                containing = p_values if 2 in p_values else q_values
                opposite = q_values if 2 in p_values else p_values
                partition_mod24 = ((sum(opposite) - 2 * t24) % 24 == 0 and
                                   (1 + 2 * sum(value for value in containing
                                              if value != 2) - t24) % 24 == 0)

    parity_condition = False
    if disjoint:
        if 2 not in union:
            parity_condition = len(p_values) % 2 == len(q_values) % 2 == 1
        elif 2 in p_values:
            parity_condition = len(q_values) % 2 == 0
        else:
            parity_condition = len(p_values) % 2 == 0

    a_union = numerator_a(union)
    return {
        "P": p_values,
        "Q": q_values,
        "disjoint": disjoint,
        "sigma_P": f"{sigma_p.numerator}/{sigma_p.denominator}",
        "sigma_Q": f"{sigma_q.numerator}/{sigma_q.denominator}",
        "product_equals_one": equation,
        "M_P": mp,
        "A_P": ap,
        "M_Q": mq,
        "A_Q": aq,
        "gcd_A_M": [math.gcd(ap, mp), math.gcd(aq, mq)],
        "forcing_identities": forcing,
        "forcing_equivalent_to_equation_on_this_input": forcing == equation,
        "cross_congruences": cross_congruences,
        "local_square_symbols": local_symbols,
        "all_local_square_conditions": bool(disjoint) and all(
            item.get("is_quadratic_residue", True) for item in local_symbols),
        "u_3_mod_4": u,
        "v_3_or_5_mod_8": v,
        "reciprocity_exponent_mod_2": reciprocity_exponent % 2,
        "raw_reciprocity_product_identity": raw_reciprocity,
        "aggregate_reciprocity_condition": aggregate_condition,
        "union_mod8_condition": union_mod8,
        "partition_mod8_conditions": partition_mod8,
        "union_mod24_condition_if_3_absent": union_mod24,
        "partition_mod24_conditions_if_3_absent": partition_mod24,
        "parity_condition": parity_condition,
        "union_identity_A_equals_squares": a_union == mp * mp + mq * mq,
    }


def parse_set(text: str) -> list[int]:
    return [] if not text.strip() else [int(token) for token in text.split(",")]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--P", required=True, help="comma-separated prime set")
    parser.add_argument("--Q", required=True, help="comma-separated prime set")
    args = parser.parse_args()
    print(json.dumps(prime_pair_report(parse_set(args.P), parse_set(args.Q)),
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
