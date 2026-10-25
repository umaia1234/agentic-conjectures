#!/usr/bin/env python3
"""Independent exact certificate for the A108864 counterexample 815634435.

Checks, using only the Python standard library:

1. A literal transcription of the upstream Lean fold `perfectDeficiency`
   (every candidate d = 0..n, Lean's `0 ∣ n ↔ n = 0`) agrees with the OEIS
   A109883 PARI program (stop at the first divisor larger than the remainder)
   for 1 <= n <= 2000.
2. The terms <= 1248 computed by the literal fold are exactly the 61 data
   terms of OEIS A108864; in particular, 0-indexed a(58) = 1155, and the 59
   terms 1..1155 are the `firstTerms` list used in the Lean module.
3. The witness 815634435 = 3*5*7*11*547*1291 (trial-division factorization,
   trial-division primality), with its divisors enumerated twice (from the
   factorization and by pairing up to sqrt(n)); sigma(n) = 2n - 6 both as the
   divisor sum and as prod(p + 1).
4. Its perfect deficiency is 6 <= 10 under both the upstream fold semantics
   restricted to divisors (non-divisors leave the remainder unchanged) and the
   PARI semantics; the witness is odd and larger than 1155, so its 0-based
   index is at least 59 > 58.
"""

from math import isqrt
import sys
import time

WITNESS = 815634435
FACTORS = [3, 5, 7, 11, 547, 1291]

# OEIS A108864 data section (%S, %T, %U lines, revision #3), offset 1.
OEIS_DATA = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26,
    28, 30, 32, 40, 42, 44, 50, 52, 60, 64, 68, 72, 110, 120, 126, 128, 130,
    136, 144, 150, 152, 180, 184, 204, 228, 256, 315, 462, 496, 512, 528, 592,
    656, 750, 884, 1012, 1024, 1155, 1188, 1248,
]

# `firstTerms` in AgenticConjectures/OeisA108864.lean.
LEAN_FIRST_TERMS = OEIS_DATA[:59]


def lean_dvd(d: int, n: int) -> bool:
    """Lean's `d ∣ n` on naturals: `0 ∣ n` holds exactly when n = 0."""
    return n == 0 if d == 0 else n % d == 0


def pd_upstream_literal(n: int) -> int:
    """(List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n."""
    m = n
    for d in range(n + 1):
        if lean_dvd(d, n) and d <= m:
            m -= d
    return m


def pd_upstream_on_divisors(n: int, divisors: list[int]) -> int:
    """The same fold, visiting only the divisors (other candidates are no-ops)."""
    assert n > 0
    m = n
    for d in sorted(divisors):
        if d <= m:
            m -= d
    return m


def pd_pari(n: int, divisors: list[int]) -> int:
    """OEIS A109883 PARI: my(r = n); fordiv(n, d, if (r < d, return (r)); r -= d;); 0."""
    r = n
    for d in sorted(divisors):
        if r < d:
            return r
        r -= d
    return 0


def divisors_by_pairing(n: int) -> list[int]:
    """Enumerate the divisors of n without a factorization."""
    low: list[int] = []
    high: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            low.append(d)
            if d * d != n:
                high.append(n // d)
    return low + high[::-1]


def factorize(n: int) -> dict[int, int]:
    """Trial division."""
    factors: dict[int, int] = {}
    p, rest = 2, n
    while p * p <= rest:
        while rest % p == 0:
            factors[p] = factors.get(p, 0) + 1
            rest //= p
        p += 1
    if rest > 1:
        factors[rest] = factors.get(rest, 0) + 1
    return factors


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % q for q in range(2, isqrt(n) + 1))


def divisors_from_factorization(factors: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in factors.items():
        divs = [d * p**j for d in divs for j in range(e + 1)]
    return sorted(divs)


def check(condition: bool, message: str) -> None:
    if not condition:
        print("FAIL:", message)
        sys.exit(1)
    print("ok:", message)


def main() -> None:
    start = time.time()

    # 1. Upstream fold versus the OEIS A109883 program.
    for n in range(1, 2001):
        if pd_upstream_literal(n) != pd_pari(n, divisors_by_pairing(n)):
            check(False, f"upstream fold and A109883 PARI program differ at n={n}")
    check(True, "upstream fold == A109883 PARI program for 1 <= n <= 2000")
    check(pd_upstream_literal(14) == 4 and pd_upstream_literal(35) == 22,
          "A109883 examples a(14)=4, a(35)=22")

    # 2. Small terms, index base, and the Lean list.
    terms = [n for n in range(1, OEIS_DATA[-1] + 1)
             if 0 < n and pd_upstream_literal(n) <= 10]
    check(terms == OEIS_DATA, "terms <= 1248 equal the 61 OEIS A108864 data terms")
    check(terms[58] == 1155 and sum(1 for t in terms if t <= 1155) == 59,
          "0-indexed a(58) = 1155: exactly 59 terms are <= 1155")
    check(LEAN_FIRST_TERMS == terms[:59] and len(set(LEAN_FIRST_TERMS)) == 59,
          "Lean firstTerms = the 59 terms 1..1155, pairwise distinct")

    # 3. The witness: factorization, divisors, sigma.
    n = WITNESS
    factors = factorize(n)
    check(factors == {p: 1 for p in FACTORS}, f"{n} = 3*5*7*11*547*1291 (squarefree)")
    check(all(is_prime(p) for p in FACTORS), "3, 5, 7, 11, 547, 1291 are prime")
    divs = divisors_by_pairing(n)
    check(divs == divisors_from_factorization(factors) and len(divs) == 64,
          "64 divisors, enumerated by pairing and from the factorization")
    sigma = sum(divs)
    product = 1
    for p in FACTORS:
        product *= p + 1
    check(sigma == product == 1631268864 == 2 * n - 6, "sigma(n) = 1631268864 = 2n - 6")
    proper_sum = sigma - n
    check(proper_sum == 815634429 and proper_sum <= n,
          "proper divisors sum to 815634429 <= n (key-lemma hypothesis)")

    # 4. Perfect deficiency, membership, parity, index.
    pd_fold = pd_upstream_on_divisors(n, divs)
    pd_par = pd_pari(n, divs)
    check(pd_fold == pd_par == 6 == 2 * n - sigma, "perfectDeficiency(n) = 6 = 2n - sigma(n)")
    check(n > 0 and pd_fold <= 10, "A(n): 0 < n and perfect deficiency <= 10")
    check(n % 2 == 1 and n > 1155, "n is odd and n > 1155")
    check(sum(1 for t in terms if t < n) >= 59,
          "at least 59 terms lie below n, so its 0-based index is > 58")

    print(f"PASS: 815634435 is an odd term of A108864 with index > 58 "
          f"({time.time() - start:.2f}s)")


if __name__ == "__main__":
    main()
