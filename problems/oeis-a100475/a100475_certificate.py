#!/usr/bin/env python3
"""Independent exact re-check of the finite data in the A100475 refutation.

The Lean module `AgenticConjectures/OeisA100475.lean` proves the refutation by
itself; every finite fact it needs is a kernel evaluation there. This script
re-derives the same numbers by an unrelated route (a sieve of Eratosthenes,
plain big-integer arithmetic, and a direct cycle search), so the constants in
the Lean file can be checked without Lean. It uses only the standard library.

Map: f(k) = reversal(p_k) for k >= 1, where p_1 = 2 and reversal reverses the
decimal digits (OEIS A100475; upstream `aStartAt`).
"""

import sys
import time

LIMIT = 10**7 + 1  # sieve covers every prime below 10^7 + 1


def sieve(n):
    """Return a bytearray s with s[i] == 1 iff i is prime, for 0 <= i < n."""
    s = bytearray([1]) * n
    s[0] = s[1] = 0
    i = 2
    while i * i < n:
        if s[i]:
            s[i * i::i] = bytes(len(range(i * i, n, i)))
        i += 1
    return s


def rev(n):
    return int(str(n)[::-1])


def ndigits(n):
    return len(str(n))


def main():
    t0 = time.time()
    failures = []

    def check(cond, msg):
        print(("ok   " if cond else "FAIL ") + msg)
        if not cond:
            failures.append(msg)

    s = sieve(LIMIT)
    primes = [i for i in range(LIMIT) if s[i]]

    def pi(x):  # number of primes < x (Lean's `Nat.count Nat.Prime x`)
        return s[:x].count(1)

    # 1. Prime counts used as kernel facts in the Lean proof.
    check(pi(10**4) == 1229, "count Prime 10000 = 1229")
    chunk_a = sum(pi(10000 + 16384 * (i + 1)) - pi(10000 + 16384 * i) for i in range(5))
    check(10000 + 5 * 2**14 == 91920 and chunk_a == 7649, "cnt_A: primes in [10000, 91920) = 7649")
    check(pi(100112) - pi(91920) == 722, "cnt_B: primes in [91920, 100112) = 722")
    chunk_c = sum(pi(100112 + 16384 * (i + 1)) - pi(100112 + 16384 * i) for i in range(25))
    check(100112 + 25 * 2**14 == 509712 and chunk_c == 32669,
          "cnt_C: primes in [100112, 509712) = 32669")
    check(pi(100112) == 9600 and pi(509712) == 42269,
          "count Prime 100112 = 9600, count Prime 509712 = 42269")
    # Side conditions of the gcd-with-factorial primality test B < n < (B + 1)^2.
    check(316 < 10000 and 100112 <= 317**2 and 720 < 100112 and 509712 <= 721**2,
          "factorial bases 316 and 720 cover their ranges")

    # 2. Dyadic Chebyshev-type steps 4^m < (m + 1)^(K + 1), exact integers.
    pairs = [(500000, 52821), (625000, 64923), (1250000, 123435),
             (2500000, 235255), (5000000, 449367)]
    for m, k in pairs:
        check((m + 1) ** (k + 1) > 4**m, f"4^{m} < {m + 1}^{k + 1}")
        # Consistency: the block (m, 2m] really has at most K primes.
        check(pi(2 * m + 1) - pi(m + 1) <= k, f"primes in [{m + 1}, {2 * m + 1}) <= {k}")
    bound6 = 42269 + 52821
    bound7 = bound6 + 64923 + 123435 + 235255 + 449367
    check(bound6 == 95090 < 10**5 and pi(1000001) <= bound6,
          "d = 6: pi(1000001) <= 42269 + 52821 = 95090 < 10^5")
    check(bound7 == 968070 < 10**6 and pi(10000001) <= bound7,
          "d = 7: pi(10000001) <= 95090 + 64923 + 123435 + 235255 + 449367 = 968070 < 10^6")
    check(4**100 < 10**63, "4^100 < 10^63 (step for d >= 8)")

    # 3. Exact pi(10^d) for d = 5, 6, 7: the counting bound pi(10^d) < 10^(d-1).
    for d, val in [(5, 9592), (6, 78498), (7, 664579)]:
        got = pi(10**d)
        check(got == val and got < 10 ** (d - 1), f"pi(10^{d}) = {got} < 10^{d - 1}")
    for d in range(1, 5):
        print(f"info pi(10^{d}) = {pi(10**d)} >= 10^{d - 1}: the digit bands d <= 4 need a search")

    # 4. Digit length of f(k) equals that of p_k and is >= that of k.
    mono = all(ndigits(rev(p)) == ndigits(p) >= ndigits(k)
               for k, p in enumerate(primes, start=1))
    check(mono, f"len f(k) = len p_k >= len k for all k <= {len(primes)}")

    # 5. Bands d <= 4: from every k <= 1229 with d digits, iterating f leaves
    #    the band {k' <= 1229 : k' has d digits} (no cycle inside a band).
    def in_band(d, k):
        return ndigits(k) == d and k <= 1229

    worst = 0
    no_cycle = True
    for k0 in range(1, 1230):
        d = ndigits(k0)
        seen = set()
        k, steps = k0, 0
        while in_band(d, k):
            if k in seen:
                no_cycle = False
                print(f"cycle inside band {d} reached from {k0}")
                break
            seen.add(k)
            k = rev(primes[k - 1])
            steps += 1
        worst = max(worst, steps)
    check(no_cycle and worst <= 1230,
          f"every k <= 1229 leaves its digit band (at most {worst} steps; Lean fuel 1230)")

    # 6. Sanity check in the style of the harvest triage (not used by the
    #    proof): no orbit from a start 1 <= x < 20000 repeats a value before
    #    it exceeds len(primes), beyond which p_k is outside the sieve.
    no_repeat = True
    for x in range(1, 20000):
        seen = set()
        k = x
        while k <= len(primes):
            if k in seen:
                no_repeat = False
                print(f"repeated value {k} in the orbit of {x}")
                break
            seen.add(k)
            k = rev(primes[k - 1])
    check(no_repeat, f"orbits from 1 <= x < 20000 repeat no value up to {len(primes)}")

    print(f"elapsed {time.time() - t0:.1f} s")
    if failures:
        print(f"{len(failures)} check(s) FAILED")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
