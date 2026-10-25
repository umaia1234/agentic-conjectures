#!/usr/bin/env python3
"""Re-verify the S(k) tables for arXiv:2501.03234 (theta-arithmetic-sum).

S'(h, k) = sum_{j=1}^{k-1} (-1)^(j + 1 + floor(hj/k)) and S(k) = sum_{h=1}^{k-1} S'(h, k).

Default mode (CI, a few seconds to a minute):

1. Exact integer checks, in pure Python, of every identity the fast programs rely on
   (DETAILS.md): the continued-fraction formula for 12k s(h,k) used by method A, the
   reciprocity s4(v,k) = k/v - 1 + 2 s3(k mod v, v) and s3 = 2s(h,k) - 4s(2h,k) used by
   method B, Sitaramachandrarao's formula for S'(2m,k), the closed forms of S(k) (Dedekind
   form, odd-row form, lattice form, k H(k) - (k-1)/2 + 2 V(k)) against the definition for
   every prime k <= 400, each claim in the proof of the upper bound
   |S(k)| < 6k(1 + ln k)^2 + 8k (Theorem 7.1) for every prime k <= 400, and (in floating
   point) the character form of S(k) and Zhang's character expansion of S'(h,k) for primes
   k <= 100. The links of Theorem 7.1 that involve logarithms are checked in floating point.
2. Compile the three C++ programs with g++ and compare, for every odd prime k <= 50000,
   method A (Dedekind form), method B (reciprocity form) and the committed table; method C
   (literal definition) for every prime k <= 2500, every k <= 1500 and the composite values
   quoted in the paper.
3. Audit the committed tables: every odd prime up to the table limit appears once, in order;
   Conjectures 1.1 and 4.1-4.3 and the upper bound |S(k)| < 6k(1 + ln k)^2 + 8k hold on every
   row; the lists published in the paper (Section 3 of arXiv v3, Section 4 of v1) are
   recomputed; summary statistics are printed.

--full additionally reruns methods A and B over the whole table and method C for every
prime k <= 30000 and every k <= 10000 (several hours; not CI-feasible).

Needs g++ and the Python package mpmath, which comes with sympy.
"""

from __future__ import annotations

import argparse
import cmath
import math
import subprocess
import sys
import tempfile
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIME_TABLE = HERE / "data" / "S_odd_primes.txt"
ALL_K_TABLE = HERE / "data" / "S_all_k_le_10000.txt"

UPSTREAM_FIRST_10 = [0, 0, 1, 2, 5, 4, 7, 10, 11, 8]  # upstream test S_fst_10
# Section 3 of arXiv:2501.03234v3 (Section 4 of v1).
PAPER_LT_2K = [2, 3, 5, 7, 11, 13, 17, 23, 29, 41, 53, 59, 83, 113, 149, 179, 233]
PAPER_LE_3K = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 131, 137, 139, 149, 163, 167, 173, 179, 193, 197, 233, 239, 251,
    257, 263, 269, 293, 317, 347, 349, 359, 383, 389, 419, 439, 443, 449, 479, 503, 509, 557,
    563, 569, 593, 599, 683, 719, 743, 797, 809, 827, 839, 863, 1013, 1019, 1049, 1103, 1229,
    1259, 1409, 1733, 1889, 1913, 2339, 2459, 2969, 3119,
]
PAPER_4K_PAIRS = [
    (32603, 126466), (33149, 126068), (34649, 134104), (34913, 137712),
    (35573, 137420), (41579, 165026), (44909, 175916), (49139, 189522),
]
PAPER_COMPOSITE = {
    945: -296, 2079: -1390, 3465: -7800, 5005: -1332, 8855: -7950, 9933: -448,
    9975: -22450, 10395: -40726, 17017: -2364, 19019: -20578,
}
PAPER_NEGATIVE_COUNT_1E4 = 151


def check(cond: bool, what: str) -> None:
    if not cond:
        raise AssertionError(what)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def factor(n: int) -> str:
    parts, d = [], 2
    while d * d <= n:
        e = 0
        while n % d == 0:
            n, e = n // d, e + 1
        if e:
            parts.append(f"{d}^{e}" if e > 1 else str(d))
        d += 1
    if n > 1:
        parts.append(str(n))
    return " * ".join(parts)


def odd_primes_upto(n: int) -> list[int]:
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytearray(len(range(p * p, n + 1, p)))
    return [p for p in range(3, n + 1, 2) if sieve[p]]


# ---------------------------------------------------------------- exact definitions

def S_literal(k: int) -> int:
    """The upstream definition with exact integer floors."""
    total = 0
    for h in range(1, k):
        for j in range(1, k):
            total += -1 if (j + 1 + (h * j) // k) % 2 else 1
    return total


def S_prime_h(h: int, k: int) -> int:
    return sum(-1 if (j + 1 + (h * j) // k) % 2 else 1 for j in range(1, k))


def s4(v: int, k: int) -> int:
    return sum(-1 if ((v * j) // k) % 2 else 1 for j in range(1, k))


def dedekind_4k2(h: int, k: int) -> int:
    """4 k^2 s(h, k) for gcd(h, k) = 1, from the definition."""
    return sum((2 * j - k) * (2 * (h * j % k) - k) for j in range(1, k))


def s3_2k(h: int, k: int) -> int:
    """2 k s3(h, k) = 2k sum_j (-1)^j ((hj/k)) for gcd(h, k) = 1."""
    return sum((-1) ** j * (2 * (h * j % k) - k) for j in range(1, k))


def x12(h: int, k: int) -> int:
    """12 k s(h, k) by the continued-fraction formula of method A (s_dedekind.cpp)."""
    r0, r1, t0, t1, alt, sgn, r = k, h, 0, 1, 0, 1, 0
    while r1:
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0 - q * r1, t1, t0 - q * t1
        alt += sgn * q
        sgn, r = -sgn, r + 1
    return h + t0 % k + k * (alt - 2 + (1 if r % 2 == 0 else -1))


def T(c: int, h: int) -> int:
    """12 h s(c, h) by Dedekind reciprocity (method B, s_hardy.cpp)."""
    if c == 1:
        return (h - 1) * (h - 2)
    num = c * c + h * h + 1 - 3 * c * h - h * T(h % c, c)
    check(num % c == 0, "T not integral")
    return num // c


def S_reciprocity(k: int) -> int:
    """Method B: S(k) = sum over odd h of s4(h, k), s4 by reciprocity."""
    total = k - 1
    for h in range(3, k - 1, 2):
        c = k % h
        num = 12 * k - 12 * h + 4 * T(c, h) - 8 * T(2 * c % h, h)
        check(num % (12 * h) == 0, "s4 not integral")
        total += num // (12 * h)
    return total


def S_dedekind(k: int) -> int:
    """Method A: S(k) = sum_{m<=n} [8 s(m,k) - 20 s(2m,k) + 8 s(4m,k)]."""
    tot = sum(8 * x12(m, k) - 20 * x12(2 * m % k, k) + 8 * x12(4 * m % k, k)
              for m in range(1, (k - 1) // 2 + 1))
    check(tot % (12 * k) == 0, "Dedekind form not integral")
    return tot // (12 * k)


def character_form(k: int) -> complex:
    """Proposition 8.1 of DETAILS.md in floating point, L(1, chi) from the digamma function.

    Also checks the expansion of S'(h, k) for even h quoted there from [Zh03, Lemma 5].
    """
    try:
        from mpmath import digamma
    except ImportError:
        sys.exit("verify.py needs the Python package mpmath, which comes with sympy "
                 "(pip install sympy)")

    qs = [q for q in range(2, k) if (k - 1) % q == 0 and is_prime(q)]
    g = next(g for g in range(2, k) if all(pow(g, (k - 1) // q, k) != 1 for q in qs))
    ind, x = {}, 1
    for e in range(k - 1):
        ind[x], x = e, x * g % k
    psi = {a: float(digamma(a / k)) for a in range(1, k)}
    total = 0j
    zhang = dict.fromkeys(range(2, k, 2), 0j)
    for t in range(1, k - 1, 2):  # chi(g) = exp(2 pi i t / (k - 1)) is odd for odd t
        chi = {a: cmath.exp(2j * math.pi * t * ind[a] / (k - 1)) for a in range(1, k)}
        L = -sum(chi[a] * psi[a] for a in range(1, k)) / k
        B = sum(a * chi[a].conjugate() for a in range(1, k)) / k
        check(abs(abs(B) - math.sqrt(k) * abs(L) / math.pi) < 1e-9 * k, f"|B_1| at {k}")
        y = 2 * chi[2].conjugate() - 1
        total += abs(L) ** 2 * abs(y) ** 2 * y * B
        for h in zhang:  # |L(1, chi chi_2^0)|^2 = |1 - chi(2)/2|^2 |L(1, chi)|^2
            zhang[h] += chi[h] * abs(1 - chi[2] / 2) ** 2 * abs(L) ** 2
    for h, z in zhang.items():
        check(abs(16 * k * z / ((k - 1) * math.pi ** 2) + S_prime_h(h, k)) < 1e-6,
              f"[Zh03, Lemma 5] at ({h},{k})")
    return 4 * k * total / ((k - 1) * math.pi ** 2)


def upper_bound_checks(k: int, lit: int) -> None:
    """Each claim in the proof of Theorem 7.1 of DETAILS.md (section 7) for a prime k > 2.

    Exact, except the links of the chain that involve logarithms.
    """
    n = (k - 1) // 2
    d = {h: dedekind_4k2(h, k) for h in range(1, k)}  # 4k^2 s(h,k)
    total_abs = sum(abs(x) for x in d.values())  # 4k^2 sum_h |s(h,k)|
    # Step 1: for c = 1, 2, 4 the residues +-cm, 1 <= m <= n, are exactly 1, ..., k-1, and
    # |s(-h,k)| = |s(h,k)|; so sum_m |s(cm,k)| = (1/2) sum_h |s(h,k)| and, by (D),
    # |S(k)| <= 18 sum_h |s(h,k)|.
    check(all(d[k - h] == -d[h] for h in range(1, k)), f"s(-h,{k}) = -s(h,{k})")
    parts = []
    for c in (1, 2, 4):
        res = [c * m % k for m in range(1, n + 1)]
        check(sorted(res + [k - x for x in res]) == list(range(1, k)), f"+-{c}m mod {k}")
        parts.append(sum(abs(d[x]) for x in res))
        check(2 * parts[-1] == total_abs, f"sum_m |s({c}m,{k})| = (1/2) sum_h |s(h,{k})|")
    check(4 * k * k * abs(lit) <= 8 * parts[0] + 20 * parts[1] + 8 * parts[2],
          f"|S({k})| <= sum_m (8|s(m,k)| + 20|s(2m,k)| + 8|s(4m,k)|)")
    check(8 * parts[0] + 20 * parts[1] + 8 * parts[2] == 18 * total_abs,
          f"18 sum_h |s(h,{k})|")
    # Steps 2 and 3, for every h: the Euclidean algorithm r_{i-1} = q_i r_i + r_{i+1} on
    # (r_0, r_1) = (k, h), the continuants Q_i = q_i Q_{i-1} + Q_{i-2} and, for each step i,
    # the quadruple (Q, Q', a, b) = (Q_{i-1}, Q_{i-2}, r_{i-1}, r_i).
    total_a, quads = 0, Counter()
    for h in range(1, k):
        qs, Q, Qp, a, b = [], 1, 0, k, h
        while b:
            q = a // b
            check(Q * a + Qp * b == k, f"k = Q_(i-1) r_(i-1) + Q_(i-2) r_i at ({h},{k})")
            check(a > b >= 1 and Q >= 1 and 0 <= Qp <= Q and q * b <= a and Q * a <= k,
                  f"quadruple at ({h},{k})")
            check((Qp == 0) == (not qs), f"Q' = 0 only at i = 1, ({h},{k})")
            quads[Q, Qp, a, b] += 1
            qs.append(q)
            Q, Qp, a, b = q * Q + Qp, Q, b, a - q * b
        check(a == 1, f"r_m = 1 at ({h},{k})")
        # Step 2: (BHK) with h h' = 1 mod k, 0 < h' < k; 0 < h + h' < 2k and
        # |sum (-1)^(i+1) q_i - 2 + (-1)^r| <= A + 3, so |s(h,k)| < (A(k/h) + 5)/12.
        r, A, hinv = len(qs), sum(qs), pow(h, -1, k)
        alt = sum(q if i % 2 == 0 else -q for i, q in enumerate(qs)) - 2 + (-1) ** r
        check(3 * d[h] == k * (h + hinv + k * alt), f"(BHK) at ({h},{k})")
        check(0 < h + hinv < 2 * k and abs(alt) <= A + 3, f"Step 2 estimates at ({h},{k})")
        check(3 * abs(d[h]) < k * k * (A + 5), f"|s({h},{k})| < (A + 5)/12")
        total_a += A
    # Facts 1-3 of Step 3.
    check(max(quads.values()) <= 2, f"Fact 1 at {k}")
    check(max(Counter((Q, b) for Q, _, _, b in quads).values()) <= 2, f"Fact 2 at {k}")
    check(all(math.gcd(Q, b) == 1 and Q * b < k and Q < k for Q, _, _, b in quads),
          f"Facts 2-3 at {k}")
    # The chain of Step 3: exact (scaled by L = lcm(1, ..., k-1)) up to the logarithms.
    L = math.lcm(*range(1, k))
    sum_ab = sum(a * (L // b) for _, _, a, b in quads)  # L sum a/b over distinct quadruples
    sum_qb = sum(k * (L // (Q * b)) for Q in range(1, k) for b in range(1, (k - 1) // Q + 1))
    sum_log = sum((1 + math.log(k / Q)) / Q for Q in range(1, k))
    check(total_a * L <= 2 * sum_ab, f"Step 3, link 1 at {k}")
    check(2 * sum_ab <= 4 * sum_qb, f"Step 3, link 2 at {k}")
    check(4 * sum_qb / L <= 4 * k * sum_log, f"Step 3, link 3 at {k}")
    check(sum_log <= (1 + math.log(k)) ** 2, f"Step 3, link 4 at {k}")
    check(total_a <= 4 * k * (1 + math.log(k)) ** 2, f"sum_h A({k}/h) <= 4k(1 + ln k)^2")
    # Conclusion: 18 sum_h |s(h,k)| < (3/2) sum_h A(k/h) + (15/2)(k-1) < 6k(1 + ln k)^2 + 8k.
    check(18 * total_abs < 6 * k * k * total_a + 30 * k * k * (k - 1), f"conclusion 1 at {k}")
    check(1.5 * total_a + 7.5 * (k - 1) < 6 * k * (1 + math.log(k)) ** 2 + 8 * k,
          f"conclusion 2 at {k}")


def identity_checks() -> None:
    t0 = time.perf_counter()
    check([S_literal(k) for k in range(10)] == UPSTREAM_FIRST_10, "upstream S_fst_10")
    # Method A: the continued-fraction evaluation of 12k s(h,k), all coprime 0 < h < k <= 500.
    for k in range(2, 501):
        for h in range(1, k):
            if math.gcd(h, k) == 1:
                check(x12(h, k) * k == 3 * dedekind_4k2(h, k), f"x12({h},{k})")
    # Method B ingredients, all coprime pairs with v odd, v < 120, k < 240.
    for v in range(3, 120, 2):
        for k in range(2, 240):
            if math.gcd(v, k) != 1:
                continue
            # s4(v,k) = k/v - 1 + 2 s3(k,v)   (times 2v)
            check(2 * v * s4(v, k) == 2 * k - 2 * v + 2 * s3_2k(k % v, v), f"recip({v},{k})")
    for k in range(3, 200, 2):
        for h in range(1, k):
            if math.gcd(h, k) == 1:
                # s3(h,k) = 2 s(h,k) - 4 s(2h,k)   (times 4k^2)
                check(2 * k * s3_2k(h, k)
                      == 2 * dedekind_4k2(h, k) - 4 * dedekind_4k2(2 * h % k, k), f"s3({h},{k})")
                # 12k s(h,k) by Dedekind reciprocity (method B) against the definition
                check(T(h, k) * k == 3 * dedekind_4k2(h, k), f"T({h},{k})")
    # Sitaramachandrarao: S'(2m,k) = 8 s(m,k) - 20 s(2m,k) + 8 s(4m,k) for odd k (times 4k^2)
    for k in range(3, 150, 2):
        for m in range(1, (k - 1) // 2 + 1):
            if math.gcd(m, k) == 1:
                check(4 * k * k * S_prime_h(2 * m, k)
                      == 8 * dedekind_4k2(m, k) - 20 * dedekind_4k2(2 * m % k, k)
                      + 8 * dedekind_4k2(4 * m % k, k), f"S'({2 * m},{k}) in Dedekind sums")
    # Closed forms of S(k) against the definition, every prime k <= 400.
    for k in odd_primes_upto(400):
        lit = S_literal(k)
        n = (k - 1) // 2
        check(all(S_prime_h(h, k) == 0 for h in range(1, k, 2)), f"S'(odd h,{k}) = 0")
        check(all(S_prime_h(k - v, k) == s4(v, k) for v in range(1, k)), f"S'(k-v,{k}) = s4")
        check(lit == sum(s4(v, k) for v in range(1, k, 2)), f"odd-row form {k}")
        check(lit == sum(-1 if ((a * b) // k) % 2 else 1
                         for a in range(1, k) for b in range(1, k)), f"square form {k}")
        check(lit == -2 * sum(-1 if ((4 * s * t) // k) % 2 else 1
                              for s in range(1, n + 1) for t in range(1, n + 1)),
              f"lattice form {k}")
        check(lit == S_dedekind(k), f"Dedekind form {k}")
        check(lit == S_reciprocity(k), f"reciprocity form {k}")
        harmonic = sum(Fraction(1, v) for v in range(1, k - 1, 2))
        vprime = sum(Fraction(s3_2k(k % v, v), 2 * v) for v in range(3, k - 1, 2))
        check(lit == k * harmonic - n + 2 * vprime, f"k H(k) - n + 2V(k) form {k}")
        # the paper's r(j,k) = sum_h (floor(hj/k) - 2 floor(hj/2k)) = k(j-1)/(2j) - s3(k mod j, j)
        for j in range(1, k - 1, 2):
            r = sum((h * j) // k - 2 * ((h * j) // (2 * k)) for h in range(1, k))
            check(2 * j * r == k * (j - 1) - s3_2k(k % j, j), f"r({j},{k})")
        upper_bound_checks(k, lit)
        # divisor terms of V(k): s3(k mod v, v) = -(v-1)^2/(4v) if v | 2k-1, + if v | 2k+1
        for v in range(3, k - 1, 2):
            if (2 * k - 1) % v == 0:
                check(Fraction(s3_2k(k % v, v), 2 * v) == Fraction(-(v - 1) ** 2, 4 * v),
                      f"divisor term 2k-1, v={v}, k={k}")
            if (2 * k + 1) % v == 0:
                check(Fraction(s3_2k(k % v, v), 2 * v) == Fraction((v - 1) ** 2, 4 * v),
                      f"divisor term 2k+1, v={v}, k={k}")
    # Proposition 8.1, the character form of S(k), and [Zh03, Lemma 5], in floating point.
    for k in odd_primes_upto(100)[1:]:
        check(abs(character_form(k) - S_literal(k)) < 1e-6, f"character form {k}")
    print(f"identities: OK ({time.perf_counter() - t0:.1f}s)")


# ---------------------------------------------------------------- tables

def read_table(path: Path) -> list[tuple[int, int]]:
    rows = []
    for line in path.read_text().splitlines():
        a, b = line.split()
        rows.append((int(a), int(b)))
    return rows


def parse_output(text: str) -> list[tuple[int, int]]:
    return [(int(a), int(b)) for a, b in (line.split() for line in text.splitlines())]


def compile_and_run(src: str, args: list[str], tmp: Path) -> str:
    exe = tmp / src.removesuffix(".cpp")
    if not exe.exists():
        subprocess.run(["g++", "-O3", "-std=c++17", str(HERE / src), "-o", str(exe)],
                       check=True, capture_output=True, text=True, timeout=120)
    done = subprocess.run([str(exe), *args], check=True, capture_output=True, text=True)
    return done.stdout


def program_checks(prime_rows, all_rows, full: bool) -> None:
    limit = prime_rows[-1][0] if full else 50000
    lit_primes = 30000 if full else 2500
    lit_all = 10000 if full else 1500
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for src in ("s_dedekind.cpp", "s_hardy.cpp"):
            t0 = time.perf_counter()
            out = parse_output(compile_and_run(src, ["3", str(limit)], tmp))
            check(out == [r for r in prime_rows if r[0] <= limit], f"{src} vs table")
            print(f"{src}: primes 3..{limit} match the table ({time.perf_counter() - t0:.1f}s)")
        t0 = time.perf_counter()
        out = parse_output(compile_and_run("s_literal.cpp", ["3", str(lit_primes)], tmp))
        check(out == [r for r in prime_rows if r[0] <= lit_primes], "literal primes vs table")
        out = parse_output(compile_and_run("s_literal.cpp", ["1", str(lit_all), "all"], tmp))
        check(out == all_rows[:lit_all], "literal all k vs table")
        for k, value in PAPER_COMPOSITE.items():
            out = parse_output(compile_and_run("s_literal.cpp", [str(k), str(k), "all"], tmp))
            check(out == [(k, value)], f"paper value S({k})")
        print(f"s_literal.cpp: primes <= {lit_primes}, all k <= {lit_all} and the paper's "
              f"composite values match ({time.perf_counter() - t0:.1f}s)")


def table_audit(prime_rows, all_rows) -> None:
    limit = prime_rows[-1][0]
    check([k for k, _ in prime_rows] == odd_primes_upto(limit), "table lists the odd primes")
    check(all_rows[:60] == [(k, S_literal(k)) for k in range(1, 61)], "all-k table head")
    check([k for k, _ in all_rows] == list(range(1, 10001)), "all-k table covers 1..10000")
    table = dict(prime_rows)
    for k, s in all_rows:
        if k % 2 == 1 and k > 2 and is_prime(k):
            check(table[k] == s, f"tables agree at {k}")
        if k in PAPER_COMPOSITE:
            check(PAPER_COMPOSITE[k] == s, f"paper value S({k}) in table")
    negatives = [k for k, s in all_rows if s < 0]
    check(len(negatives) == PAPER_NEGATIVE_COUNT_1E4, "151 negative values for k <= 10000")
    check(all(not is_prime(k) for k in negatives), "negative values only at composites")
    # Conjectures 1.1 and 4.1-4.3 on every row.
    check(all(s > 0 for _, s in prime_rows), "Conjecture 1.1")
    check(all(s > k for k, s in prime_rows if k > 5), "Conjecture 4.1")
    check(all(s > 2 * k for k, s in prime_rows if k > 233), "Conjecture 4.2")
    check(all(s > 3 * k for k, s in prime_rows if k > 3119), "Conjecture 4.3")
    ratio = max((abs(s) / (6 * k * (1 + math.log(k)) ** 2 + 8 * k), k) for k, s in prime_rows)
    check(ratio[0] < 1, "|S(k)| < 6k(1 + ln k)^2 + 8k")
    # The lists of Section 3 of the paper (k = 2 has S(2) = 1).
    rows2 = [(2, 1)] + prime_rows
    lt2 = [k for k, s in rows2 if k < 10000 and s < 2 * k]
    le3 = [k for k, s in rows2 if k < 10000 and s <= 3 * k]
    check(lt2 == PAPER_LT_2K, "17 primes below 10000 with S(k) < 2k")
    check(le3 == PAPER_LE_3K, "87 primes below 10000 with S(k) <= 3k")
    le4 = [(k, s) for k, s in prime_rows if 10000 < k <= 50000 and s <= 4 * k]
    check([r for r in le4 if r[0] > 30000] == PAPER_4K_PAIRS, "the paper's S(k) <= 4k pairs")
    print(f"table: {len(prime_rows)} odd primes 3..{limit}; S(k) > 0, > k (k > 5), > 2k "
          f"(k > 233), > 3k (k > 3119) and |S(k)| < 6k(1 + ln k)^2 + 8k on every row; paper "
          f"lists of S < 2k and S <= 3k below 10^4 reproduced; 151 negative S(k), k <= 10^4, "
          f"all composite")
    print(f"largest |S(k)| / (6k(1 + ln k)^2 + 8k) in the table: {ratio[0]:.4f} at k = {ratio[1]}")
    print(f"primes 10^4 < k <= 5*10^4 with S(k) <= 4k: {len(le4)}, from {le4[0]} to {le4[-1]}; "
          f"the {len(PAPER_4K_PAIRS)} pairs listed in the paper are exactly those with k > 30000")
    stats(prime_rows)


def stats(prime_rows) -> None:
    best = min((Fraction(s, k), k) for k, s in prime_rows if k > 5)
    print(f"min S(k)/k over primes 5 < k <= {prime_rows[-1][0]}: {best[0]} at k = {best[1]}")
    for c in (3, 4, 5, 6):
        last = max((k for k, s in prime_rows if s <= c * k), default=None)
        print(f"largest prime k in the table with S(k) <= {c}k: {last}")
    print("decade envelope of E(k) = S(k)/k - (1/2) ln k:")
    lo = 10
    while lo <= prime_rows[-1][0]:
        seg = [(s / k - 0.5 * math.log(k), k) for k, s in prime_rows if lo <= k < 10 * lo]
        if seg:
            print(f"  [{lo:>8}, {10 * lo:>8}): min {min(seg)[0]:+.3f} at {min(seg)[1]:>7}, "
                  f"max {max(seg)[0]:+.3f} at {max(seg)[1]:>7}, mean "
                  f"{sum(e for e, _ in seg) / len(seg):+.3f}")
        lo *= 10
    extremes = sorted((s / k - 0.5 * math.log(k), k) for k, s in prime_rows if k > 1000)
    for label, (e, k) in (("min", extremes[0]), ("max", extremes[-1])):
        print(f"{label} E(k) over primes k > 1000: {e:+.3f} at k = {k}; "
              f"2k - 1 = {factor(2 * k - 1)}, 2k + 1 = {factor(2 * k + 1)}")
    xs = [math.log(k) for k, _ in prime_rows if k > 1000]
    ys = [s / k for k, s in prime_rows if k > 1000]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    print(f"least squares over primes k > 1000: S(k)/k ~ {slope:.4f} ln k "
          f"{my - slope * mx:+.4f}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--full", action="store_true", help="rerun the whole table (hours)")
    args = ap.parse_args()
    prime_rows = read_table(PRIME_TABLE)
    all_rows = read_table(ALL_K_TABLE)
    identity_checks()
    program_checks(prime_rows, all_rows, args.full)
    table_audit(prime_rows, all_rows)
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
