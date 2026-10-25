#!/usr/bin/env python3
"""Exact check of Ordowski's conjecture on OEIS A108866 for 3 < n <= N.

Let E_n = -2/n + sum_{k=1}^n 2^k/k.  The conjecture says that for n > 3,
n^2 divides the reduced numerator of E_n if and only if n is prime.

Three computations are run and cross-checked:

* literal: E_n as a fractions.Fraction, numerator tested modulo n^2
  (only for n <= --literal-limit, because Fraction arithmetic is slow);
* exact valuations (method A): S_n = A_n / D_n with D_n = lcm(1..n) kept as
  unreduced integers; for every prime q | n the q-adic valuation of
  E_n = (A_n - 2 D_n / n) / D_n is read off A_n - 2 D_n / n modulo
  q^(L + 2a), where L = v_q(D_n) and a = v_q(n);
* q-adic sums (method B, independent): for each prime q, running sums of
  2^k q^L / k modulo q^(3L) (L = floor(log_q N)), kept as a fraction num / den
  with den a q-adic unit, so no modular inverse is needed.

Methods A and B produce the capped valuation min(v_q(E_n), 2 v_q(n)) for every
pair (n, q) with q prime, q | n.  Since E_n is a nonzero rational,
n^2 | numerator(E_n) iff v_q(E_n) >= 2 v_q(n) for every prime q | n.  The
script checks that A and B agree on every pair, that the literal test agrees
with the valuation verdicts, and that the verdict is "n is prime" for every
3 < n <= N.  It needs only the Python standard library (gmpy2 is used for
method A when --gmpy2 is given and the module is installed) and exits nonzero
on any disagreement.  Method B is quadratic in N; --skip-qadic leaves it out
for large runs, which are cross-checked against the output of
a108866_qadic.cpp with --compare instead.

The script also lists the composites 3 < n <= N to which none of the converse
theorems of AgenticConjectures/OeisA108866.lean applies (their hypotheses are
evaluated exactly modulo q); this report is informational and does not affect
the exit status.
"""

import argparse
import sys
import time
from fractions import Fraction


def smallest_prime_factors(limit):
    """Return spf[0..limit] with spf[n] the least prime factor of n (n >= 2)."""
    spf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def factorization(n, spf):
    """Return [(q, a), ...] with n = prod q^a, q increasing."""
    out = []
    while n > 1:
        q = spf[n]
        a = 0
        while n % q == 0:
            n //= q
            a += 1
        out.append((q, a))
    return out


def floor_log(q, n):
    """Largest L with q^L <= n."""
    L = 0
    while q ** (L + 1) <= n:
        L += 1
    return L


def valuation_capped(x, q, cap):
    """min(v_q(x), cap) for an integer x (v_q(0) = infinity)."""
    v = 0
    while v < cap and x % q == 0:
        x //= q
        v += 1
    return v


def exact_valuations(limit, spf, integer=int):
    """Method A: yield (n, [(q, a, capped v_q(E_n))]) for 4 <= n <= limit."""
    A, D = integer(0), integer(1)
    for n in range(1, limit + 1):
        fac = factorization(n, spf)
        if len(fac) == 1:  # n is a prime power: lcm gains one factor q
            q = fac[0][0]
            A *= q
            D *= q
        Dn = D // n
        A += Dn << n
        if n <= 3:
            continue
        X = A - 2 * Dn  # E_n = X / D
        row = []
        for q, a in fac:
            L = floor_log(q, n)  # v_q(D_n)
            r = int(X % q ** (L + 2 * a))
            row.append((q, a, valuation_capped(r, q, L + 2 * a) - L))
        yield n, row


def qadic_valuations(limit, primes):
    """Method B: per-prime running sums modulo q^(3L), L = floor(log_q limit)."""
    table = {}
    for q in primes:
        last = (limit // q) * q
        if last < 4:
            continue
        L = floor_log(q, limit)
        M = q ** (3 * L)
        qpow = [q ** i for i in range(L + 1)]
        num, den, pow2 = 0, 1, 1  # sum_{j<=k} 2^j q^L / j == num / den (mod M)
        for k in range(1, last + 1):
            pow2 = pow2 * 2 % M
            kp, v = k, 0
            while kp % q == 0:
                kp //= q
                v += 1
            num = (num * kp + pow2 * qpow[L - v] * den) % M
            den = den * kp % M
            if v and k >= 4:
                # q^L E_k = (num * kp - 2 q^(L - v) den) / (den * kp), denominator a unit
                z = (num * kp - 2 * qpow[L - v] * den) % M
                w = valuation_capped(z, q, 3 * L)
                table[(k, q)] = min(w - L, 2 * v)
    return table


def lean_uncovered(limit, spf):
    """Composites 3 < n <= limit to which no converse theorem of the Lean module applies.

    The families are not_modEq_of_even, not_modEq_of_three_dvd, not_modEq_of_top_digit and
    not_modEq_of_mul_pow.  For an odd prime q | n write n = c q^e + r with q^e <= n < q^(e+1).
    Since c < q, q divides a(c) = numerator(sum_{k<=c} 2^k/k) iff that sum is 0 mod q, and q
    divides numerator(E_c) iff E_c = sum_{k<=c} 2^k/k - 2/c is 0 mod q.
    """
    sums = {}  # q -> [sum_{k<=c} 2^k/k mod q for c = 0, 1, ...]

    def partial(q, c):
        s = sums.setdefault(q, [0])
        while len(s) <= c:
            k = len(s)
            s.append((s[-1] + pow(2, k, q) * pow(k, -1, q)) % q)
        return s[c]

    out = []
    for n in range(4, limit + 1):
        if spf[n] == n or n % 2 == 0:
            continue
        fac = factorization(n, spf)
        if n % 3 == 0 and len(fac) > 1:
            continue
        for q, _ in fac:
            c, r = divmod(n, q ** floor_log(q, n))
            if r and partial(q, c):
                break  # not_modEq_of_top_digit
            if not r and (partial(q, c) - 2 * pow(c, -1, q)) % q:
                break  # not_modEq_of_mul_pow
        else:
            out.append(n)
    return out


def literal_verdicts(limit):
    """Literal test: Fraction arithmetic, numerator modulo n^2."""
    out = {}
    s = Fraction(0)
    for n in range(1, limit + 1):
        s += Fraction(2 ** n, n)
        if n > 3:
            e = s - Fraction(2, n)
            out[n] = e.numerator % (n * n) == 0
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--limit", type=int, default=10000, help="check 3 < n <= LIMIT")
    parser.add_argument("--literal-limit", type=int, default=3000,
                        help="run the Fraction test for n <= this bound (0 disables)")
    parser.add_argument("--skip-qadic", action="store_true",
                        help="skip method B (quadratic in LIMIT)")
    parser.add_argument("--gmpy2", action="store_true",
                        help="use gmpy2 integers in method A if gmpy2 is installed")
    parser.add_argument("--dump", metavar="FILE",
                        help="write method A's capped valuations as lines 'n q v'")
    parser.add_argument("--compare", metavar="FILE",
                        help="check every line 'n q v' of FILE (sorted by n, then q; e.g. the "
                             "output of a108866_qadic.cpp) against method A")
    args = parser.parse_args()
    N = args.limit
    if N < 4:
        parser.error("--limit must be at least 4")

    integer = int
    if args.gmpy2:
        try:
            from gmpy2 import mpz as integer
        except ImportError:
            print("gmpy2 not available; using Python integers")

    t0 = time.time()
    spf = smallest_prime_factors(N)
    lit_limit = min(N, args.literal_limit)
    literal = literal_verdicts(lit_limit) if lit_limit >= 4 else {}
    t1 = time.time()
    b_table = None
    if not args.skip_qadic:
        b_table = qadic_valuations(N, [q for q in range(2, N + 1) if spf[q] == q])
    t2 = time.time()

    errors = []
    dump = open(args.dump, "w") if args.dump else None
    other = open(args.compare) if args.compare else None

    def next_line():
        line = other.readline()
        return tuple(map(int, line.split())) if line else None

    pending, last, compared = (next_line() if other else None), (0, 0), 0
    pairs = composites = solutions = 0
    min_prime_val = None  # least v_p(E_p) over primes p >= 5, capped at 2
    for n, row in exact_valuations(N, spf, integer):
        while pending is not None and pending[0] <= n:  # merge with the --compare file
            cn, cq, cv = pending
            mine = {q: v for q, _, v in row}.get(cq) if cn == n else None
            if (cn, cq) <= last or mine != cv:
                errors.append(f"--compare line '{cn} {cq} {cv}': method A gives {mine}")
            last, compared, pending = (cn, cq), compared + 1, next_line()
        verdict = all(v >= 2 * a for _, a, v in row)
        is_prime = spf[n] == n
        composites += not is_prime
        solutions += verdict
        if is_prime:
            v = row[0][2]
            min_prime_val = v if min_prime_val is None else min(min_prime_val, v)
        if verdict != is_prime:
            errors.append(f"n={n}: n^2 | numerator is {verdict}, n prime is {is_prime}")
        if n in literal and literal[n] != verdict:
            errors.append(f"n={n}: literal test {literal[n]} vs valuation test {verdict}")
        for q, _, v in row:
            pairs += 1
            if dump:
                dump.write(f"{n} {q} {v}\n")
            if b_table is not None and b_table.get((n, q)) != v:
                errors.append(f"(n, q)=({n}, {q}): method A {v}, method B {b_table.get((n, q))}")
    if dump:
        dump.close()
    if other:
        if pending is not None:
            errors.append(f"--compare line {pending} lies outside 3 < n <= {N}")
        other.close()
    if b_table is not None and len(b_table) != pairs:
        errors.append(f"method B computed {len(b_table)} pairs, method A {pairs}")
    uncovered = lean_uncovered(N, spf)
    t3 = time.time()

    print(f"range: 3 < n <= {N}; primes {solutions}, composites {composites}")
    print(f"(n, q) pairs from method A: {pairs}; "
          + ("compared with method B" if b_table is not None else "method B skipped"))
    print(f"literal Fraction test run for n <= {lit_limit}")
    if other:
        print(f"lines of {args.compare} checked against method A: {compared}")
    print(f"min over primes 5 <= p <= {N} of min(v_p(E_p), 2): {min_prime_val}")
    powers = [n for n in uncovered if len(factorization(n, spf)) == 1]
    others = [n for n in uncovered if len(factorization(n, spf)) > 1]
    print(f"composites outside the Lean families: {len(uncovered)} "
          f"({len(powers)} odd prime powers; others: {others})")
    print(f"timing: literal {t1 - t0:.1f}s, B {t2 - t1:.1f}s, A + coverage {t3 - t2:.1f}s")
    if errors:
        for line in errors[:20]:
            print("ERROR:", line)
        print(f"FAILED with {len(errors)} errors")
        return 1
    print("OK: for 3 < n <= N, n^2 divides numerator(E_n) exactly when n is prime; "
          "all computations agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
