#!/usr/bin/env python3
"""Certificate checker for OEIS A007406 and the Eldar-Ordowski gcd conjecture.

Standard library only (Python >= 3.8).

Notation: H2(m) = sum_{k=1}^m 1/k^2, a(m) = |numerator of H2(m)| (A007406),
v_q = q-adic valuation.  Conjecture (A007406, Eldar-Ordowski 2019): for n > 3,
gcd(n, a(n-1)) = n if n is prime and 1 otherwise.

Checks (each one is optional; the defaults are the CI run):
  --fraction-max N  definitional check with fractions.Fraction, 3 < n <= N.
  --direct-max N    the same statement through the scaled integers
                    B(m) = lcm(1..m)^2 * H2(m), 3 < n <= N.
  --tree-max Q      Boyd-tree certificate for every prime 5 <= q <= Q: verify
                    v_q(H2(m)) <= 2 on a finite set T of indices m containing
                    1..q-1 and closed under m -> q*m + r (0 <= r < q) at the
                    nodes with v_q(H2(m)) = 2.  The Lean lemma
                    AgenticConjectures.OeisA007406.padicValRat_H2_le_two_of_tree
                    turns this into v_q(H2(m)) <= 2 for every m >= 1.
  --hits FILE...    verify and expand the root hits that the C scanners
                    a007406_roots_mont.c / a007406_roots_lin.c report for larger
                    q (two files: also require identical hit lists).
  --self-test       compare the q-adic machinery with exact fractions.

Tree arithmetic: H2(m) is q-integral for m < q.  For a node s with
v_q(H2(s)) = 2 the children satisfy (Lean: H2_eq_U_add)
    H2(q s + r) = U(q s) + sum_{rho=1}^{r} (q s + rho)^-2 + H2(s) / q^2,
where U(q s) = sum_{i<s} sum_{rho=1}^{q-1} (q i + rho)^-2 is evaluated mod q^P
by the expansion
    U(q s) = sum_{j<P} (-1)^j (j+1) q^j F_j(s) A_{j+2}   (mod q^P),
    F_j(s) = sum_{i=0}^{s-1} i^j,  A_t = sum_{rho=1}^{q-1} rho^-t.
Each level costs two q-adic digits of precision; running out of precision is
reported as an error, never as a pass.
"""
import argparse
import sys
import time
from fractions import Fraction
from itertools import accumulate
from math import comb, factorial, gcd


class CheckFailure(Exception):
    pass


def spf_table(n):
    """Smallest prime factor of every integer 0..n (spf[0] = spf[1] = 0)."""
    spf = list(range(n + 1))
    spf[0] = spf[1] = 0
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def factor(n, spf):
    out = []
    while n > 1:
        p, e = spf[n], 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(2, n + 1) if sieve[i]]


def expected_gcd(n, spf):
    return n if spf[n] == n else 1


def vq(x, q, cap):
    """q-adic valuation of the integer x, capped at cap (x = 0 gives cap)."""
    if x == 0:
        return cap
    v = 0
    while v < cap and x % q == 0:
        x //= q
        v += 1
    return v


# ---------------------------------------------------------------------------
# Part A: definitional check with exact fractions.

def check_fraction(nmax, spf):
    h = Fraction(0)
    for m in range(1, nmax):
        h += Fraction(1, m * m)
        n = m + 1
        if n > 3 and gcd(n, abs(h.numerator)) != expected_gcd(n, spf):
            raise CheckFailure(f"fraction check: gcd(n, a(n-1)) wrong at n={n}")
    return max(0, nmax - 3)


# ---------------------------------------------------------------------------
# Part B: scaled integers B(m) = L(m)^2 H2(m), L(m) = lcm(1..m).
# v_q(a(m)) = max(0, v_q(B(m)) - 2 v_q(L(m))).

def check_direct(nmax, spf, progress=0):
    L2, B = 1, 0
    for m in range(1, nmax):
        p = spf[m]
        if m > 1:
            k = m
            while k % p == 0:
                k //= p
            if k == 1:  # m is a power of the prime p: L(m) = p L(m-1)
                L2 *= p * p
                B *= p * p
        B += L2 // m // m  # exact: m^2 divides L(m)^2
        n = m + 1
        if n <= 3:
            continue
        rn = B % n  # for q | n: q | B iff q | rn (one cheap pass over B)
        g = 1
        for q, e in factor(n, spf):
            if rn % q:
                continue  # v_q(B) = 0, so v_q(a(m)) = 0
            eL = 0  # v_q(L(m)) = floor(log_q m)
            while q ** (eL + 1) <= m:
                eL += 1
            cap = 2 * eL + e
            va = max(0, vq(B % q ** cap, q, cap) - 2 * eL)
            g *= q ** min(e, va)
        if g != expected_gcd(n, spf):
            raise CheckFailure(f"direct check: gcd(n, a(n-1)) = {g} at n={n}")
        if progress and n % progress == 0:
            print(f"  direct: n={n} ok", flush=True)
    return max(0, nmax - 3)


# ---------------------------------------------------------------------------
# Part C: Boyd tree.

def stirling2_rows(jmax):
    rows = [[1]]
    for j in range(1, jmax + 1):
        prev = rows[-1] + [0]
        rows.append([0] + [l * prev[l] + prev[l - 1] for l in range(1, j + 1)])
    return rows


class QAdicTree:
    """Exact q-adic evaluation of the Boyd tree of one prime q >= 5."""

    def __init__(self, q, precision):
        self.q, self.P = q, precision
        M = q ** precision
        inv = [pow(rho, -1, M) for rho in range(1, q)]
        cur = [x * x % M for x in inv]
        self.A = {}
        for t in range(2, precision + 2):
            self.A[t] = sum(cur) % M
            cur = [c * x % M for c, x in zip(cur, inv)]
        self.S2 = stirling2_rows(precision)

    def F(self, j, s):
        """sum_{i=0}^{s-1} i^j (with 0^0 = 1), via Stirling numbers."""
        return sum(self.S2[j][l] * factorial(l) * comb(s, l + 1) for l in range(j + 1))

    def U_block(self, s, P):
        """U(q s) mod q^P, P <= self.P."""
        q = self.q
        return sum((-1) ** j * (j + 1) * q ** j * self.F(j, s) * self.A[j + 2]
                   for j in range(P)) % q ** P

    def H2_root(self, m, P):
        """H2(m) mod q^P for 1 <= m < q."""
        M = self.q ** P
        return sum(pow(k, -2, M) for k in range(1, m + 1)) % M

    def children(self, s, base, P):
        """Yield (q s + r, U(q s + r) + base mod q^P) for 0 <= r < q."""
        q, M = self.q, self.q ** P
        c = (self.U_block(s, P) + base) % M
        for r in range(q):
            if r:
                c = (c + pow(q * s + r, -2, M)) % M
            yield q * s + r, c

    def expand(self, s, hs, P, stats, depth=1):
        """Check all children of a node s with v_q(H2(s)) = 2, H2(s) = hs mod q^P."""
        q, P1 = self.q, P - 2
        if P1 < 3:
            raise PrecisionError
        # H2(q s + r) = U(q s + r) + H2(s) / q^2, and hs / q^2 = H2(s) / q^2 mod q^P1
        hist = stats["hist"].setdefault(s, [0, 0, 0])
        for m, c in self.children(s, hs // (q * q), P1):
            v = vq(c, q, P1)
            hist[min(v, 2)] += 1
            stats["nodes"] += 1
            stats["depth"] = max(stats["depth"], depth)
            if v >= 3:
                raise CheckFailure(f"counterexample: v_{q}(H2({m})) >= 3")
            if v == 2:
                stats["v2"].append(m)
                self.expand(m, c, P1, stats, depth + 1)


class PrecisionError(Exception):
    pass


def root_hits(q):
    """All m in [1, q-1] with H2(m) = 0 (mod q^2), i.e. v_q(H2(m)) >= 2."""
    M = q * q
    sums = list(accumulate(pow(k, -2, M) for k in range(1, q)))
    if sums[-1] % q:
        raise CheckFailure(f"H2(q-1) is not divisible by q={q}")
    return [m for m, s in enumerate(sums, 1) if s % M == 0]


def tree_for_hits(q, hits, precision):
    """Verify the roots `hits` of q (each must have v = 2) and expand them."""
    P = precision
    while True:
        try:
            tree = QAdicTree(q, P)
            stats = {"nodes": 0, "depth": 0, "v2": [], "hist": {}}
            for m in hits:
                hs = tree.H2_root(m, P)
                v = vq(hs, q, P)
                if v < 2:
                    raise CheckFailure(f"reported hit q={q} m={m} has v={v} < 2")
                if v >= 3:
                    raise CheckFailure(f"counterexample: v_{q}(H2({m})) >= 3")
                stats["v2"].append(m)
                tree.expand(m, hs, P, stats)
            return stats
        except PrecisionError:
            P += 10


def check_tree(qmax, precision, verbose=True):
    nprimes = nodes = 0
    for q in primes_upto(qmax):
        if q < 5:
            continue
        hits = root_hits(q)
        nprimes += 1
        nodes += q - 1
        if hits:
            stats = tree_for_hits(q, hits, precision)
            nodes += stats["nodes"]
            if verbose:
                print(f"  tree q={q}: root hits {hits}, {stats['nodes']} child nodes, "
                      f"depth {stats['depth']}, v=2 nodes {stats['v2']}")
    return nprimes, nodes


def parse_hits(path):
    hits, summary = set(), {}
    with open(path) as f:
        for line in f:
            w = line.split()
            if w and w[0] == "hit":
                hits.add((int(w[1]), int(w[2])))
            elif w and w[0] == "summary":
                summary = dict(x.split("=", 1) for x in w[1:])
    if not summary:
        raise CheckFailure(f"{path}: no summary line (incomplete run?)")
    return hits, summary


def check_hits(paths, precision):
    runs = [parse_hits(p) for p in paths]
    hits, summary = runs[0]
    for other_hits, other_summary in runs[1:]:
        if other_hits != hits:
            raise CheckFailure(f"hit lists differ: {sorted(hits ^ other_hits)}")
        for key in ("qmin", "qmax", "primes", "sum_q", "roots_v>=1(m<q-1)", "roots_v>=2"):
            if other_summary.get(key) != summary.get(key):
                raise CheckFailure(f"summaries differ in {key}")
    for s in [s for _, s in runs]:
        if s.get("wolstenholme_congruence_failures") != "0" or s.get("roots_v>=3", "0") != "0":
            raise CheckFailure("a scanner reported a failure")
    by_q = {}
    for q, m in sorted(hits):
        by_q.setdefault(q, []).append(m)
    for q, ms in by_q.items():
        M = q * q
        for m in ms:  # independent recomputation of the root value
            if sum(pow(k, -2, M) for k in range(1, m + 1)) % M:
                raise CheckFailure(f"reported hit q={q} m={m} is not a root mod q^2")
        t0 = time.time()
        stats = tree_for_hits(q, ms, precision)
        print(f"  hits q={q}: roots {ms}, {stats['nodes']} child nodes, depth "
              f"{stats['depth']}, v=2 nodes {stats['v2']} ({time.time() - t0:.1f}s)")
        for node, (n0, n1, n2) in sorted(stats["hist"].items()):
            print(f"    children of {node}: v=0: {n0}, v=1: {n1}, v=2: {n2}")
    print(f"hits: {len(hits)} root hits for {summary['primes']} primes "
          f"{summary['qmin']}..{summary['qmax']} (from {len(paths)} scanner run(s)) verified")


# ---------------------------------------------------------------------------
# Self-test of the q-adic machinery against exact fractions.

def frac_mod(x, M):
    return x.numerator * pow(x.denominator, -1, M) % M


def self_test():
    for q in (5, 7, 11, 13):
        P = 6
        M = q ** P
        tree = QAdicTree(q, P)
        u = Fraction(0)
        for s in range(1, 3 * q + 2):
            u += sum(Fraction(1, (q * (s - 1) + rho) ** 2) for rho in range(1, q))
            if tree.U_block(s, P) != frac_mod(u, M):
                raise CheckFailure(f"self-test: U({q}*{s}) expansion wrong")
        for s in (1, 2, q - 1, q, q * q + 3):
            us = sum(Fraction(1, k * k) for k in range(1, q * s + q) if k % q)
            for m, c in reversed(list(tree.children(s, 0, P))):
                if c != frac_mod(us, M):
                    raise CheckFailure(f"self-test: U({m}) child value wrong")
                us -= Fraction(1, m * m) if m % q else 0
        for m in range(1, q):
            h = sum(Fraction(1, k * k) for k in range(1, m + 1))
            if tree.H2_root(m, P) != frac_mod(h, M):
                raise CheckFailure("self-test: root value wrong")
    # End to end: the tree's v = 2 nodes are exactly the m <= bound with
    # v_q(H2(m)) >= 2 (brute force with fractions).
    for q, bound in ((5, 700), (7, 2500), (11, 1400), (13, 2300)):
        h, brute = Fraction(0), []
        for m in range(1, bound + 1):
            h += Fraction(1, m * m)
            num, den = h.numerator, h.denominator
            if vq(num, q, 3) - vq(den, q, 10 ** 6) >= 2:
                brute.append(m)
        hits = root_hits(q)
        tree_nodes = tree_for_hits(q, hits, 15)["v2"] if hits else []
        if sorted(x for x in tree_nodes if x <= bound) != brute:
            raise CheckFailure(f"self-test: tree for q={q} disagrees with brute force")
    print("self-test: q-adic expansion, root values and trees (q=5,7,11,13) agree "
          "with exact fractions")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--fraction-max", type=int, default=0)
    ap.add_argument("--direct-max", type=int, default=0)
    ap.add_argument("--tree-max", type=int, default=0)
    ap.add_argument("--hits", nargs="+", metavar="FILE")
    ap.add_argument("--precision", type=int, default=15)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--progress", type=int, default=0, help="direct: print every N")
    args = ap.parse_args()
    try:
        if args.self_test:
            t0 = time.time()
            self_test()
            print(f"  ({time.time() - t0:.1f}s)")
        spf = spf_table(max(args.fraction_max, args.direct_max, 4))
        if args.fraction_max:
            t0 = time.time()
            k = check_fraction(args.fraction_max, spf)
            print(f"fraction: gcd(n, a(n-1)) = A089026(n) for 3 < n <= {args.fraction_max} "
                  f"({k} values, {time.time() - t0:.1f}s)")
        if args.direct_max:
            t0 = time.time()
            k = check_direct(args.direct_max, spf, args.progress)
            print(f"direct: gcd(n, a(n-1)) = A089026(n) for 3 < n <= {args.direct_max} "
                  f"({k} values, {time.time() - t0:.1f}s)")
        if args.tree_max:
            t0 = time.time()
            nprimes, nodes = check_tree(args.tree_max, args.precision)
            print(f"tree: v_q(H2(m)) <= 2 for all m >= 1 and all {nprimes} primes "
                  f"5 <= q <= {args.tree_max} ({nodes} tree nodes, {time.time() - t0:.1f}s)")
        if args.hits:
            t0 = time.time()
            check_hits(args.hits, args.precision)
            print(f"  ({time.time() - t0:.1f}s)")
    except CheckFailure as e:
        print(f"FAIL: {e}")
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
