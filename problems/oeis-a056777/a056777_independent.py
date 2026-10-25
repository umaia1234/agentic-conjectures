#!/usr/bin/env python3
"""OEIS A056777 search, implementation 2: independent cross-check of a056777_search.cpp.

For every n in [start, end] this computes phi(n), sigma(n), phi(n+12), sigma(n+12) exactly
and reports every composite n with phi(n+12) = phi(n) + 12 and sigma(n+12) = sigma(n) + 12;
prime n (which qualify exactly when n + 12 is prime too) are only counted.

The algorithm is deliberately different from implementation 1 (which divides each prime out
of a running cofactor with 2-adic inverses): a segmented *exponent-count* sieve. For every
prime p <= sqrt(end + 12) (2 included) and every power p^k up to the top of the segment, each
multiple of p^k in the segment increments a per-element exponent counter; a second pass over
the multiples of p then multiplies phi, sigma and the product of the prime-power parts found
so far by the tabulated phi(p^e), sigma(p^e), p^e. At the end c = m // prod is either 1 or a
single prime > sqrt(end + 12) >= sqrt(m), which contributes (c - 1) and (c + 1). All arithmetic
is exact int64 (end <= 10^12 keeps sigma(m) far below 2^63).

Block statistics use the same convention and hash as implementation 1 (block k covers
k*B < n <= (k+1)*B; exact sums of phi and sigma; hash = sum((phi*C + sigma)*(2n+1)) mod 2^64,
C = 0x9E3779B97F4A7C15), computed here with numpy's wrapping uint64 arithmetic, so the two
logs can be compared block by block.

Requires numpy and numba (local research venv; CI runs a056777_verify.py instead).
Usage: python3 a056777_independent.py --start 1 --end 10000000000 [--procs 3]
                                      [--block 1000000000] [--seg 262144]
"""
import argparse
import math
import multiprocessing as mp
import sys
import time

import numpy as np
from numba import njit

HASH_C = np.uint64(0x9E3779B97F4A7C15)


def primes_upto(limit):
    """All primes <= limit (plain sieve of Eratosthenes)."""
    flags = np.ones(limit + 1, dtype=np.bool_)
    flags[:2] = False
    for i in range(2, math.isqrt(limit) + 1):
        if flags[i]:
            flags[i * i :: i] = False
    return np.nonzero(flags)[0].astype(np.int64)


@njit(cache=False)
def phi_sigma_segment(L, W, primes, phi, sig, prod, cnt):
    """phi[i], sig[i] = phi(L+i), sigma(L+i) for 0 <= i < W (int64 arrays of length >= W)."""
    top = L + W - 1
    for i in range(W):
        phi[i] = 1
        sig[i] = 1
        prod[i] = 1
        cnt[i] = 0
    powt = np.empty(64, dtype=np.int64)
    phit = np.empty(64, dtype=np.int64)
    sigt = np.empty(64, dtype=np.int64)
    for t in range(primes.shape[0]):
        p = primes[t]
        if p * p > top:
            break
        # exponent counts: one increment per power p^k dividing m
        pk = p
        emax = 0
        while pk <= top:
            emax += 1
            j = (pk - L % pk) % pk
            while j < W:
                cnt[j] += 1
                j += pk
            if pk > top // p:
                break
            pk *= p
        powt[0] = 1
        phit[0] = 1
        sigt[0] = 1
        for e in range(1, emax + 1):
            powt[e] = powt[e - 1] * p
            phit[e] = powt[e] - powt[e - 1]
            sigt[e] = sigt[e - 1] + powt[e]
        j = (p - L % p) % p
        while j < W:
            e = cnt[j]
            phi[j] *= phit[e]
            sig[j] *= sigt[e]
            prod[j] *= powt[e]
            cnt[j] = 0
            j += p
    for i in range(W):
        c = (L + i) // prod[i]
        if c > 1:
            phi[i] *= c - 1
            sig[i] *= c + 1


def run_block(args):
    k, lo, hi, seg, primes = args
    t0 = time.time()
    phi = np.empty(seg + 12, dtype=np.int64)
    sig = np.empty(seg + 12, dtype=np.int64)
    prod = np.empty(seg + 12, dtype=np.int64)
    cnt = np.empty(seg + 12, dtype=np.uint8)
    sumphi = sumsig = h = 0
    hits, primehits = [], 0
    L = lo
    while L <= hi:
        n_cnt = min(seg, hi - L + 1)
        W = n_cnt + 12
        phi_sigma_segment(L, W, primes, phi, sig, prod, cnt)
        a, b = phi[:n_cnt], sig[:n_cnt]
        sumphi += int(a.sum())
        sumsig += int(b.sum())
        n = np.arange(L, L + n_cnt, dtype=np.uint64)
        hv = (a.astype(np.uint64) * HASH_C + b.astype(np.uint64)) * (n * np.uint64(2) + np.uint64(1))
        h = (h + int(hv.sum(dtype=np.uint64))) % (1 << 64)
        good = np.nonzero((phi[12:W] == a + 12) & (sig[12:W] == b + 12))[0]
        for i in good:
            nn = L + int(i)
            if nn > 1 and int(a[i]) == nn - 1:
                primehits += 1
            else:
                hits.append((nn, int(a[i]), int(b[i]), int(phi[i + 12]), int(sig[i + 12])))
        L += n_cnt
    return k, lo, hi, hits, primehits, sumphi, sumsig, h, time.time() - t0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--end", type=int, required=True)
    ap.add_argument("--block", type=int, default=10**9)
    ap.add_argument("--seg", type=int, default=1 << 18)
    ap.add_argument("--procs", type=int, default=3)
    a = ap.parse_args()
    if not (1 <= a.start <= a.end <= 10**12):
        sys.exit("need 1 <= start <= end <= 10^12")
    primes = primes_upto(math.isqrt(a.end + 12))
    k0, k1 = (a.start - 1) // a.block, (a.end - 1) // a.block
    tasks = [(k, max(a.start, k * a.block + 1), min(a.end, (k + 1) * a.block), a.seg, primes)
             for k in range(k0, k1 + 1)]
    print(f"# a056777_independent start={a.start} end={a.end} procs={a.procs} block={a.block} "
          f"seg={a.seg} sieve_primes<={math.isqrt(a.end + 12)} ({len(primes)} primes) "
          f"blocks={len(tasks)}", flush=True)
    t0 = time.time()
    tot_phi = tot_sig = tot_h = tot_prime = 0
    all_hits = []
    with mp.get_context("spawn").Pool(a.procs) as pool:
        for k, lo, hi, hits, ph, sp, ss, h, secs in pool.imap_unordered(run_block, tasks):
            print(f"BLOCK {k} lo={lo} hi={hi} hits={len(hits)} primehits={ph} sumphi={sp} "
                  f"sumsigma={ss} hash={h:016x} secs={secs:.2f} elapsed={time.time() - t0:.1f}")
            for x in hits:
                print("HIT %d phi=%d sigma=%d phi12=%d sigma12=%d" % x)
            sys.stdout.flush()
            tot_phi += sp
            tot_sig += ss
            tot_h = (tot_h + h) % (1 << 64)
            tot_prime += ph
            all_hits += [x[0] for x in hits]
    all_hits.sort()
    print(f"DONE start={a.start} end={a.end} hits={len(all_hits)} primehits={tot_prime} "
          f"sumphi={tot_phi} sumsigma={tot_sig} hash={tot_h:016x} secs={time.time() - t0:.1f}")
    print("HITS" + "".join(f" {x}" for x in all_hits))


if __name__ == "__main__":
    main()
