#!/usr/bin/env python3
"""Independent p<=100000 sieve followed by enlarged-FFT PFGW checks."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import math
import re
import subprocess

from sympy import primerange

K = 201886
LIMIT = 39100
PFGW = "/tmp/pfgw.25adjA/pfgw64"
WORKERS = 16
RESIDUE = re.compile(r"is composite: RES64: \[([0-9A-F]{16})\]")


def prime_factors(n):
    factors = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def order_of_three(p):
    order = p-1
    for q in prime_factors(order):
        while order % q == 0 and pow(3, order//q, p) == 1:
            order //= q
    return order


def discrete_log_three(y, p, order):
    width = math.isqrt(order)+1
    babies = {}
    value = 1
    for j in range(width):
        babies.setdefault(value, j)
        value = value*3 % p
    stride = pow(pow(3, width, p), -1, p)
    value = y
    for i in range(width+1):
        if value in babies:
            answer = i*width+babies[value]
            if answer < order and pow(3, answer, p) == y:
                return answer
        value = value*stride % p
    return None


def independent_survivors():
    covered = bytearray(LIMIT+1)
    for p in primerange(2, 100001):
        if p == 3 or K % p == 0:
            continue
        order = order_of_three(p)
        if pow(K, order, p) != 1:
            continue
        exponent = discrete_log_three(pow(K, -1, p), p, order)
        if exponent is None or exponent > LIMIT:
            continue
        count = (LIMIT-exponent)//order+1
        covered[exponent::order] = b"\1"*count
    survivors = [m for m in range(1, LIMIT+1) if not covered[m]]
    assert len(survivors) == 1991
    return survivors


def check_exponent(m):
    expression = f"201886*3^{m}-1"
    run = subprocess.run(
        [PFGW, "-a1", "-f0", f"-q{expression}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=300,
        check=False,
    )
    match = RESIDUE.search(run.stdout)
    return (m, match.group(1)) if match else (m, None)


def main():
    survivors = independent_survivors()
    print("independent_sieve_survivors", len(survivors), flush=True)
    results = []
    failures = []
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        jobs = [pool.submit(check_exponent, m) for m in survivors]
        for completed, future in enumerate(as_completed(jobs), 1):
            m, residue = future.result()
            (results if residue else failures).append((m, residue))
            if completed % 100 == 0:
                print("checked", completed, "failures", len(failures), flush=True)

    results.sort()
    canonical = "".join(f"{m}:{residue}\n" for m, residue in results).encode()
    print("composite_results", len(results))
    print("failures", len(failures))
    print("result_sha256", hashlib.sha256(canonical).hexdigest())
    if failures:
        raise SystemExit(failures[:10])
    print("ALL_M_LT_39101_COMPOSITE_A1")


if __name__ == "__main__":
    main()
