#!/usr/bin/env python3
"""Generate certified previous-prime gaps for OEIS A297707.

a(n) = prod_{k=1}^{n-1} n!_k with n!_k = prod_{0 <= j <= (n-1)/k} (n - j k),
g(n) = a(n) - prevprime(a(n)).

Every prime p <= n divides n! | a(n) and every prime factor of a(n) is <= n.
So for 1 <= h the number a(n) - h is divisible by every prime p <= n that
divides h; such h are "inadmissible" and need no stored witness.  For every
admissible h < g(n) (h = 1 or all prime factors of h exceed n) one record
stores an explicit compositeness witness for a(n) - h:

  * "factor": a sieve prime q in (n, sieve_bound] with q | a(n) - h;
  * "fermat2": 2^(N-1) mod N != 1 for N = a(n) - h (Fermat's little theorem);
  * "fermat_other": [h, b] with b^(N-1) mod N != 1 (never needed so far).

The endpoint a(n) - g(n) is found with GMP's BPSW test and then proved prime
by a PARI/GP ECPP certificate (primecert), immediately checked with
primecertisvalid.  Long runs are split into resumable partial certificates.
(g(n) = 1, where N + 1 = a(n) is fully factored and an N+1 proof would be
cheaper, happens only for n = 3 in the range treated here.)

Subcommands (records live in OUT/records/n<n>.json, certificates in
OUT/certs/n<n>.gp):

  search N_LO N_HI   gap + witnesses (endpoint only BPSW-screened)
  prove  N_LO N_HI   endpoint primality proof (ECPP certificate)
  merge              OUT/a297707_gaps.jsonl, one line per record

Requires gmpy2; the ECPP step requires PARI/GP (`gp`, run here with 2.19.0
and nbthreads = 1, which makes the certificates reproducible).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
import time
from pathlib import Path

import gmpy2


def a297707(n: int) -> gmpy2.mpz:
    value = gmpy2.mpz(1)
    for k in range(1, n):
        for term in range(n, 0, -k):
            value *= term
    return value


def primes_upto(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = b"\x00" * ((limit - p * p) // p + 1)
    return [i for i in range(limit + 1) if sieve[i]]


def sha256_decimal(value: int | gmpy2.mpz) -> str:
    return hashlib.sha256(str(value).encode("ascii")).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def is_small_prime(m: int) -> bool:
    if m < 2:
        return False
    return all(m % d for d in range(2, math.isqrt(m) + 1))


def search(n: int, primes: list[int], sieve_bound: int) -> dict:
    started = time.time()
    value = a297707(n)
    small = [p for p in primes if p <= n]
    large = [p for p in primes if n < p <= sieve_bound]
    limit = min(8 * int(gmpy2.log(value)) + 1000, int(value) - 3)
    while True:
        admissible = bytearray(b"\x01") * (limit + 1)
        admissible[0] = 0
        for p in small:
            admissible[p::p] = b"\x00" * (limit // p)
        factor = [0] * (limit + 1)
        for q in large:
            residue = int(value % q)  # nonzero: every prime factor of a(n) is <= n
            for h in range(residue, limit + 1, q):
                if admissible[h] and not factor[h] and value - h > q:
                    factor[h] = q
        factors: list[list[int]] = []
        fermat2: list[int] = []
        fermat_other: list[list[int]] = []
        gap = 0
        for h in range(1, limit + 1):
            if not admissible[h]:
                continue
            if factor[h]:
                factors.append([h, factor[h]])
                continue
            candidate = value - h
            if gmpy2.powmod(2, candidate - 1, candidate) != 1:
                fermat2.append(h)
                continue
            if gmpy2.is_bpsw_prp(candidate):
                gap = h
                break
            for base in (3, 5, 7, 11, 13, 17, 19, 23):
                if gmpy2.powmod(base, candidate - 1, candidate) != 1:
                    fermat_other.append([h, base])
                    break
            else:
                raise RuntimeError(f"n={n} h={h}: no Fermat witness among small bases")
        if gap:
            break
        if limit >= value - 3:
            raise RuntimeError(f"n={n}: no prime found below a(n)")
        limit = min(2 * limit, int(value) - 3)
    prime = value - gap
    return {
        "n": n,
        "digits": len(str(value)),
        "a_sha256": sha256_decimal(value),
        "g": gap,
        "g_kind": "one" if gap == 1 else ("prime" if is_small_prime(gap) else "composite"),
        "endpoint_digits": len(str(prime)),
        "endpoint_sha256": sha256_decimal(prime),
        "sieve_bound": sieve_bound,
        "admissible_below_g": len(factors) + len(fermat2) + len(fermat_other),
        "factor": factors,
        "fermat2": fermat2,
        "fermat_other": fermat_other,
        "endpoint": {"method": "bpsw-only"},
        "search_seconds": round(time.time() - started, 3),
    }


# Note: PARI/GP 2.19.0 segfaults on `C = primecert(C)` when C < 2^64 (the
# certificate is the input itself), so input and output variables differ.
GP_ECPP = r"""
default(nbthreads, {threads});
N = read("{nfile}");
X = if ({resume}, read("{partial}"), N);
qlast(V) = my(e = V[#V]); (e[1] + 1 - e[2]) / e[3];
targets = [{targets}];
{{
for (i = 1, #targets,
  b = targets[i];
  if (type(X) == "t_VEC" && qlast(X) <= 2^b, next);
  t0 = getwalltime();
  Y = primecert(X, , b);
  if (Y === 0, print("NOTPRIME"); quit);
  X = Y;
  writebin("{partial}.tmp", X);
  system("mv {partial}.tmp {partial}");
  print("stage ", b, " ms ", getwalltime() - t0, " steps ", #X);
);
}}
t0 = getwalltime();
C = primecert(X);
if (C === 0, print("NOTPRIME"); quit);
print("final ms ", getwalltime() - t0);
ok = primecertisvalid(C) && if (type(C) == "t_INT", C == N, C[1][1] == N);
print("VALID ", ok, " steps ", if (type(C) == "t_INT", 0, #C));
if (ok, write("{certfile}.tmp", C); system("mv {certfile}.tmp {certfile}"));
"""


def ecpp(n: int, prime: gmpy2.mpz, out: Path, threads: int, gp: str) -> dict:
    certs = out / "certs"
    work = out / "work"
    certs.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    nfile = work / f"n{n}.txt"
    nfile.write_text(f"{prime}\n")
    certfile = certs / f"n{n}.gp"
    partial = work / f"n{n}.partial.bin"
    bits = int(gmpy2.bit_length(prime))
    targets = [int(bits * f) for f in (0.85, 0.7, 0.55, 0.4, 0.25) if bits * f > 500]
    resumed = partial.exists()
    script = GP_ECPP.format(
        threads=threads,
        nfile=nfile,
        resume=int(resumed),
        partial=partial,
        targets=",".join(map(str, targets)),
        certfile=certfile,
    )
    started = time.time()
    try:
        run = subprocess.run(
            [gp, "-q", "-f", "-s", "1G", "--default", "parisizemax=8G"],
            input=script,
            capture_output=True,
            text=True,
            check=True,
        )
    finally:  # account for interrupted attempts too
        seconds = time.time() - started
        with open(work / f"n{n}.elapsed", "a") as handle:
            handle.write(f"{seconds:.1f}\n")
    total = sum(float(x) for x in (work / f"n{n}.elapsed").read_text().split())
    log = [line.strip() for line in (run.stdout + run.stderr).splitlines() if line.strip()]
    valid = [line for line in log if line.startswith("VALID ")]
    if len(valid) != 1 or not valid[0].startswith("VALID 1") or not certfile.exists():
        raise RuntimeError(f"n={n}: ECPP failed:\n{run.stdout}\n{run.stderr}")
    return {
        "method": "ecpp-pari",
        "cert_file": f"certs/n{n}.gp",
        "cert_sha256": sha256_file(certfile),
        "cert_bytes": certfile.stat().st_size,
        "cert_steps": int(valid[-1].split()[-1]),
        "seconds": round(seconds, 1),
        "seconds_all_attempts": round(total, 1),
        "threads": threads,
        "resumed": resumed,
        "log": " | ".join(log),
    }


def record_path(out: Path, n: int) -> Path:
    return out / "records" / f"n{n}.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["search", "prove", "merge"])
    parser.add_argument("n_lo", type=int, nargs="?", default=3)
    parser.add_argument("n_hi", type=int, nargs="?", default=250)
    parser.add_argument("--out", type=Path, default=Path("a297707_out"))
    parser.add_argument("--sieve-bound", type=int, default=10_000_000)
    parser.add_argument("--stride", type=int, default=1, help="process n_lo, n_lo+stride, ...")
    parser.add_argument("--threads", type=int, default=1, help="PARI nbthreads for ECPP")
    parser.add_argument("--pari", default="gp", help="PARI/GP executable")
    args = parser.parse_args()
    sys.set_int_max_str_digits(0)
    (args.out / "records").mkdir(parents=True, exist_ok=True)

    if args.command == "merge":
        lines = []
        for path in sorted((args.out / "records").glob("n*.json"), key=lambda p: int(p.stem[1:])):
            lines.append(json.dumps(json.loads(path.read_text()), separators=(",", ":")))
        (args.out / "a297707_gaps.jsonl").write_text("\n".join(lines) + "\n")
        print(f"merged {len(lines)} records")
        return

    ns = range(args.n_lo, args.n_hi + 1, args.stride)
    if args.command == "search":
        primes = primes_upto(args.sieve_bound)
        for n in ns:
            record = search(n, primes, args.sieve_bound)
            record_path(args.out, n).write_text(json.dumps(record) + "\n")
            print(
                f"n={n} digits={record['digits']} g={record['g']} kind={record['g_kind']} "
                f"factor={len(record['factor'])} fermat={len(record['fermat2'])} "
                f"t={record['search_seconds']}s",
                flush=True,
            )
        return

    for n in ns:
        path = record_path(args.out, n)
        record = json.loads(path.read_text())
        if record["endpoint"]["method"] != "bpsw-only":
            continue
        prime = a297707(n) - record["g"]
        assert sha256_decimal(prime) == record["endpoint_sha256"]
        record["endpoint"] = ecpp(n, prime, args.out, args.threads, args.pari)
        path.write_text(json.dumps(record) + "\n")
        print(f"n={n} proved via {record['endpoint']['method']} "
              f"in {record['endpoint']['seconds']}s", flush=True)


if __name__ == "__main__":
    main()
