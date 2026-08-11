#!/usr/bin/env python3
"""Reproduce and extend the nonvanishing check for OEIS A395412.

For n >= 1, let p_n be the n-th prime and P_n the n-th primorial.  A395412
counts squarefree d < p_n for which P_n/d + d is prime.

There are deliberately two levels of output:

* ``proved`` witnesses have been accepted by PARI/GP ``isprime``, which is a
  rigorous primality test (APRCL/ECPP as appropriate).
* ``screened`` witnesses have only passed GMP's BPSW probable-prime test.

The latter are useful for rapidly looking for a zero, but are not presented as
a proof.  A zero candidate would cause a full scan of every admissible d.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import time
from pathlib import Path

import gmpy2


OEIS_TERMS_1_TO_84 = [
    1, 2, 3, 5, 5, 5, 5, 2, 5, 7, 4, 7, 4, 6, 10, 3, 3, 5, 10, 6, 8,
    5, 8, 7, 9, 5, 7, 8, 9, 3, 3, 6, 3, 7, 6, 10, 6, 5, 5, 13, 6, 8,
    3, 6, 1, 6, 10, 8, 7, 7, 9, 8, 9, 7, 8, 2, 4, 6, 6, 6, 7, 7, 9,
    8, 4, 11, 9, 4, 7, 5, 5, 10, 5, 8, 6, 10, 12, 5, 6, 8, 8, 9, 7, 4,
]


def first_primes(count: int) -> list[int]:
    primes: list[int] = []
    p = 1
    for _ in range(count):
        p = int(gmpy2.next_prime(p))
        primes.append(p)
    return primes


def squarefree_table(limit: int, primes: list[int]) -> bytearray:
    is_squarefree = bytearray(b"\x01") * limit
    is_squarefree[0] = 0
    for q in primes:
        q2 = q * q
        if q2 >= limit:
            break
        count = (limit - 1 - q2) // q2 + 1
        is_squarefree[q2:limit:q2] = b"\x00" * count
    return is_squarefree


def digest_decimal(value: gmpy2.mpz) -> str:
    return hashlib.sha256(str(value).encode("ascii")).hexdigest()


class PariSession:
    """A minimal line-oriented PARI/GP session for rigorous isprime calls."""

    def __init__(self, executable: str, stack: str) -> None:
        self.process = subprocess.Popen(
            [executable, "-fq", "-s", stack],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )

    def isprime(self, value: gmpy2.mpz) -> bool:
        assert self.process.stdin is not None
        assert self.process.stdout is not None
        self.process.stdin.write(f"print(isprime({value}))\n")
        self.process.stdin.flush()
        while True:
            line = self.process.stdout.readline()
            if line == "":
                raise RuntimeError("PARI/GP terminated during isprime")
            answer = line.strip()
            if answer == "1":
                return True
            if answer == "0":
                return False
            if "error" in answer.lower() or "overflow" in answer.lower():
                raise RuntimeError(f"PARI/GP error: {answer}")

    def close(self) -> None:
        if self.process.poll() is None:
            assert self.process.stdin is not None
            self.process.stdin.write("quit\n")
            self.process.stdin.flush()
            self.process.wait()


def candidate_record(n: int, p: int, d: int, candidate: gmpy2.mpz) -> dict:
    return {
        "n": n,
        "p_n": p,
        "d": d,
        "candidate_bits": int(candidate.bit_length()),
        "candidate_decimal_sha256": digest_decimal(candidate),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prove-through", type=int, default=200)
    parser.add_argument("--screen-through", type=int, default=400)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--pari-stack", default="256M")
    parser.add_argument("--output", type=Path, default=Path("result.json"))
    args = parser.parse_args()

    if not (84 <= args.prove_through <= args.screen_through):
        parser.error("require 84 <= --prove-through <= --screen-through")
    gp = shutil.which(args.gp) if "/" not in args.gp else args.gp
    if not gp or not Path(gp).is_file():
        parser.error("PARI/GP executable not found; install pari-gp or pass --gp PATH")
    gp_version = subprocess.run(
        [gp, "--version-short"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()

    started = time.time()
    primes = first_primes(args.screen_through)
    squarefree = squarefree_table(primes[-1], primes)
    admissible = [d for d in range(1, primes[-1]) if squarefree[d]]
    primorial = gmpy2.mpz(1)
    admissible_count = 0
    proved: list[dict] = []
    screened: list[dict] = []
    zero_candidates: list[dict] = []
    published_counts: list[int] = []
    pari = PariSession(gp, args.pari_stack)

    try:
        for n, p in enumerate(primes, start=1):
            primorial *= p
            while admissible_count < len(admissible) and admissible[admissible_count] < p:
                admissible_count += 1

            count = 0
            first_bpsw: tuple[int, gmpy2.mpz] | None = None
            # Counts are needed only to reproduce the published 84 terms.  In
            # the extension, stop after a genuine/probable prime witness.
            for d in admissible[:admissible_count]:
                value = primorial // d + d
                if not gmpy2.is_bpsw_prp(value):
                    continue
                count += 1
                if first_bpsw is None:
                    first_bpsw = (d, value)
                if n > 84:
                    if n <= args.prove_through:
                        if pari.isprime(value):
                            rec = candidate_record(n, p, d, value)
                            rec["pari_isprime"] = 1
                            proved.append(rec)
                            break
                        # In the fantastically unlikely event of a BPSW
                        # pseudoprime, continue to search for a true prime.
                        continue
                    rec = candidate_record(n, p, d, value)
                    rec["gmp_bpsw"] = 1
                    screened.append(rec)
                    break
            else:
                if n <= 84:
                    published_counts.append(count)
                elif n <= args.prove_through:
                    zero_candidates.append(
                        {"n": n, "p_n": p, "status": "all admissible d composite"}
                    )
                else:
                    zero_candidates.append(
                        {"n": n, "p_n": p, "status": "no BPSW probable prime"}
                    )
                continue

            if n <= 84:
                # The loop was not stopped early in this range.
                published_counts.append(count)

            if n % 25 == 0:
                print(f"finished n={n}, elapsed={time.time() - started:.1f}s", flush=True)
    finally:
        pari.close()

    result = {
        "problem": "OEIS A395412",
        "definition": "number of squarefree d < p_n such that P_n/d + d is prime",
        "software": {
            "python": shutil.which("python3"),
            "gmpy2": gmpy2.version(),
            "pari_gp": str(gp),
            "pari_gp_version": gp_version,
        },
        "parameters": {
            "prove_through": args.prove_through,
            "screen_through": args.screen_through,
        },
        "published_terms_reproduced": published_counts == OEIS_TERMS_1_TO_84,
        "published_counts_1_to_84": published_counts,
        "proved_nonzero_range": [85, args.prove_through],
        "proved_witnesses": proved,
        "bpsw_screened_nonzero_range": [args.prove_through + 1, args.screen_through],
        "bpsw_screened_witnesses": screened,
        "zero_candidates": zero_candidates,
        "elapsed_seconds": time.time() - started,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "published_terms_reproduced": result["published_terms_reproduced"],
        "proved_witnesses": len(proved),
        "screened_witnesses": len(screened),
        "zero_candidates": zero_candidates,
        "elapsed_seconds": result["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
