#!/usr/bin/env python3
"""Cross-check the exact Erdős 424 computation against counts_result.json.

Part ``sieves`` compares two independent C++ computations of the generated set
S (the least set containing 2 and 3 with x*y - 1 in S for distinct members):

* ``erdos424_ascending.cpp`` (A): ascending push sieve over one bitset;
* ``erdos424_generations.cpp`` (B): the upstream recursion
  A_0 = {2, 3}, A_{k+1} = A_k ∪ {x*y - 1 : x != y in A_k}, evaluated
  semi-naively on two bit planes until it stabilises;

and checks both against ``reference_members``, a literal and unoptimised
Python transcription of the same recursion, at ``REFERENCE_LIMIT``.  The full
reports (count, 64-bit hash of the bitset, checkpoint and residue tallies,
first non-members, generation sizes) must agree with each other and with the
committed run for ``--limit``.  It also recomputes, for every modulus
2 <= m <= ``--closure-limit``, the least set of residues containing 2 and 3
and closed under (a, b) -> a*b - 1, and checks that it is exactly the set of
classes not congruent to 1 mod 3 (all classes when 3 does not divide m).

Part ``factorable`` checks ``erdos424_factorable.cpp`` (n is factorable if
n + 1 = x*y with 2 <= x < y and x, y not 1 mod 3) against a Python divisor
enumeration and against the prime-factor description of the non-factorable
admissible n given in DETAILS.md, then against the committed run; it also
checks that every member other than 2 and 3 is factorable, class by class.
Timings are diagnostic only.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_EXPECTED = HERE / "counts_result.json"
REFERENCE_LIMIT = 100_000
MASK64 = (1 << 64) - 1


def mix64(z: int) -> int:
    z = (z + 0x9E3779B97F4A7C15) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return z ^ (z >> 31)


def reference_members(limit: int) -> set[int]:
    """Literal fixed-point iteration of the upstream ``sequenceSet``, truncated to <= limit."""
    current = {2, 3}
    while True:
        members = sorted(current)
        new = set()
        for x in members:
            for y in members:
                if x * y - 1 > limit:
                    break
                if x != y:
                    new.add(x * y - 1)
        if new <= current:
            return current
        current |= new


def reference_hash(members: set[int], limit: int) -> str:
    words = [0] * (limit // 64 + 1)
    for n in members:
        words[n // 64] |= 1 << (n % 64)
    h = 0x424
    for word in words:
        h = mix64(h ^ word)
    return f"{h:016x}"


def residue_closure(m: int) -> list[bool]:
    """Least subset of Z/m containing 2, 3 and closed under (a, b) -> a*b - 1 (a = b allowed)."""
    seen = [False] * m
    order: list[int] = []
    for seed in (2 % m, 3 % m):
        if not seen[seed]:
            seen[seed] = True
            order.append(seed)
    i = 0
    while i < len(order):
        a = order[i]
        for b in order[: i + 1]:
            c = (a * b - 1) % m
            if not seen[c]:
                seen[c] = True
                order.append(c)
        i += 1
    return seen


def check_residue_closures(max_modulus: int) -> None:
    for m in range(2, max_modulus + 1):
        expected = [not (m % 3 == 0 and r % 3 == 1) for r in range(m)]
        if residue_closure(m) != expected:
            raise AssertionError(f"unexpected residue closure modulo {m}")


def smallest_prime_factors(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for p in range(2, int(limit**0.5) + 1):
        if spf[p] == p:
            for m in range(p * p, limit + 1, p):
                if spf[m] == m:
                    spf[m] = p
    return spf


def factorization(m: int, spf: list[int]) -> dict[int, int]:
    result: dict[int, int] = {}
    while m > 1:
        p = spf[m]
        result[p] = result.get(p, 0) + 1
        m //= p
    return result


def reference_factorable(limit: int) -> list[bool]:
    """Divisor enumeration: does n + 1 = d * e with 2 <= d < e and d, e not 1 mod 3?"""
    spf = smallest_prime_factors(limit + 1)
    flags = [False] * (limit + 1)
    for n in range(limit + 1):
        m = n + 1
        divisors = [1]
        for p, e in factorization(m, spf).items():
            divisors = [d * p**k for d in divisors for k in range(e + 1)]
        flags[n] = any(
            2 <= d and d * d < m and d % 3 != 1 and (m // d) % 3 != 1 for d in divisors
        )
    return flags


def predicted_unfactorable(n: int, spf: list[int]) -> bool:
    """Prime-factor description (DETAILS.md) for admissible n >= 4."""
    if n % 2 == 1:
        return False
    primes = factorization(n + 1, spf)
    if n % 6 == 0:
        two_mod_three = [p for p in primes if p % 3 == 2]
        return not two_mod_three or (len(primes) == 1 and primes.get(two_mod_three[0]) == 2)
    # n % 6 == 2: n + 1 = 3m
    if n + 1 == 9:
        return True
    m = (n + 1) // 3
    return m % 3 != 0 and all(p % 3 == 1 for p in factorization(m, spf))


def compile_program(source: Path, output: Path) -> None:
    subprocess.run(
        ["g++", "-O3", "-std=c++17", str(source), "-o", str(output)],
        check=True,
        capture_output=True,
        text=True,
        timeout=120,
    )


def run_program(executable: Path, limit: int) -> tuple[dict, float]:
    started = time.perf_counter()
    completed = subprocess.run(
        [str(executable), str(limit)], check=True, capture_output=True, text=True
    )
    return parse_report(completed.stdout), time.perf_counter() - started


def parse_report(text: str) -> dict:
    report: dict = {}
    for line in text.splitlines():
        key, *rest = line.split()
        if key == "impl":
            report["impl"] = rest[0]
        elif key in ("limit", "count"):
            report[key] = int(rest[0])
        elif key == "hash":
            report["hash"] = rest[0]
        elif key == "checkpoint":
            report.setdefault("checkpoints", {})[rest[0]] = int(rest[1])
        elif key in ("checkpoint_mod6", "factorable_mod6", "residues"):
            report.setdefault(key, {})[rest[0]] = [int(v) for v in rest[1:]]
        elif key == "first_nonmembers_not_1_mod_3":
            report[key] = [int(v) for v in rest]
        elif key == "generation":
            report.setdefault("generations", [])
            if int(rest[0]) != len(report["generations"]):
                raise AssertionError("generation records out of order")
            report["generations"].append(int(rest[1]))
        else:
            raise AssertionError(f"unknown record {key!r}")
    return report


SIEVE_KEYS = (
    "limit",
    "count",
    "hash",
    "checkpoints",
    "checkpoint_mod6",
    "residues",
    "first_nonmembers_not_1_mod_3",
)


def sieve_part(report: dict) -> dict:
    return {key: report[key] for key in SIEVE_KEYS}


def class_size(limit: int, modulus: int, residue: int) -> int:
    return (limit - residue) // modulus + 1 if limit >= residue else 0


def check_sieve_consistency(report: dict) -> None:
    limit, count = report["limit"], report["count"]
    if report["checkpoints"][str(limit)] != count:
        raise AssertionError("final checkpoint differs from total count")
    for m, counts in report["residues"].items():
        m = int(m)
        if len(counts) != m or sum(counts) != count:
            raise AssertionError(f"residue tallies mod {m} do not sum to the count")
        if m % 3 == 0 and any(counts[r] for r in range(1, m, 3)):
            raise AssertionError(f"a class 1 mod 3 is populated modulo {m}")
    for mark, counts in report["checkpoint_mod6"].items():
        if sum(counts) != report["checkpoints"][mark] or counts[1] or counts[4]:
            raise AssertionError(f"inconsistent mod-6 tallies at checkpoint {mark}")
    previous = 0
    for mark in sorted(report["checkpoints"], key=int):
        if report["checkpoints"][mark] < previous:
            raise AssertionError("checkpoint counts are not monotone")
        previous = report["checkpoints"][mark]
    if "generations" in report and sum(report["generations"]) != count:
        raise AssertionError("generation sizes do not sum to the count")


def verify_sieves(tmpdir: Path, limit: int, committed: dict, closure_limit: int) -> dict:
    started = time.perf_counter()
    check_residue_closures(closure_limit)
    reference = reference_members(REFERENCE_LIMIT)
    reference_seconds = time.perf_counter() - started
    asc, gen = tmpdir / "ascending", tmpdir / "generations"
    compile_program(HERE / "erdos424_ascending.cpp", asc)
    compile_program(HERE / "erdos424_generations.cpp", gen)
    small_a, _ = run_program(asc, REFERENCE_LIMIT)
    small_b, _ = run_program(gen, REFERENCE_LIMIT)
    report_a, seconds_a = run_program(asc, limit)
    report_b, seconds_b = run_program(gen, limit)

    ref_hash = reference_hash(reference, REFERENCE_LIMIT)
    for small in (small_a, small_b):
        if small["count"] != len(reference) or small["hash"] != ref_hash:
            raise AssertionError(f"{small['impl']} disagrees with the Python reference")
        for mark, value in small["checkpoints"].items():
            if value != sum(1 for n in reference if n <= int(mark)):
                raise AssertionError("checkpoint disagrees with the Python reference")
    if sieve_part(small_a) != sieve_part(small_b):
        raise AssertionError("A and B disagree at the reference limit")

    for report in (report_a, report_b):
        if report["limit"] != limit:
            raise AssertionError("an implementation reported the wrong limit")
        check_sieve_consistency(report)
    if sieve_part(report_a) != sieve_part(report_b):
        raise AssertionError("independent implementations disagree")
    if sieve_part(report_a) != {key: committed[key] for key in SIEVE_KEYS}:
        raise AssertionError("computed report disagrees with counts_result.json")
    if report_b["generations"] != committed["generations"]:
        raise AssertionError("generation profile disagrees with counts_result.json")
    return {
        "count": report_a["count"],
        "hash": report_a["hash"],
        "reference_count": len(reference),
        "residue_closures_checked_up_to": closure_limit,
        "ascending_seconds": round(seconds_a, 2),
        "generations_seconds": round(seconds_b, 2),
        "reference_seconds": round(reference_seconds, 2),
    }


def verify_factorable(tmpdir: Path, limit: int, committed: dict) -> dict:
    started = time.perf_counter()
    flags = reference_factorable(REFERENCE_LIMIT)
    spf = smallest_prime_factors(REFERENCE_LIMIT + 1)
    for n in range(4, REFERENCE_LIMIT + 1):
        if n % 3 != 1 and predicted_unfactorable(n, spf) != (not flags[n]):
            raise AssertionError(f"prime-factor description fails at n={n}")
    if any(flags[n] for n in range(REFERENCE_LIMIT + 1) if n % 3 == 1):
        raise AssertionError("a factorable n is 1 mod 3")
    reference_seconds = time.perf_counter() - started
    fac = tmpdir / "factorable"
    compile_program(HERE / "erdos424_factorable.cpp", fac)
    small, _ = run_program(fac, REFERENCE_LIMIT)
    for mark, counts in small["factorable_mod6"].items():
        expected = [0] * 6
        for n in range(int(mark) + 1):
            if flags[n]:
                expected[n % 6] += 1
        if counts != expected:
            raise AssertionError(f"factorable counts disagree with Python at {mark}")
    report, seconds = run_program(fac, limit)
    if report["limit"] != limit:
        raise AssertionError("factorable program reported the wrong limit")
    if report["factorable_mod6"] != committed["factorable_mod6"]:
        raise AssertionError("factorable counts disagree with counts_result.json")
    for mark, counts in report["factorable_mod6"].items():
        members = committed["checkpoint_mod6"][mark]
        if counts[1] or counts[4]:
            raise AssertionError("a factorable n is 1 mod 3")
        # odd admissible n >= 5 are factorable (2 * ((n + 1) / 2)); only 3 is not
        if counts[3] != class_size(int(mark), 6, 3) - 1 or counts[5] != class_size(
            int(mark), 6, 5
        ):
            raise AssertionError("an odd admissible n >= 5 is not factorable")
        # members other than 2 (class 2) and 3 (class 3) are factorable
        if members[0] > counts[0] or members[2] - 1 > counts[2] or members[5] > counts[5]:
            raise AssertionError("a member is not factorable")
    return {
        "factorable_seconds": round(seconds, 2),
        "reference_seconds": round(reference_seconds, 2),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_000_000_000)
    parser.add_argument("--part", choices=("sieves", "factorable", "all"), default="all")
    parser.add_argument("--closure-limit", type=int, default=300)
    parser.add_argument("--expected", type=Path, default=DEFAULT_EXPECTED)
    args = parser.parse_args()

    runs = json.loads(args.expected.read_text(encoding="utf-8"))["runs"]
    if str(args.limit) not in runs:
        parser.error(f"counts_result.json has runs only for limits {sorted(runs, key=int)}")
    committed = runs[str(args.limit)]

    summary: dict = {"limit": args.limit, "part": args.part}
    with tempfile.TemporaryDirectory(prefix="erdos424-") as tmp:
        tmpdir = Path(tmp)
        if args.part in ("sieves", "all"):
            summary["sieves"] = verify_sieves(tmpdir, args.limit, committed, args.closure_limit)
        if args.part in ("factorable", "all"):
            summary["factorable"] = verify_factorable(tmpdir, args.limit, committed)
    summary["result"] = "all requested checks passed"
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
