#!/usr/bin/env python3
"""Independently verify the finite Erdős 385 classification through 10^9.

Two existing C++ implementations are deliberately cross-checked:

* ``ep430_experiment.cpp`` uses a dense Euler/linear least-prime-factor sieve.
* ``ep430_segmented.cpp`` uses an odd-only segmented Eratosthenes sieve and a
  separate coverage recurrence.

The first implementation stores the full least-prime-factor table; the second
never does.  This wrapper compiles both from source, compares their complete
equality-case lists and slack-threshold records, then checks the committed
mathematical certificate.  Timing fields are diagnostic and are not certified.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFAULT_EXPECTED = HERE / "billion_result.json"


def compile_program(source: Path, output: Path) -> None:
    subprocess.run(
        ["g++", "-O3", "-std=c++17", str(source), "-o", str(output)],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )


def run_program(executable: Path, limit: int) -> tuple[str, float]:
    started = time.perf_counter()
    completed = subprocess.run(
        [str(executable), str(limit)],
        check=True,
        capture_output=True,
        text=True,
        timeout=170,
    )
    return completed.stdout, time.perf_counter() - started


def value_after_prefix(output: str, prefix: str) -> str:
    matches = [line[len(prefix) :] for line in output.splitlines() if line.startswith(prefix)]
    if len(matches) != 1:
        raise AssertionError(f"expected one {prefix!r} line, found {len(matches)}")
    return matches[0].strip()


def parse_limit(output: str) -> int:
    first = output.splitlines()[0].split()
    if len(first) not in (2, 4) or first[0] != "limit":
        raise AssertionError("malformed limit line")
    if len(first) == 4 and first[2] != "processed_odd":
        raise AssertionError("malformed segmented limit line")
    return int(first[1])


def parse_exceptions(output: str) -> list[int]:
    payload = value_after_prefix(output, "exceptional:")
    values = [] if not payload else [int(value) for value in payload.split()]
    if values != sorted(set(values)):
        raise AssertionError("exception list is not strictly increasing")
    return values


def parse_thresholds(output: str) -> dict[str, int]:
    payload = value_after_prefix(output, "last_n_with_slack_at_most:")
    result: dict[str, int] = {}
    for item in payload.split():
        threshold, last_n = item.split(":", 1)
        if threshold in result:
            raise AssertionError(f"duplicate threshold {threshold}")
        result[threshold] = int(last_n)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_000_000_000)
    parser.add_argument("--expected", type=Path, default=DEFAULT_EXPECTED)
    args = parser.parse_args()
    if args.limit < 6 or args.limit > 1_000_000_000:
        parser.error("require 6 <= limit <= 1000000000")

    expected = json.loads(args.expected.read_text(encoding="utf-8"))
    if expected.get("result") != "F(n) > n for every integer n in the strict interval":
        raise AssertionError("unexpected certificate result description")
    if args.limit != expected["limit"]:
        parser.error(
            f"the committed certificate has limit {expected['limit']}; "
            f"received {args.limit}"
        )

    with tempfile.TemporaryDirectory(prefix="erdos385-", dir="/tmp") as tmp:
        tmpdir = Path(tmp)
        dense = tmpdir / "dense"
        segmented = tmpdir / "segmented"
        compile_program(HERE / "ep430_experiment.cpp", dense)
        compile_program(HERE / "ep430_segmented.cpp", segmented)
        dense_output, dense_seconds = run_program(dense, args.limit)
        segmented_output, segmented_seconds = run_program(segmented, args.limit)

    if parse_limit(dense_output) != args.limit:
        raise AssertionError("dense implementation reported the wrong limit")
    if parse_limit(segmented_output) != args.limit:
        raise AssertionError("segmented implementation reported the wrong limit")

    # The dense experiment also prints 3 and 4, where the maximization set is
    # empty.  The mathematical certificate starts at n=6; normalize only this
    # explicitly documented boundary difference.
    dense_all = parse_exceptions(dense_output)
    if [n for n in dense_all if n < 6] != [3, 4]:
        raise AssertionError("unexpected dense boundary cases below 6")
    dense_equalities = [n for n in dense_all if n >= 6]
    segmented_equalities = parse_exceptions(segmented_output)
    if dense_equalities != segmented_equalities:
        raise AssertionError("independent implementations disagree on equality cases")

    dense_thresholds = parse_thresholds(dense_output)
    segmented_thresholds = parse_thresholds(segmented_output)
    if dense_thresholds != segmented_thresholds:
        raise AssertionError("independent implementations disagree on slack thresholds")

    if dense_equalities != expected["equality_cases"]:
        raise AssertionError("computed equality cases disagree with billion_result.json")
    if dense_thresholds != expected["last_n_with_slack_at_most"]:
        raise AssertionError("computed threshold records disagree with billion_result.json")
    if len(dense_equalities) != expected["equality_case_count"]:
        raise AssertionError("equality-case count mismatch")
    if dense_equalities[-1] != expected["last_equality"]:
        raise AssertionError("last equality mismatch")
    if expected["strict_interval"]["lower"] != dense_equalities[-1] + 1:
        raise AssertionError("strict interval does not begin after the last equality")
    if expected["strict_interval"]["upper"] != args.limit:
        raise AssertionError("strict interval has the wrong upper endpoint")

    print(
        json.dumps(
            {
                "result": "certificate verified by two independent implementations",
                "limit": args.limit,
                "equality_case_count": len(dense_equalities),
                "last_equality": dense_equalities[-1],
                "strict_interval": expected["strict_interval"],
                "dense_seconds": dense_seconds,
                "segmented_seconds": segmented_seconds,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
