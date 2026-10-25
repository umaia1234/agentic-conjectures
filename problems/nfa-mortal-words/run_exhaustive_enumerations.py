#!/usr/bin/env python3
"""Rebuild and rerun both exhaustive C++ enumerators and compare with the record.

For every requested n this script

* compiles enumerate_binary_canonical.cpp and enumerate_binary_crosscheck.cpp
  with -DNFA_STATES=n into a temporary directory;
* runs the canonical enumerator (S_n reduction on the first letter) and the
  cross-check enumerator in "orbit" mode (S_n reduction on the second letter)
  and, with --full, also in "full" mode (no symmetry reduction; n <= 5);
* checks that every run reports exactly the labelled ordered counts and
  shortest-mortal-length histogram recorded in exhaustive_maximizers.json; and
* checks that the maximizers printed by every run fall into exactly the
  relabelling classes listed there.  In full mode the printed pairs must be
  exactly the union of those classes, i.e. every labelled maximizer.

The default (n = 1..5, two threads, no --full) is the CI check.  The n = 6
check is local-only: ``--n 6 --threads 6`` takes a few minutes per enumerator
on an 18-core Apple M5 Max.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from check_exhaustive_maximizers import classes, pair_from_lists

HERE = Path(__file__).resolve().parent


def compile_program(source: str, n: int, out: Path, native: bool) -> None:
    compiler = shutil.which("g++") or shutil.which("c++") or shutil.which("clang++")
    if compiler is None:
        raise SystemExit("no C++ compiler found")
    flags = ["-O3", "-std=c++17", "-pthread", f"-DNFA_STATES={n}"]
    if native:
        flags.append("-march=native")
    subprocess.run([compiler, *flags, str(HERE / source), "-o", str(out)], check=True)


def run(cmd: list[str], log_dir: Path | None, log_name: str) -> str:
    start = time.time()
    result = subprocess.run(cmd, check=True, capture_output=True, text=True)
    elapsed = time.time() - start
    print(f"  {log_name}: {elapsed:.1f}s")
    if log_dir is not None:
        (log_dir / log_name).write_text(result.stdout, encoding="utf-8")
    return result.stdout


def parse(output: str) -> dict[str, object]:
    values: dict[str, object] = {}
    for key in (
        "ordered_2_image_bounded",
        "ordered_incomplete",
        "maximum_shortest_mortal_length",
        "labelled_maximizers",
    ):
        match = re.search(rf"\b{key}=(-?\d+)", output)
        if not match:
            raise AssertionError(f"missing {key} in output")
        values[key] = int(match[1])
    match = re.search(r"ordered_histogram=\{([^}]*)\}", output)
    if not match:
        raise AssertionError("missing histogram in output")
    values["ordered_histogram"] = {
        int(k): int(v)
        for k, v in (item.split(":") for item in match[1].split(",") if item.strip())
    }
    values["pairs"] = [
        pair_from_lists(json.loads(a), json.loads(b))
        for a, b in re.findall(r"^(?:maximizer \d+ |pair )a=(\S+) b=(\S+)$", output, re.M)
    ]
    return values


def compare(n: int, label: str, got: dict[str, object], summary: dict, reps: set) -> None:
    expected = {
        "ordered_2_image_bounded": int(summary["ordered_2_image_bounded"]),
        "ordered_incomplete": int(summary["ordered_incomplete"]),
        "maximum_shortest_mortal_length": int(summary["maximum_shortest_mortal_length"]),
        "labelled_maximizers": int(summary["labelled_maximizers"]),
        "ordered_histogram": {int(k): int(v) for k, v in summary["ordered_histogram"].items()},
    }
    for key, value in expected.items():
        if got[key] != value:
            raise AssertionError(f"n={n} {label}: {key}={got[key]}, recorded {value}")
    pairs = got["pairs"]
    got_classes = {min(members) for members in classes(pairs)}
    if got_classes != reps:
        raise AssertionError(f"n={n} {label}: maximizer classes differ from the record")
    print(
        f"PASS n={n} {label}: counts and histogram match; {len(pairs)} printed "
        f"maximizer pairs fall into exactly the {len(reps)} recorded classes"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, action="append", help="state counts (default 1..5)")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--full", action="store_true", help="also run the unreduced mode")
    parser.add_argument("--native", action="store_true", help="compile with -march=native")
    parser.add_argument("--log-dir", type=Path, help="write raw program outputs here")
    args = parser.parse_args()
    sizes = args.n or [1, 2, 3, 4, 5]
    if args.log_dir is not None:
        args.log_dir.mkdir(parents=True, exist_ok=True)

    record = json.loads((HERE / "exhaustive_maximizers.json").read_text(encoding="utf-8"))
    summaries = {int(s["n"]): s for s in record["summaries"]}
    with tempfile.TemporaryDirectory() as tmp:
        for n in sizes:
            if n not in summaries:
                raise SystemExit(f"no recorded summary for n={n}")
            if args.full and n > 5:
                raise SystemExit("full mode is limited to n <= 5")
            rep_pairs = [
                pair_from_lists(r["transitions"]["a"], r["transitions"]["b"])
                for r in record["automata"]
                if int(r["n"]) == n
            ]
            rep_classes = classes(rep_pairs)
            reps = {min(members) for members in rep_classes}
            union = set().union(*rep_classes)

            canonical = Path(tmp) / f"canonical{n}"
            crosscheck = Path(tmp) / f"crosscheck{n}"
            compile_program("enumerate_binary_canonical.cpp", n, canonical, args.native)
            compile_program("enumerate_binary_crosscheck.cpp", n, crosscheck, args.native)
            threads = str(args.threads)
            out = run([str(canonical), threads], args.log_dir, f"canonical_n{n}.txt")
            compare(n, "canonical", parse(out), summaries[n], reps)
            out = run([str(crosscheck), "orbit", threads], args.log_dir,
                      f"crosscheck_orbit_n{n}.txt")
            compare(n, "crosscheck-orbit", parse(out), summaries[n], reps)
            if args.full:
                out = run([str(crosscheck), "full", threads], args.log_dir,
                          f"crosscheck_full_n{n}.txt")
                got = parse(out)
                compare(n, "crosscheck-full", got, summaries[n], reps)
                if set(got["pairs"]) != union or len(got["pairs"]) != len(union):
                    raise AssertionError(f"n={n}: full-mode maximizers are not the union")
                print(f"PASS n={n} crosscheck-full: printed pairs are exactly all "
                      f"{len(union)} labelled maximizers")
    print("all requested exhaustive checks passed")


if __name__ == "__main__":
    sys.exit(main())
