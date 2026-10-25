#!/usr/bin/env python3
"""Re-verify the Catch-Up({1..N}) values with three independent evaluators.

Usage: python3 verify_values.py [--nmax 22] [--py-nmax 12] [--positions 10]

1. Compiles catchup_turn.cpp (turn-level search with proved pruning rules) and catchup_pick.cpp
   (pick-level recursion of `valueAux`, no pruning) with g++ -O3 -std=c++17 in a temporary
   directory.
2. Runs both for N = 1..nmax and compares them with EXPECTED below, which contains the
   OEIS A278587 terms for N = 3..20.
3. Runs valueaux_transliteration.py (a literal Python copy of `valueAux`) for N = 1..py-nmax.
4. Compares all three on every position (R, D) with R a subset of {1..positions} and D <= positions.

Exit status 0 iff everything agrees. --nmax 28 reproduces the whole table (about 30 minutes and
15 GB of memory, dominated by catchup_pick at N = 27, 28).
"""
import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

# value of Catch-Up({1..N}) for the first player, N = 1..28
EXPECTED = ["win", "win", "draw", "draw", "win", "win", "draw", "draw", "loss", "loss",
            "draw", "draw", "win", "loss", "draw", "draw", "win", "loss", "draw", "draw",
            "win", "win", "draw", "draw", "win", "win", "draw", "draw"]
# OEIS A278587 (offset 3): 1 = first player wins, -1 = second player wins, 0 = draw
A278587 = [0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0]
WORD = {1: "win", 0: "draw", -1: "loss"}


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return r.stdout


def parse_values(out):
    vals = {}
    for line in out.splitlines():
        fields = dict(f.split("=", 1) for f in line.split() if "=" in f)
        vals[int(fields["N"])] = fields["value"]
    return vals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=22)
    ap.add_argument("--py-nmax", type=int, default=12)
    ap.add_argument("--positions", type=int, default=10)
    args = ap.parse_args()
    assert 1 <= args.nmax <= len(EXPECTED) and args.py_nmax <= args.nmax
    ok = True

    for i, a in enumerate(A278587):
        if WORD[a] != EXPECTED[i + 2]:
            print(f"EXPECTED disagrees with A278587 at N={i + 3}")
            ok = False

    with tempfile.TemporaryDirectory() as tmp:
        bins = {}
        for name in ("catchup_turn", "catchup_pick"):
            bins[name] = str(Path(tmp) / name)
            run(["g++", "-O3", "-std=c++17", str(HERE / f"{name}.cpp"), "-o", bins[name]])
        py = [sys.executable, str(HERE / "valueaux_transliteration.py")]

        results = {name: parse_values(run([b, "1", str(args.nmax)])) for name, b in bins.items()}
        results["valueaux_transliteration"] = parse_values(run(py + [str(args.py_nmax)]))
        for name, vals in results.items():
            top = args.py_nmax if name == "valueaux_transliteration" else args.nmax
            got = [vals.get(N) for N in range(1, top + 1)]
            if got != EXPECTED[:top]:
                print(f"FAIL {name}: {got}")
                ok = False
            else:
                print(f"ok   {name}: N = 1..{top} match")

        n = str(args.positions)
        dumps = {name: run([b, "--positions", n]) for name, b in bins.items()}
        dumps["valueaux_transliteration"] = run(py + ["--positions", n])
        ref = dumps["valueaux_transliteration"]
        count = len(ref.splitlines())
        for name, out in dumps.items():
            if out != ref:
                bad = [(a, b) for a, b in zip(out.splitlines(), ref.splitlines()) if a != b]
                print(f"FAIL {name} positions: {len(bad)} differences, first {bad[:3]}")
                ok = False
            else:
                print(f"ok   {name}: all {count} positions with R in [1..{n}], D <= {n} match")

    print("table:", " ".join(f"{N}:{EXPECTED[N - 1]}" for N in range(1, args.nmax + 1)))
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
