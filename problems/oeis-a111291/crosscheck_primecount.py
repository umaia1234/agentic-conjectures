#!/usr/bin/env python3
"""Cross-check the pi(x) column of grid.txt with primecount (Kim Walisch,
https://github.com/kimwalisch/primecount), independently of the Lucy_Hedgehog table in tau_count.

Usage: python3 crosscheck_primecount.py [PATH_TO_primecount]
"""
import subprocess
import sys


def main() -> int:
    pc = sys.argv[1] if len(sys.argv) > 1 else "primecount"
    print(subprocess.run([pc, "--version"], capture_output=True, text=True).stdout.strip())
    rows = [tuple(map(int, line.split())) for line in open("grid.txt")
            if line.strip() and not line.startswith("#")]
    bad = 0
    for x, _, p in rows:
        got = int(subprocess.run([pc, str(x)], capture_output=True, text=True,
                                 check=True).stdout)
        print(x, got)
        if got != p:
            bad += 1
            print(f"MISMATCH at x={x}: grid.txt pi={p}, primecount {got}")
    print(f"{len(rows)} grid points: {bad} mismatches")
    print("PRIMECOUNT CROSSCHECK OK" if bad == 0 else "PRIMECOUNT CROSSCHECK FAILED")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
