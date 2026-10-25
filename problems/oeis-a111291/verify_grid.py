#!/usr/bin/env python3
"""Check the grid certificate grid.txt: pi(x_{i+1}) <= 2 T(x_i) for consecutive grid points.

For x_i <= n <= x_{i+1}, monotonicity gives pi(n) <= pi(x_{i+1}) <= 2 T(x_i) <= 2 T(n), so the
grid proves pi(n) <= 2 T(n) on [x_0, x_last] = [10^6, 10^15]. T(x) and pi(x) are recomputed with
the structured counter tau_count (pi from its Lucy_Hedgehog table) and compared with the file.

Usage: python3 verify_grid.py PATH_TO_tau_count_BINARY [UPTO]
  With UPTO, only the grid points up to the first one >= UPTO are recomputed (faster check of
  [10^6, UPTO]).
"""
import subprocess
import sys


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(__doc__)
        return 2
    upto = int(sys.argv[2]) if len(sys.argv) == 3 else None
    rows = []
    for line in open("grid.txt"):
        if line.strip() and not line.startswith("#"):
            rows.append(tuple(map(int, line.split())))
    if upto is not None:
        k = next(i for i, r in enumerate(rows) if r[0] >= upto)
        rows = rows[: k + 1]
    xs = [r[0] for r in rows]
    out = subprocess.run([sys.argv[1]] + [str(x) for x in xs], capture_output=True, text=True,
                         check=True).stdout
    got = {}
    for line in out.splitlines():
        f = dict(kv.split("=") for kv in line.split())
        got[int(f["x"])] = (int(f["T"]), int(f["pi"]))
    ok = xs[0] == 10**6 and all(a < b for a, b in zip(xs, xs[1:]))
    for x, T, P in rows:
        if got.get(x) != (T, P):
            print(f"MISMATCH at x={x}: file T={T} pi={P}, recomputed {got.get(x)}")
            ok = False
    worst = None
    for (x0, T0, _), (x1, _, P1) in zip(rows, rows[1:]):
        if P1 > 2 * T0:
            print(f"STEP FAILS: pi({x1}) = {P1} > 2 T({x0}) = {2 * T0}")
            ok = False
        r = P1 / (2 * T0)
        if worst is None or r > worst[0]:
            worst = (r, x0, x1)
    print(f"{len(rows)} grid points from {xs[0]} to {xs[-1]}; largest pi(x_(i+1)) / 2T(x_i) = "
          f"{worst[0]:.6f} on [{worst[1]}, {worst[2]}]")
    print(("VERIFIED" if ok else "FAILED") + f": pi(n) <= 2T(n) for all {xs[0]} <= n <= {xs[-1]}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
