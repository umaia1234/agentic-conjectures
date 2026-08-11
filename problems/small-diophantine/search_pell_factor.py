#!/usr/bin/env python3
"""Spot-check a Pell-factor ansatz by exact Groebner elimination.

We seek

  y(t)^4 - 4*(x(t)^3+a*x(t)+b) = G(t)^2 R(t)

with

  x=-D*t^2+C, y=t+Q,
  G=2*D*t^2-L*t+J, R=D*t^2+L*t+M.

If R(t)=v^2 has an infinite Pell orbit and the parity/congruence conditions
hold, this would give infinitely many solutions.  The cases below are only a
small exact spot-check, not an exhaustive search over Q in QQ.
"""

from __future__ import annotations

import argparse
import gc
import subprocess
import sys

import sympy as sp


C, J, M, L, D = sp.symbols("C J M L D")

# Cases actually checked during the attempt.  Q=0 belongs to a separate
# symmetric branch and is covered by analyze_ansatze.py.
CASES = (
    (0, -2, -5),
    (0, -2, -4),
    (0, -2, -3),
    (0, -2, -2),
    (0, -2, -1),
    (0, -2, 1),
    (0, -2, 2),
    (0, -3, 1),
    (0, 3, 1),
    (0, 3, 2),
    (-1, -2, 2),
)


def equations(a: int, b: int, q: int) -> list[sp.Expr]:
    return [
        -12 * C * D**2 - 4 * D**2 * J - 4 * D**2 * M + 3 * D * L**2 + 1,
        -2 * D * L * J + 4 * D * L * M - L**3 + 4 * q,
        12 * C**2 * D
        - D * J**2
        - 4 * D * J * M
        + 4 * D * a
        - L**2 * M
        + 2 * L**2 * J
        + 6 * q**2,
        L * J * (2 * M - J) + 4 * q**3,
        -4 * C**3 - 4 * C * a - J**2 * M + q**4 - 4 * b,
    ]


def run_one(a: int, b: int, q: int) -> None:
    grevlex = sp.groebner(equations(a, b, q), C, J, M, L, D, order="grevlex")
    lex = grevlex.fglm("lex")
    univariate = next(
        p.as_expr()
        for p in reversed(lex.polys)
        if p.as_expr().free_symbols <= {D}
    )
    roots = sp.polys.polytools.ground_roots(sp.Poly(univariate, D, domain=sp.QQ))
    print(
        f"(a,b,Q)=({a},{b},{q}): degree={sp.degree(univariate, D)}, "
        f"rational D roots={roots}",
        flush=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--one", nargs=3, type=int, metavar=("A", "B", "Q"))
    args = parser.parse_args()
    if args.one:
        run_one(*args.one)
        return

    # Isolate cases in child processes: SymPy's Groebner bases can retain a
    # large amount of memory between cases.
    for case in CASES:
        subprocess.run(
            [sys.executable, __file__, "--one", *(str(value) for value in case)],
            check=True,
        )
        gc.collect()


if __name__ == "__main__":
    main()
