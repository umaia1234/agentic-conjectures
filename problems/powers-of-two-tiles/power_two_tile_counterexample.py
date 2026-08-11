#!/usr/bin/env python3
"""Exact checker for a counterexample to Question 9 of EJC 33(3), P3.28.

Question 9 in Benjamini--Kozma--Tzalik asks whether the only finite subsets of
{1, 2, 4, ..., 2^n} that tile Z by translations have size one or two.

In fact there is such a tile of every odd cardinality t.  If r is the
multiplicative order of 2 modulo t and q=2^r-1, then
    A_t = {2^(ri): 0 <= i < t}
is congruent to {1, 1+q, ..., 1+(t-1)q} modulo tq.  Consequently A_t tiles Z
with translation set {0, ..., q-1} + tq Z.  The t=3 case is {1,4,16}.
"""

from __future__ import annotations

import argparse
import math


def multiplicative_order_of_two(modulus: int) -> int:
    value = 1
    for exponent in range(1, modulus + 1):
        value = (2 * value) % modulus
        if value == 1:
            return exponent
    raise AssertionError("order not found")


def verify(odd_size: int, shift: int = 0) -> None:
    if odd_size < 3 or odd_size % 2 == 0:
        raise ValueError("odd_size must be an odd integer at least 3")
    if shift < 0:
        raise ValueError("shift must be nonnegative")
    assert math.gcd(2, odd_size) == 1
    order = multiplicative_order_of_two(odd_size)
    q = 2**order - 1
    assert q % odd_size == 0
    block = (2**shift) * q
    modulus = odd_size * block
    tile = tuple(2 ** (shift + order * i) for i in range(odd_size))
    complement_residues = tuple(range(block))

    expected_tile_residues = tuple(
        2**shift + i * block for i in range(odd_size)
    )
    tile_residues = tuple(value % modulus for value in tile)
    assert tile_residues == expected_tile_residues

    representations: list[list[tuple[int, int]]] = [
        [] for _ in range(modulus)
    ]
    for value in tile:
        for translation in complement_residues:
            residue = (value + translation) % modulus
            representations[residue].append((value, translation))

    assert all(len(reps) == 1 for reps in representations)
    print(
        f"odd_size={odd_size} order={order} q={q} shift={shift} "
        f"modulus={modulus}"
    )
    print(f"tile={tile}")
    print(f"tile residues={tile_residues}")
    print("every residue has exactly one representation: yes")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("odd_size", nargs="?", type=int, default=3)
    parser.add_argument("--shift", type=int, default=0)
    args = parser.parse_args()
    verify(args.odd_size, args.shift)


if __name__ == "__main__":
    main()
