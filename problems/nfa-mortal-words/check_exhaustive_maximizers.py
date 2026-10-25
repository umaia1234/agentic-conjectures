#!/usr/bin/env python3
"""Check the recorded maximizer classes of the exhaustive enumerations (n <= 6).

For every summary in exhaustive_maximizers.json this script

1. verifies every listed representative with the independent
   transformation-monoid verifier of verify_witnesses.py (relational
   composition closure for 2-image-boundedness, full powerset BFS for the
   shortest mortal length, replay of the claimed word);
2. checks that every representative attains the recorded maximum, that the
   representatives are pairwise non-isomorphic under state relabelling, that
   their S_n-orbit sizes add up to the recorded number of labelled ordered
   maximizers, and that the number of classes under relabelling plus letter
   swap is as recorded;
3. checks that every earlier witness in witnesses.json is consistent with the
   recorded maximum and, when it attains it, lies in a listed class.

The orbit computations here are plain Python and share no code with the C++
enumerators.  run_exhaustive_enumerations.py reuses them to compare the
maximizers printed by both enumerators with the classes listed here.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence

from verify_witnesses import destinations_to_mask, shortest_mortal_path, verify_record

HERE = Path(__file__).resolve().parent
Rows = tuple[int, ...]
Pair = tuple[Rows, Rows]


def relabel(rows: Rows, sigma: Sequence[int]) -> Rows:
    """Rows of the letter after renaming every state q to sigma[q]."""

    out = [0] * len(rows)
    for q, row in enumerate(rows):
        image = 0
        for t in range(len(rows)):
            if row >> t & 1:
                image |= 1 << sigma[t]
        out[sigma[q]] = image
    return tuple(out)


def orbit(pair: Pair) -> set[Pair]:
    n = len(pair[0])
    return {
        (relabel(pair[0], sigma), relabel(pair[1], sigma))
        for sigma in itertools.permutations(range(n))
    }


def pair_from_lists(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> Pair:
    n = len(a)
    return (
        tuple(destinations_to_mask(row, n) for row in a),
        tuple(destinations_to_mask(row, n) for row in b),
    )


def classes(pairs: Iterable[Pair]) -> list[frozenset[Pair]]:
    found: list[frozenset[Pair]] = []
    seen: set[Pair] = set()
    for pair in pairs:
        if pair in seen:
            continue
        members = frozenset(orbit(pair))
        seen |= members
        found.append(members)
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "data", nargs="?", type=Path, default=HERE / "exhaustive_maximizers.json"
    )
    args = parser.parse_args()

    payload = json.loads(args.data.read_text(encoding="utf-8"))
    if payload.get("format_version") != 1:
        raise ValueError("unsupported format")
    old = json.loads((HERE / "witnesses.json").read_text(encoding="utf-8"))

    for summary in payload["summaries"]:
        n = int(summary["n"])
        maximum = int(summary["maximum_shortest_mortal_length"])
        records = [r for r in payload["automata"] if int(r["n"]) == n]
        reps: list[Pair] = []
        for record in records:
            verify_record(record)
            if int(record["claimed_shortest_mortal_length"]) != maximum:
                raise AssertionError(f"{record['id']}: not a maximizer")
            reps.append(
                pair_from_lists(record["transitions"]["a"], record["transitions"]["b"])
            )

        rep_classes = classes(reps)
        if len(rep_classes) != len(reps):
            raise AssertionError(f"n={n}: two representatives are isomorphic")
        if len(reps) != int(summary["orbits_relabelling"]):
            raise AssertionError(f"n={n}: wrong number of relabelling classes")
        labelled = sum(len(members) for members in rep_classes)
        if labelled != int(summary["labelled_maximizers"]):
            raise AssertionError(
                f"n={n}: orbit sizes sum to {labelled}, "
                f"recorded {summary['labelled_maximizers']}"
            )
        swapped = {min(min(orbit(pair)), min(orbit((pair[1], pair[0])))) for pair in reps}
        if len(swapped) != int(summary["orbits_relabelling_swap"]):
            raise AssertionError(f"n={n}: wrong number of relabelling+swap classes")
        if sum(int(v) for v in summary["ordered_histogram"].values()) != int(
            summary["ordered_incomplete"]
        ):
            raise AssertionError(f"n={n}: histogram does not sum to incomplete count")
        if int(max(summary["ordered_histogram"], key=int)) != maximum:
            raise AssertionError(f"n={n}: histogram maximum mismatch")
        if int(summary["ordered_histogram"][str(maximum)]) != labelled:
            raise AssertionError(f"n={n}: histogram top bin mismatch")

        members_all = set().union(*rep_classes)
        for record in old["automata"]:
            if int(record["n"]) != n:
                continue
            pair = pair_from_lists(record["transitions"]["a"], record["transitions"]["b"])
            if int(record["claimed_shortest_mortal_length"]) == maximum:
                if pair not in members_all:
                    raise AssertionError(f"{record['id']} is not in a listed class")
                print(f"  earlier witness {record['id']} lies in a listed class")
            else:
                letters = list(pair)
                _, _, distances = shortest_mortal_path(letters, "ab", n)
                if distances.get(0, -1) > maximum:
                    raise AssertionError(f"{record['id']} exceeds the recorded maximum")

        print(
            f"PASS n={n}: maximum {maximum}, {len(reps)} relabelling classes, "
            f"{len(swapped)} relabelling+swap classes, {labelled} labelled ordered maximizers"
        )


if __name__ == "__main__":
    main()
