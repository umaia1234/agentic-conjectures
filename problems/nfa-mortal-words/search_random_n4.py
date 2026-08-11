#!/usr/bin/env python3
"""Deterministic random search for long binary k-image-bounded mortal NFAs.

This is not an exhaustive search and therefore never proves an upper bound.
With the defaults below, CPython's stable ``random.Random`` generator rediscovers
the length-10 four-state witness in witnesses.json after candidate 466,977.
"""

from __future__ import annotations

import argparse
import random
from collections import deque
from typing import Sequence


Rows = tuple[int, ...]


def image(subset: int, rows: Rows) -> int:
    output = 0
    while subset:
        bit = subset & -subset
        output |= rows[bit.bit_length() - 1]
        subset -= bit
    return output


def is_k_image_bounded(letters: Sequence[Rows], n: int, k: int) -> bool:
    seen = {1 << q for q in range(n)}
    stack = list(seen)
    while stack:
        subset = stack.pop()
        for rows in letters:
            target = image(subset, rows)
            if target.bit_count() > k:
                return False
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return True


def shortest_mortal_word(letters: Sequence[Rows], n: int) -> str | None:
    start = (1 << n) - 1
    queue = deque([start])
    parent: dict[int, tuple[int, int] | None] = {start: None}
    while queue:
        subset = queue.popleft()
        for index, rows in enumerate(letters):
            target = image(subset, rows)
            if target in parent:
                continue
            parent[target] = (subset, index)
            if target == 0:
                word: list[str] = []
                cursor = 0
                while parent[cursor] is not None:
                    previous, letter_index = parent[cursor]
                    word.append("ab"[letter_index])
                    cursor = previous
                return "".join(reversed(word))
            queue.append(target)
    return None


def rows_as_destinations(rows: Rows, n: int) -> list[list[int]]:
    return [
        [destination for destination in range(n) if row & (1 << destination)]
        for row in rows
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=4)
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument("--samples", type=int, default=1_000_000)
    parser.add_argument("--seed", type=int, default=718_281_828)
    args = parser.parse_args()
    if args.n < 1 or args.k < 1 or args.samples < 1:
        parser.error("n, k, and samples must be positive")

    rng = random.Random(args.seed)
    allowed_rows = [
        subset for subset in range(1 << args.n) if subset.bit_count() <= args.k
    ]
    best_length = -1
    bounded_seen = 0
    incomplete_seen = 0

    for candidate_index in range(args.samples):
        letters = tuple(
            tuple(rng.choice(allowed_rows) for _ in range(args.n))
            for _ in range(2)
        )
        if not is_k_image_bounded(letters, args.n, args.k):
            continue
        bounded_seen += 1
        word = shortest_mortal_word(letters, args.n)
        if word is None:
            continue
        incomplete_seen += 1
        if len(word) <= best_length:
            continue
        best_length = len(word)
        print(
            f"candidate={candidate_index} best_length={best_length} word={word} "
            f"a={rows_as_destinations(letters[0], args.n)} "
            f"b={rows_as_destinations(letters[1], args.n)}",
            flush=True,
        )

    print(
        f"done samples={args.samples} globally_k_image_bounded={bounded_seen} "
        f"incomplete={incomplete_seen} best_length={best_length}"
    )


if __name__ == "__main__":
    main()
