#!/usr/bin/env python3
"""Exhaustively enumerate small binary k-image-bounded NFAs.

An NFA letter is represented by an n-tuple of bit masks.  Row q is the
set of destinations of state q.  For n states there are 2^(n^2) possible
relations for one letter and 2^(2 n^2) ordered binary NFAs.

The implementation deliberately uses only the Python standard library.
The default n <= 3 run examines 262,404 candidates in total and normally
finishes in well under a second on a current desktop.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence


Rows = tuple[int, ...]
Automaton = tuple[Rows, Rows]


def relation_rows(relation: int, n: int) -> Rows:
    """Decode an n-by-n Boolean relation stored row-major in an integer."""

    row_mask = (1 << n) - 1
    return tuple((relation >> (q * n)) & row_mask for q in range(n))


def image(subset: int, rows: Rows) -> int:
    """Return the relational image of a state subset under one letter."""

    result = 0
    remaining = subset
    while remaining:
        low_bit = remaining & -remaining
        state = low_bit.bit_length() - 1
        result |= rows[state]
        remaining -= low_bit
    return result


def is_k_image_bounded(automaton: Sequence[Rows], n: int, k: int) -> bool:
    """Decide k-image-boundedness by singleton subset reachability.

    For a state q and word w, q.w is exactly a subset reachable from {q}
    in the powerset automaton.  Hence it suffices to explore all subsets
    reachable from all n singleton subsets.
    """

    seen = {1 << q for q in range(n)}
    stack = list(seen)
    while stack:
        subset = stack.pop()
        if subset.bit_count() > k:
            return False
        for rows in automaton:
            target = image(subset, rows)
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return True


def shortest_mortal_word(
    automaton: Sequence[Rows], n: int, alphabet: str = "ab"
) -> str | None:
    """Find a shortest word mapping the full state set to the empty set."""

    start = (1 << n) - 1
    queue = deque([start])
    parent: dict[int, tuple[int, int] | None] = {start: None}

    while queue:
        subset = queue.popleft()
        for letter_index, rows in enumerate(automaton):
            target = image(subset, rows)
            if target in parent:
                continue
            parent[target] = (subset, letter_index)
            if target == 0:
                letters: list[str] = []
                cursor = target
                while parent[cursor] is not None:
                    previous, index = parent[cursor]
                    letters.append(alphabet[index])
                    cursor = previous
                return "".join(reversed(letters))
            queue.append(target)
    return None


@dataclass(frozen=True)
class EnumerationSummary:
    n: int
    k: int
    raw_candidates: int
    k_image_bounded_candidates: int
    incomplete_candidates: int
    shortest_length_histogram: dict[int, int]
    maximum_shortest_mortal_length: int | None
    maximizer_count: int
    first_maximizer_relation_codes: tuple[int, int] | None
    first_maximizer_word: str | None


def enumerate_size(n: int, k: int = 2) -> EnumerationSummary:
    """Enumerate every ordered binary NFA on n labelled states."""

    relations_count = 1 << (n * n)
    rows_cache = [relation_rows(code, n) for code in range(relations_count)]

    bounded_count = 0
    incomplete_count = 0
    histogram: Counter[int] = Counter()
    maximum: int | None = None
    maximizer_count = 0
    first_codes: tuple[int, int] | None = None
    first_word: str | None = None

    for first_code, first_rows in enumerate(rows_cache):
        for second_code, second_rows in enumerate(rows_cache):
            automaton = (first_rows, second_rows)
            if not is_k_image_bounded(automaton, n, k):
                continue
            bounded_count += 1

            word = shortest_mortal_word(automaton, n)
            if word is None:
                continue
            incomplete_count += 1
            length = len(word)
            histogram[length] += 1

            if maximum is None or length > maximum:
                maximum = length
                maximizer_count = 1
                first_codes = (first_code, second_code)
                first_word = word
            elif length == maximum:
                maximizer_count += 1

    return EnumerationSummary(
        n=n,
        k=k,
        raw_candidates=relations_count * relations_count,
        k_image_bounded_candidates=bounded_count,
        incomplete_candidates=incomplete_count,
        shortest_length_histogram=dict(sorted(histogram.items())),
        maximum_shortest_mortal_length=maximum,
        maximizer_count=maximizer_count,
        first_maximizer_relation_codes=first_codes,
        first_maximizer_word=first_word,
    )


def summaries(max_n: int, k: int) -> Iterable[EnumerationSummary]:
    for n in range(1, max_n + 1):
        yield enumerate_size(n, k)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=3)
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--json", action="store_true", help="emit machine-readable JSON"
    )
    args = parser.parse_args()
    if args.max_n < 1:
        parser.error("--max-n must be positive")
    if args.k < 1:
        parser.error("--k must be positive")

    results = [asdict(item) for item in summaries(args.max_n, args.k)]
    if args.json:
        print(json.dumps(results, indent=2, sort_keys=True))
        return

    for result in results:
        print(
            "n={n} k={k} raw={raw_candidates} "
            "k_image_bounded={k_image_bounded_candidates} "
            "incomplete={incomplete_candidates} "
            "max_shortest={maximum_shortest_mortal_length} "
            "maximizers={maximizer_count}".format(**result)
        )
        print(f"  histogram={result['shortest_length_histogram']}")
        print(
            "  first_maximizer_codes="
            f"{result['first_maximizer_relation_codes']} "
            f"word={result['first_maximizer_word']}"
        )


if __name__ == "__main__":
    main()
