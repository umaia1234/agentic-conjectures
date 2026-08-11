#!/usr/bin/env python3
"""Independent exact Littlewood--Richardson tableau counter.

This implementation is intentionally separate from lrcalc.  It processes a
skew tableau one row at a time.  A weakly increasing row is determined by the
number of occurrences of each label, so the dynamic-programming state only
keeps the preceding row and the cumulative content.  Python integers make the
count arbitrary precision.

It is designed as a verification oracle for small and moderate examples, not
as the primary large-scale search engine.
"""

from __future__ import annotations

import argparse
import functools
import json
from collections import defaultdict
from collections.abc import Iterable, Iterator, Sequence


Partition = tuple[int, ...]


def normalize(partition: Sequence[int]) -> Partition:
    """Validate and remove trailing zeroes from a partition."""
    result = tuple(int(part) for part in partition)
    if any(part < 0 for part in result):
        raise ValueError("partition parts must be nonnegative")
    if any(left < right for left, right in zip(result, result[1:])):
        raise ValueError("partition parts must be weakly decreasing")
    end = len(result)
    while end and result[end - 1] == 0:
        end -= 1
    return result[:end]


def _bounded_compositions(total: int, bounds: Partition) -> Iterator[Partition]:
    """Yield vectors of prescribed sum within componentwise upper bounds."""
    suffix_capacity = [0] * (len(bounds) + 1)
    for index in range(len(bounds) - 1, -1, -1):
        suffix_capacity[index] = suffix_capacity[index + 1] + bounds[index]

    values = [0] * len(bounds)

    def visit(index: int, remaining: int) -> Iterator[Partition]:
        if index == len(bounds):
            if remaining == 0:
                yield tuple(values)
            return
        lower = max(0, remaining - suffix_capacity[index + 1])
        upper = min(bounds[index], remaining)
        for value in range(lower, upper + 1):
            values[index] = value
            yield from visit(index + 1, remaining - value)

    yield from visit(0, total)


def _row_values(row_content: Partition) -> Partition:
    return tuple(
        label
        for label, multiplicity in enumerate(row_content, start=1)
        for _ in range(multiplicity)
    )


def _column_strict(
    previous: Partition,
    previous_start: int,
    current: Partition,
    current_start: int,
) -> bool:
    overlap_start = max(previous_start, current_start)
    overlap_end = min(previous_start + len(previous), current_start + len(current))
    return all(
        previous[column - previous_start] < current[column - current_start]
        for column in range(overlap_start, overlap_end)
    )


def lr_coefficient(
    outer: Sequence[int], inner: Sequence[int], content: Sequence[int]
) -> int:
    """Return ``c^outer_(inner,content)`` by the LR tableau rule."""
    outer_part = normalize(outer)
    inner_part = normalize(inner)
    content_part = normalize(content)
    rows = len(outer_part)
    padded_inner = inner_part + (0,) * (rows - len(inner_part))

    if len(inner_part) > rows:
        return 0
    if any(inner_row > outer_row for inner_row, outer_row in zip(padded_inner, outer_part)):
        return 0
    if sum(outer_part) != sum(inner_part) + sum(content_part):
        return 0
    if not content_part:
        return int(outer_part == inner_part)

    label_count = len(content_part)
    zero_content = (0,) * label_count
    # (preceding row values, cumulative used content) -> multiplicity.
    states: dict[tuple[Partition, Partition], int] = {((), zero_content): 1}

    for row, (outer_row, inner_row) in enumerate(zip(outer_part, padded_inner)):
        row_size = outer_row - inner_row
        previous_start = padded_inner[row - 1] if row else 0
        next_states: defaultdict[tuple[Partition, Partition], int] = defaultdict(int)

        @functools.lru_cache(maxsize=None)
        def feasible_rows(used: Partition) -> tuple[tuple[Partition, Partition], ...]:
            remaining = tuple(total - taken for total, taken in zip(content_part, used))
            if any(value < 0 for value in remaining):
                return ()
            result: list[tuple[Partition, Partition]] = []
            for row_content in _bounded_compositions(row_size, remaining):
                # In reading order this row is encountered from right to left,
                # hence labels are added from largest to smallest.  When label
                # k is finished, label k-1 from this row has not yet appeared.
                if any(
                    used[label - 1] < used[label] + row_content[label]
                    for label in range(1, label_count)
                ):
                    continue
                new_used = tuple(a + b for a, b in zip(used, row_content))
                result.append((_row_values(row_content), new_used))
            return tuple(result)

        for (previous, used), multiplicity in states.items():
            for current, new_used in feasible_rows(used):
                if row and not _column_strict(
                    previous, previous_start, current, inner_row
                ):
                    continue
                next_states[(current, new_used)] += multiplicity
        states = dict(next_states)
        if not states:
            return 0

    return sum(
        multiplicity
        for (_, used), multiplicity in states.items()
        if used == content_part
    )


def stretch(partition: Sequence[int], factor: int) -> Partition:
    if factor < 0:
        raise ValueError("stretch factor must be nonnegative")
    return tuple(factor * int(part) for part in partition)


def stretched_values(
    outer: Sequence[int],
    inner: Sequence[int],
    content: Sequence[int],
    factors: Iterable[int],
) -> dict[int, int]:
    return {
        factor: lr_coefficient(
            stretch(outer, factor), stretch(inner, factor), stretch(content, factor)
        )
        for factor in factors
    }


def self_test() -> None:
    tests = [
        ((3, 2, 1), (2, 1), (2, 1), 2),
        ((6, 4, 2), (4, 2), (4, 2), 3),
        ((4, 2), (2, 1), (2, 1), 1),
        ((2, 1, 1), (2,), (2,), 0),
        ((3,), (2,), (1,), 1),
    ]
    for outer, inner, content, expected in tests:
        actual = lr_coefficient(outer, inner, content)
        if actual != expected:
            raise AssertionError(
                f"c^{outer}_({inner},{content}) = {actual}, expected {expected}"
            )
    print(json.dumps({"self_test": "passed", "cases": len(tests)}))


def _parse_partition(text: str) -> Partition:
    if not text:
        return ()
    return normalize(tuple(int(part) for part in text.split(",")))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outer", help="comma-separated outer partition")
    parser.add_argument("--inner", help="comma-separated inner partition")
    parser.add_argument("--content", help="comma-separated content partition")
    parser.add_argument("--stretch", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.outer is None or args.inner is None or args.content is None:
        parser.error("--outer, --inner, and --content are required")
    outer = stretch(_parse_partition(args.outer), args.stretch)
    inner = stretch(_parse_partition(args.inner), args.stretch)
    content = stretch(_parse_partition(args.content), args.stretch)
    print(lr_coefficient(outer, inner, content))


if __name__ == "__main__":
    main()
