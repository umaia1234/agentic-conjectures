#!/usr/bin/env python3
"""Independently verify the NFA witnesses in witnesses.json.

Unlike enumerate_binary.py, k-image-boundedness is checked here by closing the
letter relations under relational composition and inspecting every row of every
word transformation.  Shortest mortality is then checked in the full powerset
automaton.  Keeping these implementations separate reduces the chance that a
single subset-reachability bug validates both the search and its witnesses.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path
from typing import Any, Sequence


Transformation = tuple[int, ...]


def destinations_to_mask(destinations: Sequence[int], n: int) -> int:
    mask = 0
    for destination in destinations:
        if not 0 <= destination < n:
            raise ValueError(f"destination {destination} is outside 0..{n - 1}")
        mask |= 1 << destination
    return mask


def transform_subset(subset: int, transformation: Transformation) -> int:
    output = 0
    for state, row in enumerate(transformation):
        if subset & (1 << state):
            output |= row
    return output


def compose(
    first: Transformation, second: Transformation
) -> Transformation:
    """Return the action 'first, then second'."""

    return tuple(transform_subset(row, second) for row in first)


def generated_transformation_monoid(
    letters: Sequence[Transformation], n: int
) -> set[Transformation]:
    identity = tuple(1 << state for state in range(n))
    closure = {identity}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for letter in letters:
            target = compose(current, letter)
            if target not in closure:
                closure.add(target)
                queue.append(target)
    return closure


def shortest_mortal_path(
    letters: Sequence[Transformation], alphabet: Sequence[str], n: int
) -> tuple[str | None, list[int] | None, dict[int, int]]:
    full_set = (1 << n) - 1
    queue = deque([full_set])
    distance = {full_set: 0}
    predecessor: dict[int, tuple[int, int]] = {}

    while queue:
        current = queue.popleft()
        for index, letter in enumerate(letters):
            target = transform_subset(current, letter)
            if target in distance:
                continue
            distance[target] = distance[current] + 1
            predecessor[target] = (current, index)
            queue.append(target)

    if 0 not in distance:
        return None, None, distance

    indices: list[int] = []
    cursor = 0
    while cursor != full_set:
        previous, index = predecessor[cursor]
        indices.append(index)
        cursor = previous
    indices.reverse()
    word = "".join(alphabet[index] for index in indices)

    path = [full_set]
    current = full_set
    for index in indices:
        current = transform_subset(current, letters[index])
        path.append(current)
    return word, path, distance


def format_subset(subset: int, n: int) -> str:
    return "{" + ",".join(str(q) for q in range(n) if subset & (1 << q)) + "}"


def verify_record(record: dict[str, Any]) -> None:
    identifier = record["id"]
    n = int(record["n"])
    k = int(record["k"])
    alphabet = list(record["alphabet"])
    if len(set(alphabet)) != len(alphabet):
        raise AssertionError(f"{identifier}: alphabet symbols are not unique")

    transitions = record["transitions"]
    letters: list[Transformation] = []
    for symbol in alphabet:
        rows = transitions[symbol]
        if len(rows) != n:
            raise AssertionError(f"{identifier}: letter {symbol} has {len(rows)} rows")
        letters.append(tuple(destinations_to_mask(row, n) for row in rows))

    monoid = generated_transformation_monoid(letters, n)
    largest_row = max(row.bit_count() for action in monoid for row in action)
    if largest_row > k:
        raise AssertionError(
            f"{identifier}: a generated word has an image of size {largest_row} > {k}"
        )

    shortest_word, path, distances = shortest_mortal_path(letters, alphabet, n)
    claimed_word = record["claimed_shortest_mortal_word"]
    claimed_length = int(record["claimed_shortest_mortal_length"])
    if shortest_word is None or path is None:
        raise AssertionError(f"{identifier}: automaton is complete, contrary to claim")
    if distances[0] != claimed_length:
        raise AssertionError(
            f"{identifier}: shortest distance is {distances[0]}, claimed {claimed_length}"
        )

    current = (1 << n) - 1
    claimed_path = [current]
    symbol_to_index = {symbol: index for index, symbol in enumerate(alphabet)}
    for symbol in claimed_word:
        if symbol not in symbol_to_index:
            raise AssertionError(f"{identifier}: unknown symbol {symbol!r}")
        current = transform_subset(current, letters[symbol_to_index[symbol]])
        claimed_path.append(current)
    if current != 0:
        raise AssertionError(f"{identifier}: claimed word is not mortal")
    if len(claimed_word) != claimed_length:
        raise AssertionError(f"{identifier}: claimed word length metadata is inconsistent")

    print(f"PASS {identifier}")
    print(f"  generated transformation monoid size: {len(monoid)}")
    print(f"  maximum singleton-image size in monoid: {largest_row}")
    print(f"  reachable full-set subsets: {len(distances)}")
    print(f"  independently found shortest word: {shortest_word!r}")
    print(
        "  claimed-word path: "
        + " -> ".join(format_subset(subset, n) for subset in claimed_path)
    )


def main() -> None:
    default_path = Path(__file__).with_name("witnesses.json")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness_file", nargs="?", type=Path, default=default_path)
    args = parser.parse_args()

    payload = json.loads(args.witness_file.read_text(encoding="utf-8"))
    if payload.get("format_version") != 1:
        raise ValueError("unsupported witness format")
    for record in payload["automata"]:
        verify_record(record)


if __name__ == "__main__":
    main()
