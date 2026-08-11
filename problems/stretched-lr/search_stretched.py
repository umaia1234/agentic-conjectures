#!/usr/bin/env python3
"""Reproducible classic-lrcalc search for negative stretched LR coefficients.

All interpolation is over ``fractions.Fraction``.  The classic lrcalc ABI
returns a signed 64-bit integer; this script therefore rejects negative or
decreasing sample sequences as suspected overflow.  The Rust search recorded
in README.md used u128 counts and BigRational coefficients instead.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import math
import random
import time
from collections.abc import Iterator, Sequence
from fractions import Fraction
from pathlib import Path


Partition = tuple[int, ...]


class _Vector(ctypes.Structure):
    _fields_ = [("length", ctypes.c_size_t), ("array", ctypes.c_int * 1)]


_VectorPointer = ctypes.POINTER(_Vector)


class ClassicLrCalc:
    """Minimal ctypes wrapper around Anders Buch's classic liblrcalc."""

    def __init__(self, library: str | Path) -> None:
        self.library_path = str(Path(library).resolve())
        self._library = ctypes.CDLL(self.library_path)
        self._library.v_new.argtypes = [ctypes.c_int]
        self._library.v_new.restype = _VectorPointer
        self._library.v_free1.argtypes = [_VectorPointer]
        self._library.lrcoef.argtypes = [
            _VectorPointer,
            _VectorPointer,
            _VectorPointer,
        ]
        self._library.lrcoef.restype = ctypes.c_longlong

    def _vector(self, partition: Sequence[int]) -> _VectorPointer:
        vector = self._library.v_new(len(partition))
        array = ctypes.cast(
            ctypes.addressof(vector.contents) + _Vector.array.offset,
            ctypes.POINTER(ctypes.c_int),
        )
        for index, part in enumerate(partition):
            array[index] = int(part)
        return vector

    def coefficient(
        self,
        outer: Sequence[int],
        inner: Sequence[int],
        content: Sequence[int],
        stretch: int = 1,
    ) -> int:
        partitions = [
            tuple(stretch * int(part) for part in partition)
            for partition in (outer, inner, content)
        ]
        vectors = [self._vector(partition) for partition in partitions]
        try:
            result = int(self._library.lrcoef(*vectors))
        finally:
            for vector in vectors:
                self._library.v_free1(vector)
        if result < 0:
            raise OverflowError("classic lrcalc returned a negative signed-64 value")
        return result


def degree_bound(*partitions: Sequence[int]) -> int:
    """Ambient hive dimension for rank equal to the maximum input length."""
    rank = max((len(tuple(partition)) for partition in partitions), default=0)
    return max(0, (rank - 1) * (rank - 2) // 2)


def interpolate_consecutive(values: Sequence[int]) -> tuple[Fraction, ...]:
    """Interpolate values at t=0,1,... in the ordinary power basis."""
    differences = [Fraction(value) for value in values]
    newton_coefficients: list[Fraction] = []
    while differences:
        newton_coefficients.append(differences[0])
        differences = [
            right - left for left, right in zip(differences, differences[1:])
        ]

    result = [Fraction(0)] * len(values)
    binomial_polynomial = [Fraction(1)]
    for order, newton_coefficient in enumerate(newton_coefficients):
        for index, coefficient in enumerate(binomial_polynomial):
            result[index] += newton_coefficient * coefficient
        if order + 1 == len(values):
            break
        next_polynomial = [Fraction(0)] * (len(binomial_polynomial) + 1)
        for index, coefficient in enumerate(binomial_polynomial):
            next_polynomial[index] -= coefficient * order
            next_polynomial[index + 1] += coefficient
        divisor = order + 1
        binomial_polynomial = [coefficient / divisor for coefficient in next_polynomial]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def evaluate(coefficients: Sequence[Fraction], value: int) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def stretched_polynomial(
    calculator: ClassicLrCalc,
    outer: Partition,
    inner: Partition,
    content: Partition,
) -> tuple[tuple[int, ...], tuple[Fraction, ...]] | None:
    base = calculator.coefficient(outer, inner, content)
    if base == 0:
        return None
    bound = degree_bound(outer, inner, content)
    values = [1, base]
    for stretch in range(2, bound + 3):
        value = calculator.coefficient(outer, inner, content, stretch)
        if value < values[-1]:
            raise OverflowError("stretched sequence decreased; possible signed-64 wrap")
        values.append(value)
    coefficients = interpolate_consecutive(values[: bound + 1])
    for stretch in (bound + 1, bound + 2):
        if evaluate(coefficients, stretch) != values[stretch]:
            raise ArithmeticError(f"interpolation failed at t={stretch}")
    return tuple(values), coefficients


def partitions(total: int, maximum: int, max_length: int) -> Iterator[Partition]:
    if total == 0:
        yield ()
        return
    if max_length == 0:
        return
    for first in range(min(total, maximum), 0, -1):
        for rest in partitions(total - first, first, max_length - 1):
            yield (first,) + rest


def random_partition(rng: random.Random, total: int, rows: int) -> Partition:
    boxes = [0] * rows
    for _ in range(total):
        boxes[rng.randrange(rows)] += 1
    boxes.sort(reverse=True)
    while boxes and boxes[-1] == 0:
        boxes.pop()
    return tuple(boxes)


def grow_partition(
    rng: random.Random, inner: Partition, boxes: int, rows: int
) -> Partition:
    outer = list(inner) + [0] * (rows - len(inner))
    for _ in range(boxes):
        addable = [
            row for row in range(rows) if row == 0 or outer[row] < outer[row - 1]
        ]
        outer[rng.choice(addable)] += 1
    while outer and outer[-1] == 0:
        outer.pop()
    return tuple(outer)


def random_triples(
    rng: random.Random, iterations: int, rows: int, max_total: int
) -> Iterator[tuple[Partition, Partition, Partition]]:
    for _ in range(iterations):
        total = rng.randint(6, max_total)
        inner_sum = rng.randint(1, total - 1)
        content_sum = total - inner_sum
        inner = random_partition(rng, inner_sum, rows)
        content = random_partition(rng, content_sum, rows)
        if rng.randrange(2):
            inner, content = content, inner
        outer = grow_partition(rng, inner, sum(content), rows)
        yield outer, inner, content


def kostka_translation_triples(
    rows: int, max_total: int
) -> Iterator[tuple[Partition, Partition, Partition]]:
    """Enumerate K_{alpha,beta} encoded as an LR coefficient."""
    for beta_sum in range(1, max_total + 1):
        for beta in partitions(beta_sum, beta_sum, rows):
            if len(beta) < 5:
                continue
            outer_sum = sum((index + 1) * part for index, part in enumerate(beta))
            if outer_sum > max_total:
                continue
            outer = tuple(sum(beta[index:]) for index in range(len(beta)))
            inner = outer[1:]
            for content in partitions(beta_sum, beta_sum, rows):
                yield outer, inner, content


def self_test(calculator: ClassicLrCalc) -> None:
    tests = [
        ((3, 2, 1), (2, 1), (2, 1), 1, 2),
        ((3, 2, 1), (2, 1), (2, 1), 2, 3),
        ((4, 2), (2, 1), (2, 1), 1, 1),
        ((2, 1, 1), (2,), (2,), 1, 0),
    ]
    for outer, inner, content, stretch, expected in tests:
        actual = calculator.coefficient(outer, inner, content, stretch)
        if actual != expected:
            raise AssertionError((outer, inner, content, stretch, actual, expected))


def fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--library", required=True, help="path to liblrcalc.so")
    parser.add_argument("--mode", choices=("random", "kostka"), default="random")
    parser.add_argument("--iterations", type=int, default=100_000)
    parser.add_argument("--rows", type=int, default=7)
    parser.add_argument("--max-total", type=int, default=30)
    parser.add_argument("--seed", type=int, default=20260811)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.rows <= 7:
        parser.error("--rows must lie in 1..7")
    if not 1 <= args.max_total <= 30:
        parser.error("--max-total must lie in 1..30")

    calculator = ClassicLrCalc(args.library)
    self_test(calculator)
    if args.self_test:
        print(json.dumps({"self_test": "passed", "library": calculator.library_path}))
        return

    rng = random.Random(args.seed)
    source = (
        random_triples(rng, args.iterations, args.rows, args.max_total)
        if args.mode == "random"
        else kostka_translation_triples(args.rows, args.max_total)
    )
    started = time.monotonic()
    generated = positive = interpolated = overflow = 0
    for outer, inner, content in source:
        generated += 1
        try:
            result = stretched_polynomial(calculator, outer, inner, content)
        except OverflowError:
            overflow += 1
            continue
        if result is None:
            continue
        positive += 1
        values, coefficients = result
        interpolated += 1
        negative = [
            (degree, fraction_text(coefficient))
            for degree, coefficient in enumerate(coefficients)
            if coefficient < 0
        ]
        if negative:
            print(
                json.dumps(
                    {
                        "status": "negative_candidate",
                        "lambda": outer,
                        "mu": inner,
                        "nu": content,
                        "values": values,
                        "coefficients_ascending": [
                            fraction_text(coefficient) for coefficient in coefficients
                        ],
                        "negative": negative,
                    }
                )
            )
            return
    print(
        json.dumps(
            {
                "status": "UNKNOWN_no_counterexample",
                "mode": args.mode,
                "seed": args.seed,
                "generated": generated,
                "positive": positive,
                "interpolated": interpolated,
                "suspected_overflow": overflow,
                "seconds": time.monotonic() - started,
                "trust_boundary": "classic lrcalc signed-64 counts",
            }
        )
    )


if __name__ == "__main__":
    main()
