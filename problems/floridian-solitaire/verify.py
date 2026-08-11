#!/usr/bin/env python3
"""Exhaustively verify the Floridian-solitaire immediate-loss witnesses.

The implementation follows the definitions in arXiv:2608.08313v1:
an alpha move selects individual parts, reduces them, adds a part equal
to the number selected, must change the partition, and must leave both
the alpha result and its Omega image separated.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Sequence


Partition = tuple[int, ...]


def normalized(parts: Iterable[int]) -> Partition:
    """Return the positive parts in nondecreasing order."""

    return tuple(sorted(part for part in parts if part > 0))


def is_separated(partition: Sequence[int]) -> bool:
    """Distinct part sizes must differ by at least two."""

    sizes = sorted(set(partition))
    return all(right - left >= 2 for left, right in zip(sizes, sizes[1:]))


def omega(partition: Sequence[int]) -> Partition:
    """Apply the paper's Omega rule."""

    p = len(partition)
    return normalized([part - 1 for part in partition] + [p])


def is_in_T(partition: Sequence[int]) -> bool:
    """Test membership in T(n), using the paper's Lemma 7 criterion."""

    p = len(partition)
    return is_separated(partition) and p not in partition and p + 2 not in partition


def selection_profiles(partition: Sequence[int]) -> Iterator[tuple[int, ...]]:
    """Enumerate all nonempty selections, compressed by equal-part counts.

    A profile records how many copies of each distinct part size are
    selected.  Selections differing only by the identities of equal
    copies yield identical alpha results, so this is exhaustive for
    legality while avoiding redundant permutations.
    """

    groups = sorted(Counter(partition).items())
    for profile in product(*(range(count + 1) for _, count in groups)):
        if any(profile):
            yield profile


def alpha_result(partition: Sequence[int], profile: Sequence[int]) -> Partition:
    """Apply one selection profile, without deciding whether it is legal."""

    groups = sorted(Counter(partition).items())
    if len(profile) != len(groups):
        raise ValueError("selection profile has the wrong number of size classes")

    selected = sum(profile)
    if selected < 1:
        raise ValueError("an alpha selection must be nonempty")

    result: list[int] = []
    for (part, count), chosen in zip(groups, profile):
        if not 0 <= chosen <= count:
            raise ValueError("selection count is out of range")
        result.extend([part] * (count - chosen))
        if part > 1:
            result.extend([part - 1] * chosen)
    result.append(selected)
    return normalized(result)


def is_legal_alpha_result(before: Sequence[int], after: Sequence[int]) -> bool:
    """Apply the three literal legality conditions for an alpha result."""

    return (
        tuple(after) != tuple(before)
        and is_separated(after)
        and is_separated(omega(after))
    )


def support_sum(r: int, target: int) -> list[int]:
    """Construct r values with consecutive support and prescribed sum.

    Requires 0 <= target <= r(r-1)/2.  This implements the
    representation lemma from PROOF.md.
    """

    if not 0 <= target <= r * (r - 1) // 2:
        raise ValueError("target outside the representation interval")

    for h in range(r):
        lower = h * (h + 1) // 2
        upper = h * r - lower
        if lower <= target <= upper:
            values = list(range(h + 1))
            remaining = target - lower
            for _ in range(r - h - 1):
                value = min(h, remaining)
                values.append(value)
                remaining -= value
            if remaining != 0:
                raise AssertionError("greedy representation failed")
            values.sort()
            if len(values) != r or sum(values) != target:
                raise AssertionError("bad support-sum construction")
            if set(values) != set(range(h + 1)):
                raise AssertionError("constructed support is not consecutive")
            return values

    raise AssertionError("the representation intervals did not cover target")


def block_witness(n: int) -> Partition:
    """Construct a block-lemma witness for an eligible even n."""

    if n % 2:
        raise ValueError("the implemented block search uses even r")

    for r in range(2, n + 1, 2):
        for delta in (0, 1):
            smallest = r + 2 + 2 * delta
            baseline = r * smallest
            difference = n - baseline
            if difference < 0 or difference % 2:
                continue
            target = difference // 2
            if target <= r * (r - 1) // 2:
                offsets = support_sum(r, target)
                return normalized(smallest + 2 * value for value in offsets)

    raise ValueError(f"no block-lemma witness for n={n}")


@dataclass(frozen=True)
class Witness:
    partition: Partition
    family: str


def make_witness(n: int) -> Witness:
    """Construct the proof's witness for every n > 6."""

    if n <= 6:
        raise ValueError("the theorem and generator have domain n > 6")

    if n % 2 == 1:
        m = (n - 1) // 2
        return Witness(normalized((1, m, m)), "paper: n=2m+1")

    if n % 6 == 4:
        m = (n - 1) // 3
        return Witness(normalized([1] + [3] * m), "paper: n=3m+1")

    if n == 18:
        return Witness((1, 5, 5, 7), "exception: n=18")

    if n == 20:
        return Witness((4, 4, 6, 6), "exception: n=20")

    return Witness(block_witness(n), "new block lemma")


@dataclass(frozen=True)
class CheckResult:
    selection_profiles: int
    separated_intermediates: int


def verify_witness(n: int, witness: Witness) -> CheckResult:
    """Exhaustively prove that one generated witness is an immediate loss."""

    partition = witness.partition
    if any(part <= 0 for part in partition):
        raise AssertionError(f"n={n}: partition has a nonpositive part: {partition}")
    if tuple(sorted(partition)) != partition:
        raise AssertionError(f"n={n}: partition is not normalized: {partition}")
    if sum(partition) != n:
        raise AssertionError(f"n={n}: parts sum to {sum(partition)}: {partition}")
    if not is_separated(partition):
        raise AssertionError(f"n={n}: initial partition is not separated: {partition}")

    checked = 0
    separated_intermediates = 0
    for profile in selection_profiles(partition):
        checked += 1
        after = alpha_result(partition, profile)
        if sum(after) != n:
            raise AssertionError(
                f"n={n}: alpha operation did not preserve n: {profile} -> {after}"
            )

        if is_separated(after):
            separated_intermediates += 1
            # Independently check the paper's characterization of T(n).
            if is_separated(omega(after)) != is_in_T(after):
                raise AssertionError(
                    f"n={n}: T(n) criterion disagrees with direct Omega: {after}"
                )

        if is_legal_alpha_result(partition, after):
            raise AssertionError(
                f"n={n}: witness has a legal alpha move: "
                f"{partition}, selection={profile}, result={after}, "
                f"omega={omega(after)}"
            )

    return CheckResult(checked, separated_intermediates)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=7, help="first n (default: 7)")
    parser.add_argument("--end", type=int, default=500, help="last n (default: 500)")
    parser.add_argument(
        "--show-witnesses",
        action="store_true",
        help="print every generated partition",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.start <= 6 or args.end < args.start:
        raise SystemExit("require 7 <= --start <= --end")

    family_counts: Counter[str] = Counter()
    total_profiles = 0
    total_separated_intermediates = 0
    largest_check = (0, 0, ())

    for n in range(args.start, args.end + 1):
        witness = make_witness(n)
        result = verify_witness(n, witness)
        family_counts[witness.family] += 1
        total_profiles += result.selection_profiles
        total_separated_intermediates += result.separated_intermediates
        largest_check = max(
            largest_check,
            (result.selection_profiles, n, witness.partition),
        )
        if args.show_witnesses:
            print(f"n={n}: {witness.partition} [{witness.family}]")

    print(f"VERIFIED immediate-loss witnesses for every n={args.start}..{args.end}")
    print(f"witnesses checked: {args.end - args.start + 1}")
    print(f"nonempty selection profiles checked: {total_profiles}")
    print(f"separated intermediate partitions cross-checked: {total_separated_intermediates}")
    print("families:")
    for family, count in sorted(family_counts.items()):
        print(f"  {family}: {count}")
    profiles, n, partition = largest_check
    print(f"largest single exhaustive check: n={n}, profiles={profiles}, witness={partition}")


if __name__ == "__main__":
    main()
