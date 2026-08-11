#!/usr/bin/env python3
"""Independent exact checks for the Floridian-solitaire construction.

The program uses the definitions in arXiv:2608.08313v1.  A partition is a
sorted tuple; repeated parts are allowed, while distinct part sizes in a
separated partition differ by at least two.
"""

from __future__ import annotations

from collections import Counter
from itertools import product


def separated(partition: tuple[int, ...]) -> bool:
    values = sorted(set(partition))
    return all(b - a >= 2 for a, b in zip(values, values[1:]))


def alpha_targets(partition: tuple[int, ...]) -> set[tuple[int, ...]]:
    """Return every legal middle-of-turn T-position reachable by alpha.

    For a size m>1, selecting a nonempty proper subset of its copies leaves
    both m-1 and m and therefore cannot be separated.  Thus 0/all are the
    only choices worth enumerating.  Copies of 1 may be selected partially.
    """

    counts = Counter(partition)
    sizes = sorted(counts)
    choices = [range(counts[m] + 1) if m == 1 else (0, counts[m]) for m in sizes]
    targets: set[tuple[int, ...]] = set()

    for selected_counts in product(*choices):
        s = sum(selected_counts)
        if s == 0:
            continue

        out: list[int] = [s]
        for m, selected in zip(sizes, selected_counts):
            out.extend([m] * (counts[m] - selected))
            if m > 1:
                out.extend([m - 1] * selected)

        target = tuple(sorted(out))
        if target == partition or not separated(target):
            continue

        p = len(target)
        if p in target or p + 2 in target:
            continue
        targets.add(target)

    return targets


def represent_weight(r: int, k: int) -> list[int]:
    """Find r indices with consecutive support and sum k.

    This realizes every 0 <= k <= r(r-1)/2.  The returned indices lie in
    {0,...,h}, with every index in that set occurring at least once.
    """

    assert 0 <= k <= r * (r - 1) // 2
    for h in range(r):
        triangular = h * (h + 1) // 2
        extras = r - h - 1
        if triangular <= k <= h * r - triangular:
            indices = list(range(h + 1))
            remainder = k - triangular
            if h:
                indices.extend([h] * (remainder // h))
                if remainder % h:
                    indices.append(remainder % h)
                indices.extend([0] * (extras - (remainder // h) - bool(remainder % h)))
            else:
                indices.extend([0] * extras)
            assert len(indices) == r and sum(indices) == k
            assert set(indices) == set(range(h + 1))
            return indices
    raise AssertionError((r, k))


def new_open_case_witness(n: int) -> tuple[int, ...]:
    """Construct an immediate loss when n == 0 or 2 (mod 6), n > 6."""

    assert n > 6 and n % 6 in (0, 2)
    if n == 18:
        return (1, 5, 5, 7)
    if n == 20:
        return (4, 4, 6, 6)

    for r in range(2, n + 1, 2):
        for delta in (0, 1):
            base = r + 2 + 2 * delta
            excess = n - r * base
            if excess < 0 or excess % 2:
                continue
            k = excess // 2
            if k <= r * (r - 1) // 2:
                indices = represent_weight(r, k)
                answer = tuple(sorted(base + 2 * i for i in indices))
                assert len(answer) == r and sum(answer) == n and separated(answer)
                return answer
    raise AssertionError(f"coverage failed at n={n}")


def all_n_witness(n: int) -> tuple[int, ...]:
    """Combine the paper's easy residue classes with the new construction."""

    assert n > 6
    if n % 2:
        m = (n - 1) // 2
        return tuple(sorted((1, m, m)))
    if n % 6 == 4:
        m = (n - 1) // 3
        return tuple(sorted((1,) + (3,) * m))
    return new_open_case_witness(n)


def main() -> None:
    checked = 0
    open_checked = 0
    for n in range(7, 501):
        witness = all_n_witness(n)
        assert sum(witness) == n
        assert separated(witness), (n, witness)
        assert not alpha_targets(witness), (n, witness, alpha_targets(witness))
        checked += 1
        if n % 6 in (0, 2):
            open_checked += 1

    print(f"verified immediate losses for every n=7..500 ({checked} cases)")
    print(f"verified new residue-class construction in {open_checked} open cases")
    for n in (8, 12, 14, 18, 20, 24, 26, 30, 32, 48, 80, 500):
        if n % 6 in (0, 2):
            print(n, new_open_case_witness(n))


if __name__ == "__main__":
    main()
