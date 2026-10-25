#!/usr/bin/env python3
"""Compare a 6-coloring of [1,537] with the 131 partitions of Chen--Zhu--Long.

The published list is the arXiv ancillary file (not stored in this repository):

  curl -L -o solutions537.txt \
    https://arxiv.org/src/2610.31362v1/anc/solutions537.txt
  # sha256 fcae1cd5165c585ea41028059410ea47cdfa514a5488a1c876fc8591ce4631b6

Each of its data lines is "NAME c(1)c(2)...c(537)" with colors 1..6 numbered
by least elements.  Two colorings are reported as equal if they agree after
renumbering colors by least elements, and as equivalent (the paper's notion,
Proposition 4) if they become equal after x -> r*x mod 538 for some unit r.

Usage: compare_published_537.py COLORING.col solutions537.txt
"""

from __future__ import annotations

import hashlib
import sys
from math import gcd

N = 538
EXPECTED_SHA256 = "fcae1cd5165c585ea41028059410ea47cdfa514a5488a1c876fc8591ce4631b6"


def word(color: dict[int, int]) -> str:
    """Colors of 1..537 renumbered 1..6 in order of first appearance."""
    names: dict[int, int] = {}
    return "".join(str(names.setdefault(color[x], len(names) + 1)) for x in range(1, N))


def canonical(color: dict[int, int]) -> str:
    return min(word({x: color[r * x % N] for x in range(1, N)})
               for r in range(1, N) if gcd(r, N) == 1)


def main() -> int:
    coloring_path, published_path = sys.argv[1], sys.argv[2]
    data = open(published_path, "rb").read()
    if hashlib.sha256(data).hexdigest() != EXPECTED_SHA256:
        print("warning: solutions537.txt differs from the arXiv v1 file")
    rows = [[int(t) for t in raw.split("#")[0].split()]
            for raw in open(coloring_path, encoding="utf-8")]
    mine = {x: i for i, row in enumerate(r for r in rows if r) for x in row}
    mine_word, mine_canon = word(mine), canonical(mine)
    equal, equivalent, distances = [], [], []
    for line in data.decode().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        name, text = line.split()
        theirs = {x: int(text[x - 1]) for x in range(1, N)}
        their_word = word(theirs)
        distances.append((sum(a != b for a, b in zip(their_word, mine_word)), name))
        if their_word == mine_word:
            equal.append(name)
        if canonical(theirs) == mine_canon:
            equivalent.append(name)
    distances.sort()
    print(f"published partitions read: {len(distances)}")
    print(f"equal after color renaming: {equal}")
    print(f"equivalent under x -> r*x mod 538 and renaming: {equivalent}")
    print(f"nearest (differing positions, name): {distances[:3]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
