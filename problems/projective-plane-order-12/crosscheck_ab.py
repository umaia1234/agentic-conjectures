#!/usr/bin/env python3
"""Cross-check the outputs of method A (ds_enumerate) and method B (ds_search_normalized).

Usage: python3 crosscheck_ab.py v m A_output B_output

Both outputs must list sets of the same size k for the same (v, m) in `SOLUTION ...` lines
(method B prefixes `t=<t>`).  The script re-checks from scratch (stdlib only) that every
listed set contains 0 and 1, has pairwise distinct differences, and avoids N = m Z_v; then
it filters the method-A list by method B's normal form (third smallest element equal to
the least ratio (c-a)/(b-a), b-a a unit) and requires the filtered list to equal the
method-B list exactly.  Exit code 0 iff everything matches.
"""
import sys
from math import gcd


def parse(path):
    sets = []
    with open(path) as fh:
        for line in fh:
            if not line.startswith("SOLUTION"):
                continue
            toks = [t for t in line.split()[1:] if not t.startswith("t=")]
            sets.append(tuple(int(t) for t in toks))
    return sets


def valid(s, v, m):
    if len(set(s)) != len(s) or 0 not in s or 1 not in s:
        return False
    diffs = [(a - b) % v for a in s for b in s if a != b]
    return len(diffs) == len(set(diffs)) and all(d % m for d in diffs)


def normal(s, v):
    rest = sorted(set(s) - {0, 1})
    t = rest[0]
    for a in s:
        for b in s:
            if a == b or gcd((b - a) % v, v) != 1:
                continue
            ib = pow((b - a) % v, -1, v)
            for c in s:
                if c != a and c != b and (c - a) * ib % v < t:
                    return False
    return True


def compare(v, m, a_path, b_path):
    a_sets, b_sets = parse(a_path), parse(b_path)
    sizes = {len(s) for s in a_sets} | {len(s) for s in b_sets}
    if len(sizes) > 1:
        print("FAIL: mixed set sizes", sizes)
        return 1
    for name, lst in (("A", a_sets), ("B", b_sets)):
        if len(set(lst)) != len(lst):
            print(f"FAIL: duplicate sets in {name}")
            return 1
        bad = [s for s in lst if not valid(s, v, m)]
        if bad:
            print(f"FAIL: invalid set in {name}: {bad[0]}")
            return 1
    a_norm = {tuple(sorted(s)) for s in a_sets if normal(s, v)}
    b_norm = {tuple(sorted(s)) for s in b_sets}
    if not all(normal(s, v) for s in b_norm):
        print("FAIL: method B output not in normal form")
        return 1
    print(f"A sets={len(a_sets)} A in normal form={len(a_norm)} B sets={len(b_norm)}")
    if a_norm != b_norm:
        print(f"FAIL: A-only={len(a_norm - b_norm)} B-only={len(b_norm - a_norm)}")
        return 1
    print("OK: method A filtered by the normal form equals method B")
    return 0


def main():
    if len(sys.argv) != 5:
        print(__doc__)
        return 2
    return compare(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4])


if __name__ == "__main__":
    sys.exit(main())
