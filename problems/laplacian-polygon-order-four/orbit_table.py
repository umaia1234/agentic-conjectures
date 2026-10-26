#!/usr/bin/env python3
"""Face-orbit tables for DETAILS.md, read from face_orbits.tsv.

1. Methods: how many orbits face_certificate.py closed by a Bernstein expansion on the box,
   and how many by Kuhn simplices, with their total number of simplices.
2. The 8-dimensional faces: in each row one arc is fixed at 0 or 1 and the other two are
   free (6^4 = 1296 faces).  The points of such a face with at most four fractional weights
   lie on its 4-dimensional subfaces, which are maximal patterns.  For each orbit of these
   faces under relabelling and complement, the table lists the number of faces, and, inside
   one representative, the number of Phi-orbits of maximal patterns, how many of them needed
   Kuhn simplices, and their simplices.

Usage: python3 orbit_table.py [--table face_orbits.tsv]
"""
import argparse
import itertools
import os
import sys

import face_certificate as F


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--table", default=os.path.join(here, "face_orbits.tsv"))
    args = ap.parse_args()
    method, pieces = {}, {}
    with open(args.table) as fh:
        next(fh)
        for line in fh:
            which, rep, _, m, n = line.rstrip("\n").split("\t")
            method[which, rep], pieces[which, rep] = m, int(n)
    ok = all(m.startswith(("box", "kuhn")) for m in method.values())

    print("| | orbits | box | needed simplices | simplices |")
    print("|---|---|---|---|---|")
    for which in ("phi", "psi"):
        keys = [k for k in method if k[0] == which]
        kuhn = [k for k in keys if method[k] != "box"]
        print(f"| {which} | {len(keys)} | {len(keys) - len(kuhn)} | {len(kuhn)} "
              f"| {sum(pieces[k] for k in kuhn)} |")

    rep_phi, _ = F.orbits(F.maximal_patterns(), (False, True))
    faces8 = []
    for choice in itertools.product(range(3), "01", repeat=4):
        p = ["F"] * 12
        for r in range(4):
            p[3 * r + choice[2 * r]] = choice[2 * r + 1]
        faces8.append("".join(p))
    rep8 = {}
    for p in faces8:
        if p not in rep8:
            imgs = {F.act(p, perm, c) for perm in F.PERMS for c in (False, True)}
            for q in imgs:
                rep8[q] = min(imgs)
    size = {}
    for r in rep8.values():
        size[r] = size.get(r, 0) + 1
    print(f"\n8-dimensional faces: {len(faces8)} in {len(size)} orbits\n")
    print("| representative | faces | Phi-orbits on it | needed simplices | simplices |")
    print("|---|---|---|---|---|")
    for r in sorted(size):
        free = [k for k, ch in enumerate(r) if ch == "F"]
        subs = set()
        for keep in itertools.combinations(free, 4):
            fix = [k for k in free if k not in keep]
            for bits in itertools.product("01", repeat=4):
                p = list(r)
                for k, ch in zip(fix, bits):
                    p[k] = ch
                subs.add(rep_phi["".join(p)])
        ok = ok and all(("phi", s) in method for s in subs)
        kuhn = [s for s in subs if method.get(("phi", s)) != "box"]
        rows = " ".join(r[3 * i:3 * i + 3] for i in range(4))
        print(f"| `{rows}` | {size[r]} | {len(subs)} | {len(kuhn)} "
              f"| {sum(pieces.get(('phi', s), 0) for s in kuhn)} |")
    print("\nRESULT: every listed face is certified" if ok else "\nRESULT: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
