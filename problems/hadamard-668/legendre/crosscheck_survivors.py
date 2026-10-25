#!/usr/bin/env python3
"""Cross-check the PSD survivor sets of lp_orbit_search and lp_column_search (u3 mode).

lp_orbit_search keeps every H-invariant A with sum 1, admissible 3-compression and
PSD_A <= 2L + 2; lp_column_search additionally requires the 37-compression to be one of the
admissible ones in c_file.  Hence {A-survivors with admissible 37-compression} must EQUAL the
B-survivors.  Survivor files hold one sign mask per line (bit j set <=> A = -1 on the j-th H-orbit,
orbits ordered by least element), as written by both programs.

Usage: python3 crosscheck_survivors.py gens c_file survivors_orbit survivors_column
"""
import sys

L, P = 333, 37


def main():
    gens = [int(t) % L for t in sys.argv[1].split(",")]
    H, todo = {1}, [1]
    while todo:
        x = todo.pop()
        for g in gens:
            y = x * g % L
            if y not in H:
                H.add(y)
                todo.append(y)
    orb, nor = [-1] * L, 0
    for x in range(L):
        if orb[x] < 0:
            for h in H:
                orb[h * x % L] = nor
            nor += 1
    col, cos = [-1] * P, []
    for b in range(P):
        if col[b] < 0:
            c = sorted({b * h % P for h in H})
            for y in c:
                col[y] = len(cos)
            cos.append(c)
    adm = {tuple(map(int, line.split())) for line in open(sys.argv[2]) if line.strip()}
    sa = [int(line) for line in open(sys.argv[3])]
    sb = {int(line) for line in open(sys.argv[4])}
    sel = set()
    for m in sa:
        c = [0] * P
        for x in range(L):
            c[x % P] += -1 if (m >> orb[x]) & 1 else 1
        assert all(c[y] == c[cc[0]] for cc in cos for y in cc)
        if tuple(c[cc[0]] for cc in cos) in adm:
            sel.add(m)
    print(f"gens={sys.argv[1]} orbit-search survivors={len(sa)} of which admissible 37-compression={len(sel)} "
          f"column-search survivors={len(sb)} equal sets: {sel == sb}")
    sys.exit(0 if sel == sb else 1)


if __name__ == "__main__":
    main()
