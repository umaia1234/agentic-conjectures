#!/usr/bin/env python3
"""Export Cayley tables of all groups of order lo..hi from GAP's SmallGroups
library (via passagemath-gap).  One group per line:
  order id "StructureDescription" t[0][0] ... t[m-1][m-1]
Element 0 is the identity.  usage: export_groups.py lo hi > groups.txt"""
import sys
from sage.all__sagemath_gap import libgap

lo, hi = int(sys.argv[1]), int(sys.argv[2])
for m in range(lo, hi + 1):
    for i in range(1, int(libgap.NumberSmallGroups(m)) + 1):
        G = libgap.SmallGroup(m, i)
        els = list(libgap.Elements(G))
        one = libgap.Identity(G)
        els.sort(key=lambda g: g != one)  # identity first, stable otherwise
        assert els[0] == one and len(els) == m
        pos = {str(g): k for k, g in enumerate(els)}
        assert len(pos) == m
        tab = [pos[str(a * b)] for a in els for b in els]
        desc = str(libgap.StructureDescription(G)).replace(" ", "")
        sys.stdout.write("%d %d %s %s\n" % (m, i, desc, " ".join(map(str, tab))))
    sys.stdout.flush()
