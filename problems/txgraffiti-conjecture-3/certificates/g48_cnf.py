#!/usr/bin/env python3
"""Regenerate and audit the CNF behind the DRAT certificate for i(G48) >= 16.

The CNF is satisfiable iff G48 has an independent dominating set with at most K = 15 vertices.
The drat-trim check of g48_ids_le15.drat shows it is unsatisfiable, which is the Lean
proposition `AgenticConjectures.TxGraffitiConjecture3.G48LowerBound`.

The graph is read from the `nbrs48` neighbour lists in the Lean module, so the CNF refers to the
same graph as the Lean `G48`. Standard library only.

Variables (DIMACS numbering):
  x_v = v + 1        (v = 0..47)   v is in D
  y_i = 49 + i       (i = 0..14)   D meets the pair {2i, 2i+1}
  64, 65, ...                      totalizer node outputs, allocated in recursion order
Clauses, in file order:
  1. domination, one per vertex v:  x_v or x_w1 or x_w2 or x_w3  (w1..w3 the neighbours of v)
  2. independence, one per edge {u, w} with u < w:  -x_u or -x_w
  3. pair indicators, for i = 0..14:  -x_{2i} or y_i,  -x_{2i+1} or y_i
  4. totalizer over the 33 units [y_0..y_14, x_30..x_47]: a node over the unit list L splits it
     at len(L) // 2 into children with outputs a_1..a_p and b_1..b_q (a leaf's single output is
     the unit itself) and owns outputs o_1..o_s, s = min(len(L), K + 1); for 0 <= i <= p,
     0 <= j <= q with 1 <= i + j <= s it has the clause  -a_i or -b_j or o_{i+j}  (the literal
     -a_0 or -b_0 is omitted)
  5. the root clause  -o_{K+1}  (the root has K + 1 = 16 outputs)

Why unsatisfiable means "no independent dominating set with <= K vertices": let D be one. Set
x_v = [v in D] and y_i = [2i in D or 2i+1 in D], and give every totalizer output its intended
value o_j = [at least j units below the node are true]. Clauses 1-4 then hold (4 because counts
add up along the tree). Each pair {2i, 2i+1} is an edge of G48 (checked below), so D contains at
most one vertex of each pair and the number of true units equals |D| <= K; hence o_{K+1} is false
at the root and clause 5 holds. So the CNF is satisfiable. `--check` also runs this construction
on the 16-vertex independent dominating set D48 against the K = 16 version of the CNF.

Usage:
  python3 g48_cnf.py --check          # regenerate, compare bytes and SHA-256, self-test (CI)
  python3 g48_cnf.py --write          # (re)write g48_ids_le15.cnf
  python3 g48_cnf.py --g6             # print G48 as graph6 (input for ../search/tx3check.c)
  python3 g48_cnf.py --same-as FILE   # is FILE (graph6) the same labelled graph as G48?
"""
import hashlib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "AgenticConjectures" / "TxGraffitiConjecture3.lean"
CNF = HERE / "g48_ids_le15.cnf"
SHA256 = "f916d6b4a0d21f0764c9425634bcd8f50a3c849d7e681971ff6c16b7f50bbbf2"
K = 15
D48 = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 34]


def read_graph():
    src = LEAN.read_text()
    m = re.search(r"def nbrs48 : List \(List ℕ\) :=\s*\[(.*?)\]\n\n", src, re.S)
    if not m:
        sys.exit(f"nbrs48 not found in {LEAN}")
    nbrs = [[int(t) for t in g.split(",")] for g in re.findall(r"\[([0-9, ]+)\]", m.group(1))]
    n = len(nbrs)
    assert n == 48, n
    for v, ws in enumerate(nbrs):
        assert len(ws) == 3 and len(set(ws)) == 3, (v, ws)
        for w in ws:
            assert 0 <= w < n and w != v and v in nbrs[w], (v, w)
    for i in range(15):
        assert 2 * i + 1 in nbrs[2 * i], i
    return nbrs


def totalizer(units, k, top):
    cls = []

    def build(lits):
        nonlocal top
        if len(lits) == 1:
            return [lits[0]]
        mid = len(lits) // 2
        a, b = build(lits[:mid]), build(lits[mid:])
        size = min(len(lits), k + 1)
        out = list(range(top + 1, top + size + 1))
        top += size
        for i in range(len(a) + 1):
            for j in range(len(b) + 1):
                s = i + j
                if s == 0 or s > size:
                    continue
                c = []
                if i:
                    c.append(-a[i - 1])
                if j:
                    c.append(-b[j - 1])
                c.append(out[s - 1])
                cls.append(c)
        return out

    root = build(units)
    assert len(root) == k + 1
    cls.append([-root[k]])
    return cls, top


def build_cnf(nbrs, k):
    n = len(nbrs)
    cls = [[v + 1] + [w + 1 for w in nbrs[v]] for v in range(n)]
    cls += [[-(u + 1), -(w + 1)] for u in range(n) for w in nbrs[u] if u < w]
    top = n
    units = []
    for i in range(15):
        top += 1
        cls += [[-(2 * i + 1), top], [-(2 * i + 2), top]]
        units.append(top)
    units += [v + 1 for v in range(30, n)]
    tcls, top = totalizer(units, k, top)
    return top, cls + tcls


def graph6(nbrs):
    n, bits = len(nbrs), []
    for j in range(1, n):
        bits += [int(i in nbrs[j]) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    return chr(63 + n) + "".join(chr(63 + int("".join(map(str, bits[t:t + 6])), 2))
                                 for t in range(0, len(bits), 6))


def edges_of_graph6(text):
    n, data = ord(text[0]) - 63, text[1:]
    bits = [(ord(ch) - 63) >> (5 - t) & 1 for ch in data for t in range(6)]
    pairs = [(i, j) for j in range(1, n) for i in range(j)]
    return n, {p for p, b in zip(pairs, bits) if b}


def dimacs(nvars, cls):
    return f"p cnf {nvars} {len(cls)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cls)


def intended_assignment(nbrs, k, D):
    """Values of all variables for an independent dominating set D (the soundness construction)."""
    val = {v + 1: v in D for v in range(48)}
    for i in range(15):
        val[49 + i] = (2 * i in D) or (2 * i + 1 in D)
    units = [49 + i for i in range(15)] + [v + 1 for v in range(30, 48)]
    top = 63

    def build(lits):
        nonlocal top
        if len(lits) == 1:
            return [lits[0]], int(val[lits[0]])
        mid = len(lits) // 2
        _, ca = build(lits[:mid])
        _, cb = build(lits[mid:])
        size = min(len(lits), k + 1)
        out = list(range(top + 1, top + size + 1))
        top += size
        for j, o in enumerate(out, start=1):
            val[o] = ca + cb >= j
        return out, ca + cb

    build(units)
    return val


def self_test(nbrs):
    D = set(D48)
    assert all(w not in D for v in D for w in nbrs[v]), "D48 not independent"
    assert all(v in D or any(w in D for w in nbrs[v]) for v in range(48)), "D48 not dominating"
    nv, cls = build_cnf(nbrs, 16)
    val = intended_assignment(nbrs, 16, D)
    assert len(val) == nv
    bad = [c for c in cls if not any(val[abs(l)] == (l > 0) for l in c)]
    assert not bad, bad[:3]


def main():
    nbrs = read_graph()
    nv, cls = build_cnf(nbrs, K)
    text = dimacs(nv, cls)
    digest = hashlib.sha256(text.encode()).hexdigest()
    if sys.argv[1:] == ["--write"]:
        CNF.write_text(text)
        print(f"wrote {CNF.name}: {nv} variables, {len(cls)} clauses, sha256 {digest}")
        return
    if sys.argv[1:] == ["--g6"]:
        print(graph6(nbrs))
        return
    if len(sys.argv) == 3 and sys.argv[1] == "--same-as":
        n, edges = edges_of_graph6(Path(sys.argv[2]).read_text().strip())
        same = n == 48 and edges == {(u, w) for u in range(48) for w in nbrs[u] if u < w}
        print("same labelled graph as G48" if same else "DIFFERENT from G48")
        sys.exit(0 if same else 1)
    if sys.argv[1:] != ["--check"]:
        sys.exit(__doc__)
    self_test(nbrs)
    on_disk = CNF.read_bytes()
    ok = on_disk == text.encode() and digest == SHA256
    print(f"regenerated {nv} variables, {len(cls)} clauses, sha256 {digest}")
    print(f"committed CNF {'matches' if on_disk == text.encode() else 'DIFFERS'}; "
          f"expected sha256 {'matches' if digest == SHA256 else 'DIFFERS'}")
    print("self-test: D48 (16 vertices) satisfies the K = 16 CNF under the intended assignment")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
