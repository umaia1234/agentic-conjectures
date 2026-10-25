#!/usr/bin/env python3
"""CNF for translation-invariant E677 countermodels over a finite group G.

Magma on G: x<>y = x * f(x^-1 * y) for a permutation f of G.  Left
translations are automorphisms, so E677 holds iff it holds at y = e, i.e.
  x = f(x * f(x^-1 * u)),   u = f(x) * f(f(x)^-1)        for all x,
and E255 fails (at every element) iff f has no fixed point (y<>e = e iff
f(y^-1) = y^-1).  Variables F[z][v] <-> f(z) = v.
usage: tinv_cnf.py <groups file> <order> <id> [general] [fix a b] > out.cnf
("fix a b" adds the units f(e) = a, f(a) = b of a symmetry-breaking case.)"""
import sys


def read_group(path, order, gid):
    with open(path) as fh:
        for line in fh:
            t = line.split()
            if int(t[0]) == order and int(t[1]) == gid:
                m = int(t[0])
                tab = list(map(int, t[3:]))
                assert len(tab) == m * m
                mul = [tab[i * m:(i + 1) * m] for i in range(m)]
                R = range(m)                       # group axioms, identity 0
                assert all(mul[0][x] == x == mul[x][0] for x in R)
                assert all(any(mul[x][y] == 0 for y in R) for x in R)
                assert all(sorted(mul[x]) == list(R) for x in R)
                assert all(mul[mul[x][y]][z] == mul[x][mul[y][z]] for x in R for y in R for z in R)
                return m, gid, t[2], mul
    raise SystemExit("no such group")


def cnf(m, mul, anti=True):
    inv = [next(b for b in range(m) if mul[a][b] == 0) for a in range(m)]
    nv = 0

    def block():
        nonlocal nv
        base = nv
        nv += m * m
        return lambda i, j: base + i * m + j + 1

    F, U, R = block(), block(), block()
    cl = []
    for z in range(m):
        cl.append([F(z, v) for v in range(m)])
        cl.append([F(v, z) for v in range(m)])
        for v in range(m):
            for w in range(v + 1, m):
                cl.append([-F(z, v), -F(z, w)])
                cl.append([-F(v, z), -F(w, z)])
        if anti:
            cl.append([-F(z, z)])                  # no fixed point: E255 fails
    for x in range(m):
        xi = inv[x]
        for a in range(m):
            for b in range(m):                     # U(x,u) <- f(x)=a, f(a^-1)=b, u=ab
                cl.append([-F(x, a), -F(inv[a], b), U(x, mul[a][b])])
        for u in range(m):
            c = mul[xi][u]
            for d in range(m):
                xd = mul[x][d]
                cl.append([-U(x, u), -F(c, d), F(xd, x)])    # E677 at (x, e)
                cl.append([-U(x, u), -F(xd, x), F(c, d)])    # f injective
                cl.append([-F(c, d), -F(xd, x), R(x, u)])
        for a in range(m):
            ai = inv[a]
            for u in range(m):                     # f(x)=a, R(x,u) -> f(a^-1) = a^-1 u
                cl.append([-F(x, a), -R(x, u), F(ai, mul[ai][u])])
    if anti:
        for a in range(m):                         # 13.2(vii) at e: f(y f(e)) != y
            for y in range(m):
                cl.append([-F(0, a), -F(mul[y][a], y)])
        for z in range(m):                         # 13.2(v) at e: f(z f(z^-1)) != z
            for w in range(m):
                cl.append([-F(inv[z], w), -F(mul[z][w], z)])
    return nv, cl


if __name__ == "__main__":
    m, gid, desc, mul = read_group(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
    opts = sys.argv[4:]
    anti = "general" not in opts
    nv, cl = cnf(m, mul, anti)
    tag = ""
    if "fix" in opts:
        k = opts.index("fix")
        a, b = int(opts[k + 1]), int(opts[k + 2])
        cl += [[a + 1], [a * m + b + 1]]           # F(0,a), F(a,b)
        tag = " case f(e)=%d f(%d)=%d" % (a, a, b)
    out = sys.stdout
    out.write("c tinv E677 %s group SmallGroup(%d,%d) = %s%s\n" % ("anti255" if anti else "general", m, gid, desc, tag))
    out.write("p cnf %d %d\n" % (nv, len(cl)))
    out.write("".join(" ".join(map(str, c)) + " 0\n" for c in cl))
