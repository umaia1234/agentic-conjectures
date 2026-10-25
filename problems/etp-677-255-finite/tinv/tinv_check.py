#!/usr/bin/env python3
"""Independent brute-force check of a translation-invariant magma
x<>y = x*f(x^-1 y): builds the full table and tests E677 and E255 directly.
usage: tinv_check.py <groups file> <order> <id> f0 f1 ... f(m-1)"""
import sys
from tinv_cnf import read_group

m, gid, desc, mul = read_group(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
f = list(map(int, sys.argv[4:]))
assert sorted(f) == list(range(m))
inv = [next(b for b in range(m) if mul[a][b] == 0) for a in range(m)]
T = [[mul[x][f[mul[inv[x]][y]]] for y in range(m)] for x in range(m)]
e677 = all(T[y][T[x][T[T[y][x]][y]]] == x for x in range(m) for y in range(m))
bad255 = [x for x in range(m) if T[T[T[x][x]][x]][x] != x]
print("group", m, gid, desc, "E677", e677, "non255", len(bad255))
