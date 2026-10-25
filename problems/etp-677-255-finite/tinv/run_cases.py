#!/usr/bin/env python3
"""Run the symmetry-breaking cases of the translation-invariant search with
CaDiCaL.  Appends one line per case to the log:
  m i a b | UNSAT|SAT|UNKNOWN | seconds
and a MODEL line (checked by brute force) for SAT cases.  Cases already in
the log are skipped, so the run can be resumed.  The number of parallel
solvers is re-read from <workers file> before each launch.
usage: run_cases.py <groups file> <cases file> <time limit> <log> <workers file>"""
import os
import subprocess
import sys
import tempfile
import time
from tinv_cnf import cnf, read_group

gpath, cpath, tl, logp, wpath = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
tmp = tempfile.mkdtemp(prefix="tinv_cases_")
done = set()
if os.path.exists(logp):
    for line in open(logp):
        if "|" in line:
            done.add(tuple(map(int, line.split("|")[0].split())))
cases = [tuple(map(int, l.split())) for l in open(cpath) if l.strip()]
cases = [c for c in cases if c not in done]
groups = {}
base = {}
log = open(logp, "a")


def workers():
    try:
        return int(open(wpath).read().strip())
    except (OSError, ValueError):
        return 1


def launch(case):
    m, i, a, b = case
    if (m, i) not in groups:
        groups[(m, i)] = read_group(gpath, m, i)
    if (m, i) not in base:
        nv, cl = cnf(m, groups[(m, i)][3], True)
        base.clear()                               # cases of a group are contiguous
        base[(m, i)] = (nv, len(cl), "".join(" ".join(map(str, c)) + " 0\n" for c in cl))
    nv, ncl, text = base[(m, i)]
    fn = os.path.join(tmp, "%d_%d_%d_%d.cnf" % case)
    with open(fn, "w") as fh:
        fh.write("p cnf %d %d\n" % (nv, ncl + 2))
        fh.write(text)
        fh.write("%d 0\n%d 0\n" % (a + 1, a * m + b + 1))
    out = open(fn + ".out", "w")
    p = subprocess.Popen(["cadical", "-q", "-t", str(tl), fn], stdout=out)
    return p, fn, out, time.time()


def finish(case, p, fn, out, t0):
    out.close()
    t = time.time() - t0
    st = {10: "SAT", 20: "UNSAT"}.get(p.returncode, "UNKNOWN")
    log.write("%d %d %d %d | %s | %.2fs\n" % (case + (st, t)))
    if st == "SAT":
        m, i, a, b = case
        _, _, desc, mul = groups[(m, i)]
        lits = [int(x) for l in open(fn + ".out") if l.startswith("v") for x in l.split()[1:]]
        f = [v for z in range(m) for v in range(m) if (z * m + v + 1) in lits]
        inv = [mul[x].index(0) for x in range(m)]
        T = [[mul[x][f[mul[inv[x]][y]]] for y in range(m)] for x in range(m)]
        ok = all(T[y][T[x][T[T[y][x]][y]]] == x for x in range(m) for y in range(m))
        non255 = sum(T[T[T[x][x]][x]][x] != x for x in range(m))
        log.write("MODEL %d %d f %s E677 %s non255 %d\n" % (m, i, " ".join(map(str, f)), ok, non255))
    log.flush()
    os.remove(fn)
    os.remove(fn + ".out")


running = []
while cases or running:
    for r in running[:]:
        if r[1].poll() is not None:
            running.remove(r)
            finish(r[0], *r[1:])
    while cases and len(running) < workers():
        c = cases.pop(0)
        running.append((c,) + launch(c))
    time.sleep(0.05)
os.rmdir(tmp)
