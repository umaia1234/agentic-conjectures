#!/usr/bin/env python3
"""CI-sized check for WOWII Graph Conjecture 61 (standard library + g++).

1. Compiles wowii61.cpp and runs it on EVERY labeled graph with n <= 7
   vertices (no nauty needed) with the brute-force crosscheck on: the
   numbers of connected labeled graphs must be OEIS A001187 and all
   violation / disagreement counters must be zero.
2. Runs the independent Python reference wowii61_ref.py on every labeled
   graph with n <= 6 and requires its summary to equal the C++ summary.
3. Checks the committed results of the local nauty runs
   (results/*.txt): graph counts are OEIS A001349 (connected graphs,
   n <= 11) and A000055 (trees, n <= 26, and the trees inside the sparse
   family, n = 12..20), histogram totals match the
   counts, no graph is disconnected, every violation counter is zero, the
   histograms themselves satisfy the conjecture and the PROOF.md bounds,
   the diameter-path family only has D >= n-5, and for n <= 7 the set of
   occurring (n, D, f-alpha, alpha-r) values equals the one found in the
   labeled enumeration of step 1 (every unlabeled graph is labeled).
"""

import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import wowii61_summary as ws  # noqa: E402

A001187 = [1, 1, 4, 38, 728, 26704, 1866256]                      # n = 1..7
A001349 = [1, 1, 2, 6, 21, 112, 853, 11117, 261080, 11716571,
           1006700565]                                            # n = 1..11
A000055 = [1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301, 3159, 7741,
           19320, 48629, 123867, 317955, 823065, 2144505, 5623756,
           14828074, 39299897, 104636890, 279793450]              # n = 1..26
VIOLATIONS = ["conj", "thm1", "thm2a", "thm2b", "fms", "hh", "tree_f"]
CROSS = ["xf", "xa", "xd", "xr"]

failures = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failures.append(msg)


def summary_from_text(text):
    s = ws.Summary()
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write(text)
    try:
        s.read(fh.name)
    finally:
        os.unlink(fh.name)
    return s


def support(s, n):
    return {k[1:] for k in s.hist if k[0] == n}


def histogram_ok(s):
    """Re-check the inequalities on the histogram (n, D, f-alpha, alpha-r)."""
    cd = ws.ceil_div
    return all(fa + ar >= cd(D, 3) and fa >= cd(D, 4) and ar >= 0 and
               (n < 2 or fa >= 1) and (fa != 1 or D <= 4)
               for (n, D, fa, ar) in s.hist)


def main():
    cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("c++")
    tmp = tempfile.mkdtemp()
    exe = os.path.join(tmp, "wowii61")
    subprocess.run([cxx, "-O2", "-std=c++17", os.path.join(HERE, "wowii61.cpp"),
                    "-o", exe], check=True)

    labeled = {}
    for n in range(1, 8):
        out = subprocess.run([exe, "--labeled", str(n), "--crosscheck"],
                             check=True, capture_output=True, text=True).stdout
        s = summary_from_text(out)
        labeled[n] = (out, s)
        check(s.count.get(n) == A001187[n - 1] and s.graphs == 2 ** (n * (n - 1) // 2),
              "labeled n=%d: %d connected labeled graphs (A001187)" % (n, s.count.get(n, 0)))
        bad = {c: v for c, v in s.checks[n].items() if v}
        check(not bad, "labeled n=%d: no violation, crosscheck agrees %s" % (n, bad or ""))

    for n in range(1, 7):
        ref = subprocess.run([sys.executable, os.path.join(HERE, "wowii61_ref.py"),
                              "--labeled", str(n)],
                             check=True, capture_output=True, text=True).stdout
        strip = lambda t: [ln for ln in t.splitlines() if not ln.startswith("CROSSCHECK")]
        check(strip(ref) == strip(labeled[n][0]),
              "labeled n=%d: Python reference summary identical to C++" % n)

    res = os.path.join(HERE, "results")
    conn = ws.Summary()
    for name in ("connected_n1-10.txt", "connected_n11.txt"):
        conn.read(os.path.join(res, name))
    check([conn.count.get(n) for n in range(1, 12)] == A001349,
          "results: connected graph counts n=1..11 equal A001349")
    trees = ws.Summary()
    trees.read(os.path.join(res, "trees_n1-26.txt"))
    check([trees.count.get(n) for n in range(1, 27)] == A000055 and
          [trees.trees.get(n) for n in range(1, 27)] == A000055,
          "results: tree counts n=1..26 equal A000055")
    check([conn.trees.get(n) for n in range(1, 12)] == A000055[:11],
          "results: trees among connected graphs n=1..11 equal A000055")
    sparse = ws.Summary()
    sparse.read(os.path.join(res, "sparse.txt"))
    check(sorted(sparse.count) == list(range(12, 21)) and
          [sparse.trees.get(n) for n in range(12, 21)] == A000055[11:20],
          "results/sparse: n=12..20, trees among them equal A000055")
    diampath = ws.Summary()
    diampath.read(os.path.join(res, "diampath_n12-18.txt"))
    check(sorted(diampath.count) == list(range(12, 19)) and
          all(D >= n - 5 for (n, D, _, _) in diampath.hist),
          "results/diampath: n=12..18, every graph has diameter D >= n-5")
    for label, s in (("connected", conn), ("trees", trees), ("sparse", sparse),
                     ("diampath", diampath)):
        totals_ok = all(sum(c for k, c in s.hist.items() if k[0] == n) == s.count[n]
                        for n in s.count)
        check(totals_ok and s.graphs == sum(s.count.values()) and s.disconnected == 0,
              "results/%s: %d connected graphs, histogram totals equal graph counts"
              % (label, s.graphs))
        check(histogram_ok(s), "results/%s: histogram satisfies f >= r + ceil(D/3), "
              "f >= alpha + ceil(D/4), r <= alpha, (5), (6)" % label)
        bad = sorted((n, c) for n in s.checks for c in VIOLATIONS + CROSS
                     if s.checks[n][c])
        check(not bad, "results/%s: all violation/crosscheck counters zero" % label)
    for n in range(1, 8):
        check(support(conn, n) == support(labeled[n][1], n),
              "n=%d: (D, f-alpha, alpha-r) values of the nauty run equal the "
              "labeled enumeration" % n)
    shutil.rmtree(tmp)
    print("FAILED: %d check(s)" % len(failures) if failures else "all checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
