#!/usr/bin/env python3
"""Merge and tabulate summaries written by wowii61.cpp / wowii61_ref.py.

  python3 wowii61_summary.py merge PART... > merged.txt
  python3 wowii61_summary.py report SUMMARY...
  python3 wowii61_summary.py ndcount SUMMARY...     lines "n D #graphs"

`merge` adds counts and histograms and keeps, for every (n, D), the K
lexicographically smallest graph6 strings at the minimum value (K = 5).
`report` prints Markdown tables: per n, per diameter, and for the residual
diameters 4, 7, 8, >= 10 that PROOF.md does not cover.  slack means
f - r - ceil(D/3); "f-alpha < ceil(D/3)" counts the graphs for which the
stronger inequality f >= alpha + ceil(D/3) fails, so that the conjecture
needs r < alpha there.
Standard library only.
"""

import sys

K = 5
CHECKS = ["conj", "thm1", "thm2a", "thm2b", "fms", "hh", "tree_f",
          "xf", "xa", "xd", "xr"]


def ceil_div(a, b):
    return -(-a // b)


class Summary:
    def __init__(self):
        self.crosscheck = None
        self.graphs = 0
        self.disconnected = 0
        self.count = {}
        self.trees = {}
        self.hist = {}
        self.checks = {}
        self.ex = {"EX_SLACK": {}, "EX_FA": {}}
        self.xc = {}  # n -> crosscheck was on in every file containing n

    @staticmethod
    def _add(d, k, v):
        d[k] = d.get(k, 0) + v

    def read(self, path):
        with open(path) as fh:
            lines = fh.read().split("\n")
        if lines[0] != "WOWII61-SUMMARY v1":
            raise SystemExit("%s: not a WOWII61 summary" % path)
        flag = "CROSSCHECK 1" in lines
        for line in lines:
            if line.startswith("N "):
                n = int(line.split()[1])
                self.xc[n] = self.xc.get(n, True) and flag
        for line in lines[1:]:
            p = line.split()
            if not p:
                continue
            tag = p[0]
            if tag == "CROSSCHECK":
                c = p[1] == "1"
                self.crosscheck = c if self.crosscheck is None else self.crosscheck and c
            elif tag == "GRAPHS":
                self.graphs += int(p[1])
            elif tag == "DISCONNECTED":
                self.disconnected += int(p[1])
            elif tag == "N":
                self._add(self.count, int(p[1]), int(p[2]))
            elif tag == "TREES":
                self._add(self.trees, int(p[1]), int(p[2]))
            elif tag == "H":
                self._add(self.hist, tuple(int(x) for x in p[1:5]), int(p[5]))
            elif tag == "CHECK":
                ck = self.checks.setdefault(int(p[1]), dict.fromkeys(CHECKS, 0))
                ck[p[2]] += int(p[3])
            elif tag in self.ex:
                key, val = (int(p[1]), int(p[2])), int(p[3])
                cur = self.ex[tag].get(key)
                if cur is None or val < cur[0]:
                    self.ex[tag][key] = [val, {p[4]}]
                elif val == cur[0]:
                    cur[1].add(p[4])
            else:
                raise SystemExit("%s: unknown line %r" % (path, line))

    def lines(self):
        out = ["WOWII61-SUMMARY v1", "CROSSCHECK %d" % bool(self.crosscheck),
               "GRAPHS %d" % self.graphs, "DISCONNECTED %d" % self.disconnected]
        out += ["N %d %d" % kv for kv in sorted(self.count.items())]
        out += ["TREES %d %d" % kv for kv in sorted(self.trees.items())]
        out += ["H %d %d %d %d %d" % (k + (c,)) for k, c in sorted(self.hist.items())]
        for n in sorted(self.checks):
            out += ["CHECK %d %s %d" % (n, c, self.checks[n][c]) for c in CHECKS]
        for tag in ("EX_SLACK", "EX_FA"):
            for (n, D), (val, g6s) in sorted(self.ex[tag].items()):
                out += ["%s %d %d %d %s" % (tag, n, D, val, s) for s in sorted(g6s)[:K]]
        return out

    # ------------------------------------------------------------ derived
    def stats(self, pred):
        """Aggregate the histogram over the (n, D) accepted by `pred`."""
        st = {"graphs": 0, "min_slack": None, "at_min": 0, "min_fa": None,
              "alpha_fails": 0, "min_slack_alpha_fails": None}
        for (n, D, fa, ar), c in self.hist.items():
            if not pred(n, D):
                continue
            st["graphs"] += c
            s = fa + ar - ceil_div(D, 3)
            if st["min_slack"] is None or s < st["min_slack"]:
                st["min_slack"], st["at_min"] = s, 0
            if s == st["min_slack"]:
                st["at_min"] += c
            if st["min_fa"] is None or fa < st["min_fa"]:
                st["min_fa"] = fa
            if fa < ceil_div(D, 3):  # f >= alpha + ceil(D/3) fails
                st["alpha_fails"] += c
                m = st["min_slack_alpha_fails"]
                st["min_slack_alpha_fails"] = s if m is None else min(m, s)
        return st

    def example(self, pred):
        """Smallest graph6 at the minimum slack among the (n, D) accepted."""
        cands = [(val, g6) for (n, D), (val, g6s) in self.ex["EX_SLACK"].items()
                 if pred(n, D) for g6 in g6s]
        return min(cands)[1] if cands else "-"


def fmt(v):
    return "-" if v is None else str(v)


def code(g6):
    """Markdown code span (graph6 strings may contain backticks)."""
    return "`` %s ``" % g6 if "`" in g6 else "`%s`" % g6


RESIDUAL = [("4", lambda D: D == 4), ("7", lambda D: D == 7), ("8", lambda D: D == 8),
            (">= 10", lambda D: D >= 10)]


def report(s):
    print("| n | graphs | trees | min slack | graphs at min | max D | violations | crosscheck |")
    print("|---|---|---|---|---|---|---|---|")
    for n in sorted(s.count):
        ck = s.checks[n]
        viol = sum(ck[c] for c in CHECKS[:7])
        xm = sum(ck[c] for c in CHECKS[7:]) if s.xc.get(n) else None
        st = s.stats(lambda m, D: m == n)
        maxd = max(D for (m, D, _, _) in s.hist if m == n)
        print("| %d | %d | %d | %s | %d | %d | %d | %s |" % (
            n, s.count[n], s.trees.get(n, 0), fmt(st["min_slack"]), st["at_min"], maxd,
            viol, "not run" if xm is None else "%d mismatches" % xm))
    print()
    print("| D | graphs | min slack | graphs at min | min f-alpha | ceil(D/4) | ceil(D/3) "
          "| graphs with f-alpha < ceil(D/3) | min slack among them |")
    print("|---|---|---|---|---|---|---|---|---|")
    for D in sorted({D for (_, D, _, _) in s.hist}):
        st = s.stats(lambda m, E: E == D)
        print("| %d | %d | %s | %d | %s | %d | %d | %d | %s |" % (
            D, st["graphs"], fmt(st["min_slack"]), st["at_min"], fmt(st["min_fa"]),
            ceil_div(D, 4), ceil_div(D, 3), st["alpha_fails"],
            fmt(st["min_slack_alpha_fails"])))
    print()
    print("| residual D | graphs | min slack | graphs at min | graphs with f-alpha < ceil(D/3) "
          "| smallest graph6 at min slack |")
    print("|---|---|---|---|---|---|")
    for label, dpred in RESIDUAL:
        st = s.stats(lambda m, D: dpred(D))
        if st["graphs"]:
            print("| %s | %d | %s | %d | %d | %s |" % (
                label, st["graphs"], fmt(st["min_slack"]), st["at_min"], st["alpha_fails"],
                code(s.example(lambda m, D: dpred(D)))))


def main(argv):
    if len(argv) >= 2 and argv[0] == "merge":
        s = Summary()
        for p in argv[1:]:
            s.read(p)
        print("\n".join(s.lines()))
        return 0
    if len(argv) >= 2 and argv[0] == "report":
        s = Summary()
        for p in argv[1:]:
            s.read(p)
        report(s)
        return 0
    if len(argv) >= 2 and argv[0] == "ndcount":
        s = Summary()
        for p in argv[1:]:
            s.read(p)
        nd = {}
        for (n, D, _, _), c in s.hist.items():
            nd[(n, D)] = nd.get((n, D), 0) + c
        for (n, D), c in sorted(nd.items()):
            print(n, D, c)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
