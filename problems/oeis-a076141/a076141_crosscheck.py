#!/usr/bin/env python3
"""Cross-checks for the A076141 single-occurrence enumerators.

--smoke LMAX   compile a076141_occ_closed.cpp (P), a076141_occ_hensel.cpp (Q) and
               a076141_bruteforce_odd.cpp (BF) with g++, run them for bit lengths
               3..LMAX, and require
                 * exit status 0 everywhere (no counterexample);
                 * the OCC lists of P (both and full) and Q (full) equal BF's list;
                 * the OCC lists of P and Q in reduced mode equal BF's list
                   restricted to the reduced positions;
                 * identical per-L summary lines (including candidate counts)
                   for P and Q in full and in reduced mode.
--logs FILE..  check committed run logs of P, Q and BF: every log ends with
               exit status 0 and counterexamples=0, its recorded occ_sha256
               matches its OCC lines, P and Q logs of the same mode have
               identical per-L lines and OCC lines, the bit lengths are covered
               without gaps, reduced-mode lists equal the full-mode lists
               restricted to the reduced positions where both exist, and a
               brute-force log equals the full-mode lists on its range.
"""

import hashlib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCES = {
    "P": "a076141_occ_closed.cpp",
    "Q": "a076141_occ_hensel.cpp",
    "BF": "a076141_bruteforce_odd.cpp",
}


def reduced_position(L, t):
    """Positions searched in reduced mode (Lean: OeisA076141.SearchedPos)."""
    sigma = L // 3 + 1
    return (3 <= t <= sigma) or (2 * sigma + 2 <= t and L + sigma + 1 <= 2 * t and t < L)


def occ_lines(text):
    return [ln for ln in text.splitlines() if ln.startswith("OCC ")]


def per_l_lines(text):
    return [ln for ln in text.splitlines() if ln.startswith("L=")]


def restrict(lines):
    out = []
    for ln in lines:
        _, L, t, _, _ = ln.split()
        if reduced_position(int(L), int(t)):
            out.append(ln)
    return out


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        fail(f"{' '.join(cmd)} exited with {r.returncode}: {r.stderr.strip()}")
    return r.stdout


def smoke(lmax, threads="2"):
    with tempfile.TemporaryDirectory() as tmp:
        exe = {}
        for key, src in SOURCES.items():
            exe[key] = os.path.join(tmp, key)
            subprocess.run(["g++", "-O3", "-std=c++20", "-o", exe[key],
                            os.path.join(HERE, src)], check=True)
        lo, hi = "3", str(lmax)
        bf = occ_lines(run([exe["BF"], lo, hi, threads]))
        p_both = run([exe["P"], lo, hi, "both", threads])
        p_full = run([exe["P"], lo, hi, "full", threads])
        q_full = run([exe["Q"], lo, hi, "full", threads])
        p_red = run([exe["P"], lo, hi, "reduced", threads])
        q_red = run([exe["Q"], lo, hi, "reduced", threads])
    for name, out in (("P both", p_both), ("P full", p_full), ("Q full", q_full)):
        if occ_lines(out) != bf:
            fail(f"{name} OCC list differs from brute force")
    for name, out in (("P reduced", p_red), ("Q reduced", q_red)):
        if occ_lines(out) != restrict(bf):
            fail(f"{name} OCC list differs from restricted brute force")
    if per_l_lines(p_full) != per_l_lines(q_full):
        fail("P/Q full-mode per-L lines differ")
    if per_l_lines(p_red) != per_l_lines(q_red):
        fail("P/Q reduced-mode per-L lines differ")
    print(f"OK smoke L=3..{lmax}: {len(bf)} occurrences, brute force = P = Q, "
          f"{len(restrict(bf))} at reduced positions, candidate counts agree")


def parse_log(path):
    text = open(path).read()
    meta = dict(re.findall(r"^# (\w+): (.*)$", text, re.M))
    cmd = meta.get("cmd", "")
    m = re.search(r"\./(a076141_\w+) (\d+) (\d+) (\w+)", cmd)
    if not m:
        fail(f"{path}: no command line")
    prog, lmin, lmax, mode = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
    if prog == "a076141_bruteforce_odd":
        mode = "brute"
    if meta.get("exit_status") != "0":
        fail(f"{path}: exit status {meta.get('exit_status')}")
    if not re.search(r"^SUMMARY .* counterexamples=0( position_check=ok)?$", text, re.M):
        fail(f"{path}: SUMMARY line missing or counterexamples != 0")
    occ = occ_lines(text)
    digest = hashlib.sha256("".join(ln + "\n" for ln in occ).encode()).hexdigest()
    if digest != meta.get("occ_sha256"):
        fail(f"{path}: occ_sha256 mismatch")
    lines = per_l_lines(text)
    ls = [int(ln.split()[0][2:]) for ln in lines]
    if ls != list(range(lmin, lmax + 1)):
        fail(f"{path}: per-L lines do not cover {lmin}..{lmax}")
    return prog, mode, lmin, lmax, lines, occ


def check_logs(paths):
    by_key, brute = {}, []
    for path in paths:
        prog, mode, lmin, lmax, lines, occ = parse_log(path)
        if mode == "brute":
            brute.append((lmin, lmax, occ))
            continue
        by_key.setdefault((mode, lmin, lmax), {})[prog] = (lines, occ)
    cover = {}
    for (mode, lmin, lmax), progs in sorted(by_key.items()):
        if set(progs) != {"a076141_occ_closed", "a076141_occ_hensel"}:
            fail(f"{mode} L={lmin}..{lmax}: need one log of each enumerator")
        (lp, op), (lq, oq) = progs["a076141_occ_closed"], progs["a076141_occ_hensel"]
        if lp != lq:
            fail(f"{mode} L={lmin}..{lmax}: per-L lines differ")
        if op != oq:
            fail(f"{mode} L={lmin}..{lmax}: OCC lists differ")
        cover.setdefault(mode, []).append((lmin, lmax, op))
        print(f"OK {mode} L={lmin}..{lmax}: P and Q agree on {len(lp)} per-L lines "
              f"and {len(op)} occurrences")
    occ_by_mode = {}
    for mode, segs in cover.items():
        segs.sort()
        for (a0, b0, _), (a1, _, _) in zip(segs, segs[1:]):
            if a1 != b0 + 1:
                fail(f"{mode}: gap or overlap between segments at L={b0}")
        occ_by_mode[mode] = (segs[0][0], segs[-1][1], [ln for s in segs for ln in s[2]])
        print(f"OK {mode}: L={segs[0][0]}..{segs[-1][1]} covered without gaps")
    if "full" in occ_by_mode and "reduced" in occ_by_mode:
        f0, f1, focc = occ_by_mode["full"]
        r0, r1, rocc = occ_by_mode["reduced"]
        lo, hi = max(f0, r0), min(f1, r1)
        within = lambda lines: [ln for ln in lines if lo <= int(ln.split()[1]) <= hi]
        if within(restrict(focc)) != within(rocc):
            fail("reduced-mode lists differ from restricted full-mode lists")
        print(f"OK reduced = restricted full on L={lo}..{hi}")
    for lmin, lmax, occ in brute:
        if "full" not in occ_by_mode:
            fail("a brute-force log needs the full-mode logs")
        f0, f1, focc = occ_by_mode["full"]
        if not (f0 <= lmin and lmax <= f1):
            fail(f"brute force L={lmin}..{lmax} is not inside the full-mode range")
        if [ln for ln in focc if lmin <= int(ln.split()[1]) <= lmax] != occ:
            fail(f"full-mode lists differ from brute force on L={lmin}..{lmax}")
        print(f"OK brute force L={lmin}..{lmax}: {len(occ)} occurrences, equal to full mode")


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "--smoke":
        smoke(int(sys.argv[2]))
    elif len(sys.argv) >= 3 and sys.argv[1] == "--logs":
        check_logs(sys.argv[2:])
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
