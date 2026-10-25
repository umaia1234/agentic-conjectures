#!/usr/bin/env python3
"""Re-run the exhaustive difference-set searches (methods A and B) and check the results.

Usage:
  python3 verify_difference_sets.py controls   # prime-power controls, A vs B   (~10 s)
  python3 verify_difference_sets.py affine     # Z_143 relative case, A and B   (~10 s)
  python3 verify_difference_sets.py planar     # Z_157 planar case, method B    (~25 s)
  python3 verify_difference_sets.py planar-full  # Z_157, method A count profile (15-25 min)

Needs g++ (C++17).  Binaries go to ./build/.  Exit code 0 iff every check passes.
Expected solution counts for the controls are the numbers of normalised Singer
(planar, phi(v)/(3e)) and Bose (affine, phi(v)/(2e)) difference sets, q = p^e; the
other expected numbers are the recorded outputs of the runs documented in README.md.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BUILD = os.path.join(HERE, "build")
sys.path.insert(0, HERE)
import crosscheck_ab  # noqa: E402  (stdlib-only helper in this directory)

PLANAR_CONTROLS = {2: 2, 3: 4, 4: 2, 5: 10, 7: 12, 8: 8, 9: 12}
AFFINE_CONTROLS = {3: 2, 4: 2, 5: 4, 7: 8, 8: 6, 9: 8, 11: 16}
# method A: number of normalised sets of each size 2..k (Z_143 relative, Z_157 planar)
A_PROFILE_143 = [1, 118, 5854, 147630, 1830480, 9372616, 13930702, 3114022, 25068, 0, 0]
A_PROFILE_157 = [1, 152, 10804, 447580, 10951390, 143642744, 814387056, 1339150704,
                 301309320, 2052820, 0, 0]
B_NODES = {(143, 12, 13): 346794, (157, 13, 157): 21979581}


def build():
    os.makedirs(BUILD, exist_ok=True)
    for src, exe in (("ds_enumerate.cpp", "ds_enumerate"),
                     ("ds_search_normalized.cpp", "ds_search_normalized")):
        subprocess.run(["g++", "-O3", "-std=c++17", "-o", os.path.join(BUILD, exe),
                        os.path.join(HERE, src)], check=True)


def run(exe, v, k, m, tag):
    out = os.path.join(BUILD, f"{tag}_{exe}_{v}_{k}_{m}.out")
    with open(out, "w") as fh:
        subprocess.run([os.path.join(BUILD, exe), str(v), str(k), str(m)], stdout=fh,
                       check=True)
    with open(out) as fh:
        lines = fh.read().splitlines()
    return out, lines


def total(lines):
    tot = [l for l in lines if l.startswith("TOTAL")]
    return dict(kv.split("=") for kv in tot[0].split()[1:])


def check(cond, msg):
    print(("PASS " if cond else "FAIL ") + msg)
    return cond


def controls():
    ok = True
    for fam, table in (("planar", PLANAR_CONTROLS), ("affine", AFFINE_CONTROLS)):
        for q, expected in table.items():
            if fam == "planar":
                v, k, m = q * q + q + 1, q + 1, q * q + q + 1
            else:
                v, k, m = q * q - 1, q, q + 1
            a_out, a_lines = run("ds_enumerate", v, k, m, "ctl")
            b_out, _ = run("ds_search_normalized", v, k, m, "ctl")
            n_a = int(total(a_lines)["solutions"])
            ok &= check(n_a == expected, f"{fam} q={q}: method A finds {n_a} (expected "
                                         f"{expected})")
            rc = crosscheck_ab.compare(v, m, a_out, b_out)
            ok &= check(rc == 0, f"{fam} q={q}: method B = method A filtered by normal form")
    for q in (6, 10):  # orders with no plane at all: both searches must be empty
        for fam, (v, k, m) in (("planar", (q * q + q + 1, q + 1, q * q + q + 1)),
                               ("affine", (q * q - 1, q, q + 1))):
            for exe in ("ds_enumerate", "ds_search_normalized"):
                _, lines = run(exe, v, k, m, "ctl")
                ok &= check(total(lines)["solutions"] == "0",
                            f"{fam} q={q}: {exe} finds no solution")
    return ok


def profile(lines):
    return [int(l.split("sets=")[1]) for l in lines if l.startswith("COUNT")]


def main_case(v, k, m, with_a, a_profile):
    ok = True
    if with_a:
        _, lines = run("ds_enumerate", v, k, m, "main")
        ok &= check(total(lines)["solutions"] == "0", f"Z_{v}: method A finds no solution")
        ok &= check(profile(lines) == a_profile, f"Z_{v}: method A count profile matches")
    _, lines = run("ds_search_normalized", v, k, m, "main")
    t = total(lines)
    ok &= check(t["solutions"] == "0", f"Z_{v}: method B finds no solution")
    ok &= check(int(t["nodes"]) == B_NODES[(v, k, m)], f"Z_{v}: method B node count "
                                                       f"{t['nodes']} matches")
    return ok


def main():
    mode = sys.argv[1] if len(sys.argv) == 2 else ""
    if mode not in ("controls", "affine", "planar", "planar-full"):
        print(__doc__)
        return 2
    build()
    if mode == "controls":
        ok = controls()
    elif mode == "affine":
        ok = main_case(143, 12, 13, True, A_PROFILE_143)
    elif mode == "planar":
        ok = main_case(157, 13, 157, False, None)
    else:
        ok = main_case(157, 13, 157, True, A_PROFILE_157)
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
