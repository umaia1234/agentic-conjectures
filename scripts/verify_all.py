#!/usr/bin/env python3
"""Re-run every machine-checkable certificate declared in problems/*/status.yaml.

Usage:
  python3 scripts/verify_all.py            # run everything (local, no time limit skip)
  python3 scripts/verify_all.py --ci       # run only checks marked ci_feasible: true
  python3 scripts/verify_all.py --only oeis-a067720
  python3 scripts/verify_all.py --list     # show what would run

Exit code 0 iff every executed check passed. A problem with no verify entries
is reported as SKIP (that is allowed; the dashboard shows it as unverified).
"""
import argparse
import shutil
import subprocess
import sys
import time
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PROBLEMS = ROOT / "problems"
CI_TIMEOUT = 180  # seconds per command in --ci mode


def load_status_files(only: str | None):
    for d in sorted(PROBLEMS.iterdir()):
        if not d.is_dir() or (only and d.name != only):
            continue
        sf = d / "status.yaml"
        if sf.exists():
            with open(sf) as f:
                yield d, yaml.safe_load(f)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ci", action="store_true", help="only ci_feasible checks, with timeout")
    ap.add_argument("--only", metavar="ID", help="run a single problem directory")
    ap.add_argument("--list", action="store_true", help="list checks without running")
    args = ap.parse_args()

    ran, passed, failed, skipped = 0, [], [], []
    for pdir, status in load_status_files(args.only):
        checks = status.get("verify") or []
        if args.ci:
            checks = [c for c in checks if c.get("ci_feasible")]
        if not checks:
            skipped.append(pdir.name)
            continue
        for c in checks:
            cmd = c["cmd"]
            missing = [t for t in (c.get("requires") or []) if shutil.which(t) is None]
            if missing:
                print(f"FAIL {pdir.name}: missing required tools {missing} for: {cmd}")
                failed.append((pdir.name, cmd, "missing tools"))
                continue
            if args.list:
                print(f"{pdir.name}: {cmd}")
                continue
            ran += 1
            t0 = time.time()
            try:
                r = subprocess.run(
                    cmd, shell=True, cwd=pdir, capture_output=True, text=True,
                    timeout=CI_TIMEOUT if args.ci else None,
                )
            except subprocess.TimeoutExpired:
                print(f"FAIL {pdir.name} ({CI_TIMEOUT}s timeout): {cmd}")
                failed.append((pdir.name, cmd, "timeout"))
                continue
            dt = time.time() - t0
            if r.returncode == 0:
                print(f"PASS {pdir.name} ({dt:.1f}s): {cmd}")
                passed.append((pdir.name, cmd))
            else:
                tail = (r.stdout + r.stderr).strip().splitlines()[-8:]
                print(f"FAIL {pdir.name} (exit {r.returncode}): {cmd}")
                for line in tail:
                    print(f"     | {line}")
                failed.append((pdir.name, cmd, f"exit {r.returncode}"))

    print(f"\n{len(passed)} passed, {len(failed)} failed, "
          f"{len(skipped)} problems with no runnable checks{' (ci mode)' if args.ci else ''}")
    if failed:
        for name, cmd, why in failed:
            print(f"  FAILED {name}: {cmd} [{why}]")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
