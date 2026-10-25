#!/usr/bin/env python3
"""For every theorem listed under `lean.theorems` in problems/*/status.yaml,
run `#print axioms` and require that only the three standard axioms appear
(propext, Classical.choice, Quot.sound). Catches sorryAx and ofReduceBool
even if source-level greps are evaded. Requires a completed `lake build`.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS_RE = re.compile(
    r"^'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M
)


def main() -> int:
    modules, theorems = set(), []
    for sf in sorted(ROOT.glob("problems/*/status.yaml")):
        with open(sf) as f:
            status = yaml.safe_load(f) or {}
        lean = status.get("lean") or {}
        modules.update(lean.get("modules") or [])
        theorems.extend(lean.get("theorems") or [])

    if not theorems:
        print("axiom check: no Lean theorems declared in status files yet")
        return 0

    src = "".join(f"import {m}\n" for m in sorted(modules))
    src += "".join(f"#print axioms {t}\n" for t in theorems)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(src)
        scratch = Path(f.name)
    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(scratch)],
            cwd=ROOT, capture_output=True, text=True, timeout=600,
        )
    finally:
        scratch.unlink()

    if r.returncode != 0:
        print("axiom check: lean failed on the generated file:")
        print(r.stdout + r.stderr)
        return 1

    # "'thm' depends on axioms: [a, b]" / "'thm' does not depend on any axioms".
    # Lean wraps long axiom lists over several lines, so parse the whole output.
    found = {}
    for m in AXIOMS_RE.finditer(r.stdout):
        found[m.group(1)] = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    bad = False
    missing = [t for t in theorems if t not in found]
    if missing:
        print(f"axiom check: no #print axioms output parsed for {missing}")
        bad = True
    for name, axioms in found.items():
        extra = axioms - ALLOWED
        if extra:
            print(f"DISALLOWED axioms in {name}: {sorted(extra)}")
            bad = True
    if bad:
        return 1
    print(f"axiom check OK: {len(theorems)} theorem(s), standard axioms only")
    return 0


if __name__ == "__main__":
    sys.exit(main())
