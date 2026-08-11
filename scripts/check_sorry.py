#!/usr/bin/env python3
"""Ban sorry/admit/axiom/native_decide in our Lean sources (comments stripped).

Statements of open problems must be written as `def ... : Prop := ...`
(no proof term needed), so nothing in this library ever requires `sorry`.
`native_decide` is banned because it extends the trusted base to the compiler.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = "AgenticConjectures"
BANNED = re.compile(r"(?<![A-Za-z0-9_'])(sorry|admit|native_decide|axiom)(?![A-Za-z0-9_'])")


def strip_comments(src: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(src):
        two = src[i : i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = len(src) if j == -1 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def main() -> int:
    hits = []
    targets = [ROOT / f"{LIB}.lean", *sorted((ROOT / LIB).rglob("*.lean"))]
    for p in targets:
        if not p.exists():
            continue
        clean = strip_comments(p.read_text(encoding="utf-8"))
        for n, line in enumerate(clean.splitlines(), 1):
            m = BANNED.search(line)
            if m:
                hits.append((p.relative_to(ROOT), n, m.group(1)))
    if hits:
        print("Banned tokens found:")
        for path, n, tok in hits:
            print(f"  {path}:{n}: {tok}")
        return 1
    print(f"no-sorry gate OK: {len(targets)} file(s) clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
