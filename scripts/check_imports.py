#!/usr/bin/env python3
"""Every Lean module under AgenticConjectures/ must be reachable from the root
module AgenticConjectures.lean via imports, so `lake build` compiles all of it.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = "AgenticConjectures"
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.À-ჿFF]+)", re.MULTILINE)


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def main() -> int:
    files = {LIB: ROOT / f"{LIB}.lean"}
    for p in (ROOT / LIB).rglob("*.lean"):
        files[module_of(p)] = p

    imports = {
        mod: set(IMPORT_RE.findall(p.read_text(encoding="utf-8")))
        for mod, p in files.items()
    }

    reachable, frontier = {LIB}, [LIB]
    while frontier:
        for dep in imports.get(frontier.pop(), ()):
            if dep in files and dep not in reachable:
                reachable.add(dep)
                frontier.append(dep)

    unreachable = sorted(set(files) - reachable)
    if unreachable:
        print("Modules not imported (transitively) from the root module:")
        for m in unreachable:
            print(f"  {m}  ({files[m].relative_to(ROOT)})")
        print(f"\nAdd `import {unreachable[0]}` (etc.) to {LIB}.lean.")
        return 1
    print(f"import reachability OK: {len(files)} module(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
