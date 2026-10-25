#!/usr/bin/env python3
"""Check that AgenticConjectures/CatchUpGame.lean copies the upstream definitions verbatim.

The block from the `Player` docstring through the body of `value` must be byte-identical in the
upstream snapshot and in our module, and the snapshot must have the recorded SHA-256.
"""
import hashlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE / "upstream" / "CatchUpConjecture.lean"
MODULE = HERE.parent.parent / "AgenticConjectures" / "CatchUpGame.lean"
SHA256 = "53b9153986d279c1512993a9d3ffe80ff8c53233f59a82998dea36326e0f2790"
START = "/--\nAn arbitrary two elements type"
END = "  valueAux S 0 0 true\n"


def block(text, name):
    i = text.find(START)
    j = text.find(END, i)
    if i < 0 or j < 0 or text.count(START) != 1:
        sys.exit(f"FAIL: definition block not found exactly once in {name}")
    return text[i:j + len(END)]


def main():
    raw = UPSTREAM.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SHA256:
        print("FAIL: upstream snapshot SHA-256 changed")
        return 1
    up = block(raw.decode(), UPSTREAM.name)
    ours = block(MODULE.read_text(), MODULE.name)
    if up != ours:
        print("FAIL: the definitions in CatchUpGame.lean differ from the upstream snapshot")
        return 1
    print(f"PASS: {len(up.splitlines())} lines (Player .. value) identical to the upstream snapshot")
    return 0


if __name__ == "__main__":
    sys.exit(main())
