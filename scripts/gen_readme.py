#!/usr/bin/env python3
"""Regenerate the problem dashboard in README.md from problems/*/status.yaml.

The table is written between the STATUS:BEGIN / STATUS:END markers; everything
else in README.md is left untouched. Run with --check to fail (exit 1) when the
committed README is stale (used by CI).
"""
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
BEGIN, END = "<!-- STATUS:BEGIN (scripts/gen_readme.py) -->", "<!-- STATUS:END -->"

BADGE = {"proved": "✅ proved", "refuted": "🔴 refuted", "partial": "🟡 partial", "open": "⚪ open"}
DOMAIN_ORDER = ["oeis", "erdos", "graph-combinatorics", "other"]
DOMAIN_TITLE = {
    "oeis": "OEIS", "erdos": "Erdős problems",
    "graph-combinatorics": "Graphs & combinatorics", "other": "Other",
}


def esc(s: str) -> str:
    """Escape characters that would break a markdown table cell."""
    return s.replace("|", "\\|").replace("\n", " ")


def checks_cell(status: dict) -> str:
    tags = []
    if (status.get("lean") or {}).get("theorems"):
        tags.append("lean")
    verifies = status.get("verify") or []
    if any(v.get("ci_feasible") for v in verifies):
        tags.append("cert")
    elif verifies:
        tags.append("cert(local)")
    return " + ".join(tags) if tags else "—"


def main() -> int:
    check = "--check" in sys.argv
    rows = {d: [] for d in DOMAIN_ORDER}
    counts = dict.fromkeys(BADGE, 0)
    for sf in sorted(ROOT.glob("problems/*/status.yaml")):
        with open(sf) as f:
            s = yaml.safe_load(f)
        st = s.get("claimed_status", "open")
        counts[st] = counts.get(st, 0) + 1
        d = s.get("domain") if s.get("domain") in rows else "other"
        rows[d].append(
            f"| [{esc(s.get('title', s['id']))}](problems/{s['id']}/README.md) "
            f"| {BADGE.get(st, st)} | {checks_cell(s)} | {esc(s.get('claim', ''))} |"
        )

    total = sum(counts.values())
    lines = [BEGIN, "",
             f"**{total} problems** — " + " · ".join(
                 f"{BADGE[k]}: {counts.get(k, 0)}" for k in BADGE), ""]
    for d in DOMAIN_ORDER:
        if not rows[d]:
            continue
        lines += [f"### {DOMAIN_TITLE[d]}", "",
                  "| Problem | Claimed status | Machine checks | Claim |",
                  "|---|---|---|---|", *rows[d], ""]
    lines.append(END)
    block = "\n".join(lines)

    text = README.read_text(encoding="utf-8")
    if BEGIN in text and END in text:
        head, rest = text.split(BEGIN, 1)
        _, tail = rest.split(END, 1)
        new = head + block + tail
    else:
        new = text.rstrip() + "\n\n## Dashboard\n\n" + block + "\n"

    if check:
        if new != text:
            print("README.md dashboard is stale; run scripts/gen_readme.py")
            return 1
        print("README dashboard up to date")
        return 0
    README.write_text(new, encoding="utf-8")
    print(f"README dashboard regenerated: {total} problems")
    return 0


if __name__ == "__main__":
    sys.exit(main())
