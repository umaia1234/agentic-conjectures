#!/usr/bin/env python3
"""Generate the weekly GitHub release tag, title, and notes.

Reads docs/highlights.yaml plus problems/*/status.yaml and writes three
files into the output directory (default build/release): tag.txt,
title.txt, and notes.md. The release job in .github/workflows/verify.yml
runs this after both verification jobs are green and creates or updates
the release for the newest curated week; agents never run release
commands by hand.
"""
import sys
from pathlib import Path

import gen_readme as gr

REPO_URL = "https://github.com/umaia1234/agentic-conjectures"
PAGES_URL = "https://umaia1234.github.io/agentic-conjectures/"


def main() -> int:
    outdir = Path(sys.argv[1] if len(sys.argv) > 1 else "build/release")
    statuses = gr.load_statuses()
    by_id = {s["id"]: s for s in statuses}
    weeks, errors = gr.load_highlights(by_id)
    if errors:
        print("invalid weekly highlights data:")
        for error in errors:
            print(f"  {error}")
        return 1

    week = weeks[-1]
    counts = dict.fromkeys(gr.BADGE["en"], 0)
    for s in statuses:
        st = s.get("claimed_status", "open")
        counts[st] = counts.get(st, 0) + 1
    total = sum(counts.values())

    tag = f"weekly-{week['week']}"
    title = (
        f"Week of {week['week']} — {total} problems: "
        f"{counts['proved']} proved · {counts['refuted']} refuted · "
        f"{counts['partial']} partial · {counts['open']} open"
    )

    curator = week["curator"]
    lines = [
        f"**Curated by `{curator['model']}` ({curator['harness']})** — each "
        "week a different model picks 2–3 CI-verified results; curation is "
        "commentary, never a claim upgrade "
        f"([how it works]({REPO_URL}/blob/main/AGENTS.md#iteration-pipeline) "
        f"· [weekly archive]({REPO_URL}/blob/main/docs/HIGHLIGHTS.md)).",
        "",
    ]
    for pick in week["picks"]:
        s = by_id[pick["problem"]]
        checks = gr.checks_cell(s, "en")
        tag_txt = f" `{checks}`" if checks != "—" else ""
        lines.append(
            f"- {gr.BADGE['en'][s['claimed_status']]} "
            f"[{s.get('title', s['id'])}]"
            f"({REPO_URL}/blob/main/problems/{s['id']}/README.md)"
            f"{tag_txt} — {pick['blurb']}"
        )
    lines += [
        "",
        f"**Dashboard at release time:** {total} problems — "
        + " · ".join(
            f"{gr.BADGE['en'][k]}: {counts[k]}" for k in gr.BADGE["en"]
        ),
        "",
        f"📊 [Live dashboard]({PAGES_URL}) · "
        f"🔁 Reproduce: `python3 scripts/verify_all.py --ci` — "
        "a claim CI does not verify is just a claim.",
    ]

    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "tag.txt").write_text(tag + "\n", encoding="utf-8")
    (outdir / "title.txt").write_text(title + "\n", encoding="utf-8")
    (outdir / "notes.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {outdir}/tag.txt, title.txt, notes.md ({tag})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
