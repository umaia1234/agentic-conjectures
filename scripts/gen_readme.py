#!/usr/bin/env python3
"""Regenerate localized problem indexes from problems/*/status.yaml.

Generated blocks in the root landing pages and documentation index are updated;
everything outside their markers is left untouched. Run with --check to fail
(exit 1) when any committed index is stale (used by CI).
"""
import sys
from pathlib import Path
from urllib.parse import quote

import yaml

ROOT = Path(__file__).resolve().parent.parent
READMES = [(ROOT / "README.md", "en"), (ROOT / "README.ko.md", "ko")]
DOC_READMES = [
    (ROOT / "docs" / "README.md", "en"),
    (ROOT / "docs" / "README.ko.md", "ko"),
]
BEGIN, END = "<!-- STATUS:BEGIN (scripts/gen_readme.py) -->", "<!-- STATUS:END -->"
CBEGIN, CEND = "<!-- COUNTS:BEGIN (scripts/gen_readme.py) -->", "<!-- COUNTS:END -->"
DBEGIN = "<!-- DETAILS:BEGIN (scripts/gen_readme.py) -->"
DEND = "<!-- DETAILS:END -->"
SHIELD = "https://img.shields.io/badge"
DOMAIN_ORDER = ["oeis", "erdos", "graph-combinatorics", "other"]
COUNT_STYLE = {
    "en": [
        (None, "problems", "8250df"),
        ("proved", "proved", "2da44e"),
        ("refuted", "refuted", "cf222e"),
        ("partial", "partial", "bf8700"),
        ("open", "open", "848d97"),
    ],
    "ko": [
        (None, "문제", "8250df"),
        ("proved", "증명", "2da44e"),
        ("refuted", "반례", "cf222e"),
        ("partial", "부분 결과", "bf8700"),
        ("open", "미해결", "848d97"),
    ],
}
BADGE = {
    "en": {
        "proved": "✅ proved", "refuted": "🔴 refuted",
        "partial": "🟡 partial", "open": "⚪ open",
    },
    "ko": {
        "proved": "✅ 증명", "refuted": "🔴 반례",
        "partial": "🟡 부분 결과", "open": "⚪ 미해결",
    },
}
DOMAIN_TITLE = {
    "en": {
        "oeis": "OEIS", "erdos": "Erdős problems",
        "graph-combinatorics": "Graphs & combinatorics", "other": "Other",
    },
    "ko": {
        "oeis": "OEIS", "erdos": "에르되시 문제",
        "graph-combinatorics": "그래프·조합론", "other": "기타",
    },
}
TABLE_HEADER = {
    "en": "| Problem | Claimed status | Machine checks | Solved by | Claim |",
    "ko": "| 문제 | 주장 상태 | 기계 검증 | 작업 모델 | 주장 |",
}
CHECK_LABEL = {
    "en": {"lean": "lean", "cert": "cert", "cert_local": "cert(local)"},
    "ko": {"lean": "Lean", "cert": "인증서", "cert_local": "인증서(로컬)"},
}


def esc(s: str) -> str:
    """Escape characters that would break a markdown table cell."""
    return s.replace("|", "\\|").replace("\n", " ")


def checks_cell(status: dict, locale: str) -> str:
    tags = []
    if (status.get("lean") or {}).get("theorems"):
        tags.append(CHECK_LABEL[locale]["lean"])
    verifies = status.get("verify") or []
    if any(v.get("ci_feasible") for v in verifies):
        tags.append(CHECK_LABEL[locale]["cert"])
    elif verifies:
        tags.append(CHECK_LABEL[locale]["cert_local"])
    return " + ".join(tags) if tags else "—"


def solved_by_cell(status: dict) -> str:
    models = []
    for a in status.get("attribution") or []:
        m = a.get("model")
        if m and m not in models:
            models.append(m)
    return " · ".join(f"`{m}`" for m in models) if models else "—"


def localized_problem_file(status: dict, filename: str, locale: str) -> str:
    """Return a Korean companion when it exists, otherwise the English file."""
    if locale == "ko":
        path = Path(filename)
        korean = path.with_name(f"{path.stem}.ko{path.suffix}")
        if (ROOT / "problems" / status["id"] / korean).exists():
            return korean.as_posix()
    return filename


def dashboard_blocks(statuses: list[dict], locale: str) -> tuple[str, str]:
    rows = {d: [] for d in DOMAIN_ORDER}
    counts = dict.fromkeys(BADGE["en"], 0)
    title_key = "title_ko" if locale == "ko" else "title"
    claim_key = "claim_ko" if locale == "ko" else "claim"
    for s in statuses:
        st = s.get("claimed_status", "open")
        counts[st] = counts.get(st, 0) + 1
        d = s.get("domain") if s.get("domain") in rows else "other"
        readme_name = localized_problem_file(s, "README.md", locale)
        rows[d].append(
            f"| [{esc(s.get(title_key, s.get('title', s['id'])))}]"
            f"(problems/{s['id']}/{readme_name}) "
            f"| {BADGE[locale].get(st, st)} | {checks_cell(s, locale)} "
            f"| {solved_by_cell(s)} | {esc(s.get(claim_key, s.get('claim', '')))} |"
        )

    total = sum(counts.values())
    if locale == "ko":
        summary = f"**문제 {total}개** — " + " · ".join(
            f"{BADGE[locale][k]}: {counts.get(k, 0)}" for k in BADGE["en"])
    else:
        summary = f"**{total} problems** — " + " · ".join(
            f"{BADGE[locale][k]}: {counts.get(k, 0)}" for k in BADGE["en"])
    lines = [BEGIN, "", summary, ""]
    for d in DOMAIN_ORDER:
        if not rows[d]:
            continue
        lines += [f"### {DOMAIN_TITLE[locale][d]}", "",
                  TABLE_HEADER[locale],
                  "|---|---|---|---|---|", *rows[d], ""]
    lines.append(END)
    block = "\n".join(lines)

    badges = " ".join(
        f"![{label}]({SHIELD}/{quote(label, safe='')}-"
        f"{counts.get(g, 0) if g else total}-{color})"
        for g, label, color in COUNT_STYLE[locale]
    )
    counts_block = f"{CBEGIN}\n{badges}\n{CEND}"
    return block, counts_block


def details_block(statuses: list[dict], locale: str) -> str:
    """Render the index of problem-local mathematical-details artifacts."""
    rows = []
    title_key = "title_ko" if locale == "ko" else "title"
    for status in statuses:
        artifacts = status.get("artifacts") or []
        details = next(
            (
                artifact.get("path")
                for artifact in artifacts
                if artifact.get("kind") == "mathematical-details"
            ),
            None,
        )
        if not details:
            continue
        readme_name = localized_problem_file(status, "README.md", locale)
        details_name = localized_problem_file(status, details, locale)
        label = "Detailed derivation" if locale == "en" else "상세 전개"
        rows.append(
            f"| [{esc(status.get(title_key, status.get('title', status['id'])))}]"
            f"(../problems/{status['id']}/{readme_name}) "
            f"| {BADGE[locale].get(status.get('claimed_status', 'open'), 'open')} "
            f"| [{label}](../problems/{status['id']}/{details_name}) |"
        )

    header = (
        "| Problem | Claimed status | Mathematical details |"
        if locale == "en"
        else "| 문제 | 주장 상태 | 수학 상세 |"
    )
    return "\n".join([DBEGIN, header, "|---|---|---|", *rows, DEND])


def replace_block(text: str, begin: str, end: str, block: str, path: Path) -> str:
    """Replace one required generated block."""
    if text.count(begin) != 1 or text.count(end) != 1:
        relative = path.relative_to(ROOT)
        raise ValueError(f"{relative} must contain one {begin}/{end} pair")
    head, rest = text.split(begin, 1)
    _, tail = rest.split(end, 1)
    return head + block + tail


def main() -> int:
    check = "--check" in sys.argv
    statuses = []
    missing_ko = []
    for sf in sorted(ROOT.glob("problems/*/status.yaml")):
        with open(sf) as f:
            status = yaml.safe_load(f)
        statuses.append(status)
        for key in ("title_ko", "claim_ko"):
            if not isinstance(status.get(key), str) or not status[key].strip():
                missing_ko.append(f"{status.get('id', sf.parent.name)}.{key}")
    if missing_ko:
        print("missing Korean dashboard fields:")
        for item in missing_ko:
            print(f"  {item}")
        return 1

    stale = []
    for readme, locale in READMES:
        if not readme.exists():
            print(f"missing root landing page: {readme.relative_to(ROOT)}")
            return 1
        block, counts_block = dashboard_blocks(statuses, locale)
        text = readme.read_text(encoding="utf-8")
        if BEGIN in text and END in text:
            head, rest = text.split(BEGIN, 1)
            _, tail = rest.split(END, 1)
            new = head + block + tail
        else:
            heading = "Dashboard" if locale == "en" else "대시보드"
            new = text.rstrip() + f"\n\n## {heading}\n\n" + block + "\n"
        if CBEGIN in new and CEND in new:
            head, rest = new.split(CBEGIN, 1)
            _, tail = rest.split(CEND, 1)
            new = head + counts_block + tail
        if check:
            if new != text:
                stale.append(readme.name)
        else:
            readme.write_text(new, encoding="utf-8")

    for readme, locale in DOC_READMES:
        if not readme.exists():
            print(f"missing documentation index: {readme.relative_to(ROOT)}")
            return 1
        text = readme.read_text(encoding="utf-8")
        try:
            new = replace_block(
                text, DBEGIN, DEND, details_block(statuses, locale), readme
            )
        except ValueError as exc:
            print(exc)
            return 1
        if check:
            if new != text:
                stale.append(str(readme.relative_to(ROOT)))
        else:
            readme.write_text(new, encoding="utf-8")

    if check:
        if stale:
            print(f"stale dashboard in {stale}; run scripts/gen_readme.py")
            return 1
        print("README indexes up to date")
        return 0
    print(f"README indexes regenerated: {len(statuses)} problems")
    return 0


if __name__ == "__main__":
    sys.exit(main())
