#!/usr/bin/env python3
"""Regenerate the bilingual upstream-source tables from sources.yaml.

Only the content between the UPSTREAM-SOURCES markers is replaced. Run with
--check to fail when either committed table is stale.
"""

import argparse
import re
import sys
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parent.parent
SOURCE_FILE = ROOT / "docs" / "upstream" / "sources.yaml"
DOCUMENTS = (
    (ROOT / "docs" / "upstream" / "README.md", "en"),
    (ROOT / "docs" / "upstream" / "README.ko.md", "ko"),
)
BEGIN = "<!-- UPSTREAM-SOURCES:BEGIN (scripts/gen_upstream_docs.py) -->"
END = "<!-- UPSTREAM-SOURCES:END -->"
HEADERS = {
    "en": "| Repository | Commit | Purpose at the time |",
    "ko": "| 저장소 | 커밋 | 당시 용도 |",
}
REQUIRED_FIELDS = ("name", "url", "commit", "commit_url", "purpose", "purpose_ko")


def markdown_cell(value: str) -> str:
    """Escape characters that would break a Markdown table cell."""
    return value.replace("|", "\\|").replace("\n", " ")


def load_sources() -> list[dict[str, str]]:
    """Load and validate the source rows used by both localized documents."""
    try:
        data = yaml.safe_load(SOURCE_FILE.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError) as exc:
        raise ValueError(f"cannot load {SOURCE_FILE.relative_to(ROOT)}: {exc}") from exc

    if not isinstance(data, dict) or not isinstance(data.get("sources"), list):
        raise ValueError("docs/upstream/sources.yaml must contain a 'sources' list")

    sources = data["sources"]
    for index, source in enumerate(sources, start=1):
        if not isinstance(source, dict):
            raise ValueError(f"source row {index} must be a mapping")
        for field in REQUIRED_FIELDS:
            value = source.get(field)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"source row {index} has no non-empty '{field}'")
        if not re.fullmatch(r"[0-9a-f]{40}", source["commit"]):
            raise ValueError(f"source row {index} commit must be a full lowercase SHA-1")
        if not source["url"].startswith("https://"):
            raise ValueError(f"source row {index} url must use HTTPS")
        if not source["commit_url"].startswith("https://"):
            raise ValueError(f"source row {index} commit_url must use HTTPS")
    return sources


def generated_block(sources: list[dict[str, str]], locale: str) -> str:
    """Render the generated table block for one locale."""
    lines = [BEGIN, HEADERS[locale], "|---|---|---|"]
    purpose_key = "purpose_ko" if locale == "ko" else "purpose"
    for source in sources:
        lines.append(
            f"| [{markdown_cell(source['name'])}]({source['url']}) "
            f"| [`{source['commit']}`]({source['commit_url']}) "
            f"| {markdown_cell(source[purpose_key])} |"
        )
    lines.append(END)
    return "\n".join(lines)


def replace_generated_block(text: str, block: str, document: Path) -> str:
    """Replace exactly one generated block without touching surrounding prose."""
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        relative = document.relative_to(ROOT)
        raise ValueError(f"{relative} must contain exactly one matching marker pair")
    head, rest = text.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    return head + block + tail


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if either generated table differs from the committed document",
    )
    args = parser.parse_args()

    try:
        sources = load_sources()
        stale = []
        for document, locale in DOCUMENTS:
            original = document.read_text(encoding="utf-8")
            updated = replace_generated_block(
                original, generated_block(sources, locale), document
            )
            if args.check:
                if updated != original:
                    stale.append(str(document.relative_to(ROOT)))
            else:
                document.write_text(updated, encoding="utf-8")
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.check:
        if stale:
            print(
                "stale upstream source tables in "
                f"{stale}; run scripts/gen_upstream_docs.py"
            )
            return 1
        print(f"upstream source tables up to date: {len(sources)} sources")
        return 0

    print(f"upstream source tables regenerated: {len(sources)} sources")
    return 0


if __name__ == "__main__":
    sys.exit(main())
