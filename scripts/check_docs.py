#!/usr/bin/env python3
"""Check local Markdown links and English/Korean companion navigation.

Human-facing Markdown files at the repository root and below ``docs/`` must
have an English/Korean pair.  Problem documentation may remain English-only,
but whenever a ``.ko.md`` companion exists, both files must link to each other
near the top.  Local links in every repository-owned Markdown file must point
to an existing path.

The checker intentionally does not make network requests or validate heading
fragments.  It verifies the repository-local path before a query or fragment.
"""

from __future__ import annotations

import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent

# Build products and dependency checkouts are not repository documentation.
IGNORED_DIRS = {
    ".git",
    ".lake",
    ".mypy_cache",
    ".pytest_cache",
    ".venv",
    "__pycache__",
    "build",
    "node_modules",
    "venv",
}

# CLAUDE.md is a one-line tool shim that delegates to AGENTS.md, not a
# human-facing document.  Every other root-level English Markdown file follows
# the bilingual companion policy.
UNPAIRED_ROOT_FILES = {"CLAUDE.md"}
TOP_LINE_LIMIT = 25

FENCE_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
HTML_COMMENT_RE = re.compile(r"<!--[\s\S]*?-->")
INLINE_CODE_RE = re.compile(r"(`+)[^\n]*?\1")
MATH_RE = re.compile(r"\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$")
REFERENCE_LINK_RE = re.compile(
    r"^ {0,3}\[(?!\^)[^\]\n]+\]:\s*(?:<([^>\n]*)>|(\S+))",
    re.MULTILINE,
)
HTML_LINK_RE = re.compile(
    r"\b(?:href|src)\s*=\s*(?:\"([^\"]*)\"|'([^']*)'|([^\s>]+))",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Link:
    line: int
    target: str


def markdown_files() -> list[Path]:
    """Return repository-owned Markdown files, including new untracked ones."""
    files: list[Path] = []
    for directory, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = sorted(d for d in dirnames if d not in IGNORED_DIRS)
        base = Path(directory)
        files.extend(base / name for name in filenames if name.endswith(".md"))
    return sorted(files, key=lambda path: path.relative_to(ROOT).as_posix())


def _blank(match: re.Match[str]) -> str:
    """Replace content while retaining offsets and line numbers."""
    return re.sub(r"[^\n]", " ", match.group(0))


def _strip_fenced_code(text: str) -> str:
    lines: list[str] = []
    fence_char: str | None = None
    fence_length = 0

    for line in text.splitlines(keepends=True):
        match = FENCE_RE.match(line)
        if fence_char is None:
            if match:
                marker = match.group(1)
                fence_char, fence_length = marker[0], len(marker)
                lines.append(re.sub(r"[^\n]", " ", line))
            else:
                lines.append(line)
            continue

        lines.append(re.sub(r"[^\n]", " ", line))
        if match:
            marker = match.group(1)
            if marker[0] == fence_char and len(marker) >= fence_length:
                fence_char = None
                fence_length = 0

    return "".join(lines)


def searchable_markdown(text: str) -> str:
    """Blank constructs whose link-like text Markdown does not interpret."""
    text = _strip_fenced_code(text)
    text = HTML_COMMENT_RE.sub(_blank, text)
    text = INLINE_CODE_RE.sub(_blank, text)
    return MATH_RE.sub(_blank, text)


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def inline_links(text: str) -> list[Link]:
    """Extract inline Markdown destinations, including nested-parenthesis URLs."""
    links: list[Link] = []
    cursor = 0

    while True:
        close_label = text.find("](", cursor)
        if close_label < 0:
            break
        cursor = close_label + 2

        # Avoid treating arbitrary prose containing ``](...`` as a link.
        line_start = text.rfind("\n", 0, close_label) + 1
        if "[" not in text[line_start:close_label]:
            continue

        start = cursor
        while start < len(text) and text[start].isspace():
            start += 1
        if start >= len(text):
            continue

        if text[start] == "<":
            end = start + 1
            while end < len(text) and text[end] != ">":
                end += 2 if text[end] == "\\" and end + 1 < len(text) else 1
            if end < len(text):
                links.append(
                    Link(_line_number(text, close_label), text[start + 1 : end])
                )
            continue

        end = start
        depth = 0
        while end < len(text):
            char = text[end]
            if char == "\\" and end + 1 < len(text):
                end += 2
                continue
            if char == "(":
                depth += 1
            elif char == ")":
                if depth == 0:
                    break
                depth -= 1
            elif char.isspace() and depth == 0:
                break
            end += 1

        links.append(Link(_line_number(text, close_label), text[start:end]))

    return links


def all_links(text: str) -> list[Link]:
    """Extract inline, reference-definition, and HTML links from Markdown."""
    searchable = searchable_markdown(text)
    links = inline_links(searchable)
    for match in REFERENCE_LINK_RE.finditer(searchable):
        target = match.group(1) if match.group(1) is not None else match.group(2)
        assert target is not None
        links.append(Link(_line_number(searchable, match.start()), target))
    for match in HTML_LINK_RE.finditer(searchable):
        target = next(group for group in match.groups() if group is not None)
        links.append(Link(_line_number(searchable, match.start()), target))
    return sorted(links, key=lambda link: (link.line, link.target))


def local_path(source: Path, target: str) -> Path | None:
    """Resolve a local link target, or return None for non-file destinations."""
    target = re.sub(r"\\(.)", r"\1", target.strip())
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc or not parsed.path:
        return None

    decoded = unquote(parsed.path)
    if decoded.startswith("/"):
        return ROOT / decoded.lstrip("/")
    return source.parent / decoded


def companion_for(path: Path) -> Path:
    if path.name.endswith(".ko.md"):
        return path.with_name(path.name.removesuffix(".ko.md") + ".md")
    return path.with_name(path.name.removesuffix(".md") + ".ko.md")


def companion_required(path: Path) -> bool:
    """Whether an English document is in a mandatory bilingual location."""
    relative = path.relative_to(ROOT)
    if len(relative.parts) == 1:
        return path.name not in UNPAIRED_ROOT_FILES
    return relative.parts[0] == "docs"


def has_top_language_line(path: Path, expected: str) -> bool:
    lines = path.read_text(encoding="utf-8").splitlines()[:TOP_LINE_LIMIT]
    return expected in (line.strip() for line in lines)


def check_companions(files: list[Path]) -> tuple[list[str], int]:
    errors: list[str] = []
    file_set = set(files)
    pairs = 0

    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        is_korean = path.name.endswith(".ko.md")

        if is_korean:
            english = companion_for(path)
            if english not in file_set:
                errors.append(f"{relative}: Korean document has no English companion")
            continue

        korean = companion_for(path)
        if korean not in file_set:
            if companion_required(path):
                errors.append(f"{relative}: missing required Korean companion")
            continue

        pairs += 1
        english_line = f"**English** | [한국어]({korean.name})"
        korean_line = f"[English]({path.name}) | **한국어**"
        if not has_top_language_line(path, english_line):
            errors.append(
                f"{relative}: expected near the top: {english_line}"
            )
        korean_relative = korean.relative_to(ROOT).as_posix()
        if not has_top_language_line(korean, korean_line):
            errors.append(
                f"{korean_relative}: expected near the top: {korean_line}"
            )

    return errors, pairs


def check_links(files: list[Path]) -> tuple[list[str], int]:
    errors: list[str] = []
    checked = 0
    root_resolved = ROOT.resolve()

    for source in files:
        relative = source.relative_to(ROOT).as_posix()
        text = source.read_text(encoding="utf-8")
        for link in all_links(text):
            destination = local_path(source, link.target)
            if destination is None:
                continue
            checked += 1
            resolved = destination.resolve()
            if not resolved.is_relative_to(root_resolved):
                errors.append(
                    f"{relative}:{link.line}: local link escapes repository: "
                    f"{link.target!r}"
                )
            elif not resolved.exists():
                errors.append(
                    f"{relative}:{link.line}: broken local link: {link.target!r}"
                )

    return errors, checked


def main() -> int:
    files = markdown_files()
    companion_errors, pairs = check_companions(files)
    link_errors, links = check_links(files)
    errors = sorted(companion_errors + link_errors)

    if errors:
        print("documentation check failed:")
        for error in errors:
            print(f"  {error}")
        return 1

    print(
        "documentation OK: "
        f"{len(files)} Markdown file(s), {links} local link(s), "
        f"{pairs} bilingual pair(s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
