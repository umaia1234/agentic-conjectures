# Upstream snapshots

Verbatim OEIS entry text for the three sequences treated in this directory,
retrieved 2026-08-12 with

```bash
curl -s "https://oeis.org/search?q=id:A286185&fmt=text" -o A286185.txt
curl -s "https://oeis.org/search?q=id:A286183&fmt=text" -o A286183.txt
curl -s "https://oeis.org/search?q=id:A286182&fmt=text" -o A286182.txt
```

| file | sequence | OEIS version at retrieval |
|---|---|---|
| `A286182.txt` | prism graph, `2n` nodes | #27 Feb 16 2025 |
| `A286183.txt` | antiprism graph, `2n` nodes | #21 Feb 16 2025 |
| `A286185.txt` | Möbius ladder graph, `2n` nodes | #26 Feb 16 2025 |

These are the canonical statements this directory is checked against: the `%N`
name lines fix what is being counted, the `%F` formula lines carry the
`(conjectured)` tags that [../PROOF.md](../PROOF.md) settles for A286185 and
A286183, and the `%t` Mathematica lines are the graph constructions that
[../certificate.py](../certificate.py) re-implements and cross-checks against
its own.

There is **no** upstream Lean snapshot: none of these entries appears in
google-deepmind/formal-conjectures, so the Lean statements in
`AgenticConjectures/OeisA286185A286183.lean` are written directly against the
OEIS text above rather than against a prior formalisation.

OEIS content is licensed CC BY-NC-SA 4.0 by The OEIS Foundation Inc.; these
files are included unmodified for provenance.
