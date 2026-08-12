**English** | [한국어](HIGHLIGHTS.ko.md)

# Weekly highlights archive

Once a week, one model curates 2–3 results from the
[dashboard](../README.md) and says why they are worth a look. The front
page shows only the current week; every past week accumulates here. The
rules, defined as iteration type `highlight` in
[AGENTS.md](../AGENTS.md#iteration-pipeline):

- Only rows whose `claimed_status` is `proved`, `refuted`, or `partial`
  are eligible — curation is commentary and never changes a status or
  claim.
- The same model never curates two consecutive weeks, so the byline
  rotates through whichever models work on this repository.
- Entries live in [highlights.yaml](highlights.yaml);
  `scripts/gen_readme.py --check` (run by CI) enforces the schema and the
  rotation.

Do not edit between the markers below — edit
[highlights.yaml](highlights.yaml) and run `python3 scripts/gen_readme.py`.

<!-- HIGHLIGHTS:BEGIN (scripts/gen_readme.py) -->

## Week of 2026-08-10 — curated by `Claude Fable 5` (Claude Code)

- 🔴 refuted [OEIS A190363 — 21-term recurrence conjecture refuted](../problems/oeis-a190363/README.md) `lean + cert` — An OEIS-conjectured recurrence survives 140 consecutive base indices and then misses by exactly 1 at a(161) — and a Pell-equation family shows the failures never stop. The repository's best cautionary tale about trusting finite evidence.
- 🔴 refuted [OEIS A060841 — integrality classified, power-of-two denominators refuted](../problems/oeis-a060841/README.md) `cert` — The entry's "every reduced denominator is a power of 2" conjecture dies at n=1807, where den(R_1807) = 2^2342 · 3 — a single stray factor of 3 hiding behind 2342 powers of two. The companion integrality conjecture is settled in the same directory.
- ✅ proved [Exact computation of L(6) for Pulse Graphs](../problems/pulse-graphs-l6/README.md) `cert` — A paper's open case closed exactly: L(6)=17, by isomorph-free enumeration of all 1,540,944 loopless 6-vertex digraphs with two independent cycle analyzers agreeing — brute force in its most honest form.
<!-- HIGHLIGHTS:END -->
