**English** | [한국어](CONTRIBUTING.ko.md)

# Contributing

Got an agent and spare tokens? Point them at an open problem. This
repository is built so that an autonomous agent (Claude Code, Codex, or any
tool that can read a protocol file and run shell commands) can pick a
problem, attack it, and leave behind only machine-verified results.

## The 5-minute version

1. Fork and clone the repository.
2. Start your agent inside the repo and give it this kickoff prompt:

   ```text
   Read AGENTS.md and follow it exactly. Run one iteration: pick one problem
   from the README dashboard whose claimed_status is partial or open (or
   harvest a new small conjecture into a new problems/<id>/ directory).
   Attack it within the budgets in AGENTS.md. Before committing, pass every
   verification gate locally. Update the problem's status.yaml and README,
   regenerate the dashboard, and open a pull request from a branch.
   Never put your own name, any AI/model/tool name, or any trailer in
   commits, code, or documents.
   ```

3. The agent works; CI judges the PR. Green CI means the claims in the PR
   are machine-verified; anything CI cannot check must be labeled honestly
   in `status.yaml` (that is enforced by review).

Claude Code picks the protocol up automatically via `CLAUDE.md`; other tools
read `AGENTS.md` by convention. Nothing here is specific to one vendor.

## What counts as a contribution

In descending order of typical feasibility:

- **Lean formalizations** of results that currently have only informal
  proofs (`proved`/`refuted` rows without `lean` in the Machine checks
  column). This is the highest-value, lowest-risk work.
- **Extended search bounds** with reproducible code and recorded runtimes
  ("no counterexample up to N" is a normal product here).
- **New small problems**: auto-formalized OEIS conjectures, small
  combinatorics questions, minor conjectures from recent papers — harvested
  into a new `problems/<id>/` with an honest `status.yaml`.
- **Counterexamples or proofs** for existing `open`/`partial` problems.
- **Independent re-verification**: a second, independently written checker
  for an existing certificate.

Famous problems (Frankl, Conway 99-graph, Hadamard 668, projective plane of
order 12, R(3,10), …) are bound-tracking infrastructure — do not claim to
"solve" them; incremental, certified exclusions are welcome.

## Hard rules (summary of [AGENTS.md](AGENTS.md))

- Every claim must be machine-reverifiable: independent scripts for
  counterexamples, DRUP/DRAT for SAT, sorry-free Lean 4 for proofs
  (`sorry`, extra axioms, and `native_decide` are banned and CI-checked).
- Honest statuses. Never claim novelty before external review. Negative
  results are results.
- No self-attribution anywhere: no AI/model/tool names, no
  `Co-Authored-By`-style trailers, in any commit, document, or PR.
- English documents by default; a Korean `.ko.md` companion is welcome but
  optional for problem docs (update existing companions if you change their
  originals).
- Do not submit anything derived from this repository to external venues
  (OEIS, erdosproblems.com, journals, upstream repos) without opening an
  issue here first. Unreviewed machine output sent upstream is spam and
  harms everyone — this is the one form of misuse we actively police.

## Local verification gates (identical to CI)

```bash
pip install pyyaml sympy
python3 scripts/verify_all.py --ci        # re-run certificates
lake exe cache get && lake build          # Lean library (first run downloads ~5 GB)
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py
python3 scripts/gen_readme.py --check
```

## Review

PRs are reviewed for exactly two things: (1) CI is green, and (2) the
`status.yaml` claims match what was actually verified, including caveats.
Statement faithfulness of Lean formalizations (does the formal statement
match the cited source?) gets special scrutiny — quote the source in the
problem README and note any semantic gaps.
