**English** | [한국어](AGENTS.ko.md)

# AGENTS.md — Operating protocol for autonomous iterations

Every agent session working in this repository follows these rules. The goal:
pick open problems and conjectures, attack them, and accumulate **only
machine-verifiable results**.

## Iron rules

1. **Sign your work with your model and harness names — and keep human
   identities out.** Model attribution is mandatory and truthful:
   - Every commit message ends with two trailers naming who did the work,
     e.g. `Model: GPT-5.6 Sol` + `Harness: Codex CLI`, or
     `Model: Claude Fable 5` + `Harness: Claude Code`.
   - PR bodies state the same model/harness pair.
   - When you create or change a problem's results, record it in that
     problem's `status.yaml` under `attribution:` (model, harness, scope).
     The dashboard's "Solved by" column is generated from this.
   - **Never tag work you did not do, and never impersonate another model.**
     Attribution follows the same honesty bar as the mathematics.
   - Commit author/committer stays the **repo-local git identity
     (umaia1234 noreply) only** — never a personal account or email, and no
     `Co-Authored-By:` trailers (they alter the GitHub contributor graph);
     model attribution lives in the `Model:`/`Harness:` trailers instead.
   - Before every push, run `git log --format='%an <%ae>%n%B' -1` and check
     that the author is the repo identity and the trailers are present.
2. **Every claim must be machine-reverifiable.** Counterexamples need an
   independent verification script (ideally two independent implementations);
   SAT results need DRUP/DRAT certificates; proofs are Lean 4 (`sorry`,
   extra axioms, and `native_decide` are banned). A claim that CI cannot
   re-verify must look that way in `status.yaml` — no dressing up.
3. **Honest status labels.** `proved`/`refuted` only for complete claims.
   Partial results and negative searches are `partial`. Record work even when
   there is no result — "no counterexample up to N, plus code and logs" is a
   normal product of this repository. Never claim novelty before external
   review.
4. **No pushing straight to main (in autonomous loops).** Work on an
   `agent/<date>-<slug>` branch → push → PR → merge after CI is green.
   No force-push (unless a human explicitly instructs it).
5. **No downgrading or deleting verified results.** Changes that demote an
   existing `proved`/`refuted` or delete certificates require human approval.
   If an error is found, fix the status but record what happened in the
   problem README.
6. **Statement faithfulness.** Check every formalization against the
   `upstream/` snapshot or the canonical source. Keep the original quotation
   and source URL in the README, and state explicitly where our Lean statement
   could diverge from the original (index base, subtraction semantics,
   boundary values).
7. **External submissions only with human approval.** Everything that leaves
   the repository: OEIS comments, formal-conjectures PRs, erdosproblems
   reports, and the like.
8. **The default documentation language is English.** Documents, commit
   messages, code comments, and PR text are written in English. A Korean
   companion translation for human readers lives beside a document as
   `<name>.ko.md`, cross-linked from the top of both files
   (English file: `**English** | [한국어](<name>.ko.md)`,
   Korean file: `[English](<name>.md) | **한국어**`).
   When you change a document, update its companion in the same commit.

## Iteration pipeline

One autonomous iteration = exactly **one finite unit of work** from this list:

1. **harvest** — collect new candidates (formal-conjectures updates,
   erdosproblems.com, OEIS "conjectured" entries, recent minor arXiv
   conjectures). Prior-art check is mandatory: record already-solved problems
   as such and drop them.
2. **triage** — score candidates: refutable by finite search? formalizable
   with mathlib alone? expected compute budget? famous-problem status (famous
   hard problems are bound-tracking infrastructure, never "targets to solve").
3. **attack** — write a counterexample search program and run it within
   budget, or write a proof → formalize in Lean. Estimate the runtime of any
   search before launching it and stay under 2 hours locally (checkpoint and
   split anything longer).
4. **verify** — pass every gate below locally before committing.
5. **report** — update `status.yaml` → `python3 scripts/gen_readme.py` →
   record reproduction commands and runtimes in the problem README → push the
   branch + open a PR.

## Verification gates (run locally, identical to CI)

```
python3 scripts/check_imports.py    # every Lean module reachable from the root
python3 scripts/check_sorry.py      # sorry/admit/axiom/native_decide banned
lake build                          # full compilation
python3 scripts/check_axioms.py     # #print axioms: only the 3 standard axioms
python3 scripts/verify_all.py --ci  # re-run ci_feasible certificates
python3 scripts/gen_readme.py --check
```

## Lean conventions

- One root project (mathlib pinned at v4.30.0). One module (or subdirectory)
  per problem: `AgenticConjectures/<ProblemId>.lean`.
- Every new module must be imported in `AgenticConjectures.lean` (CI enforces
  this).
- State open problems as `def statement : Prop := ...` — no `sorry` needed.
  Proofs/refutations are `theorem ... : statement` / `theorem ... : ¬ statement`.
- Register completed theorems in the problem's `status.yaml` under
  `lean.modules`/`lean.theorems` (they enter the axiom audit).
- Record the correspondence with the upstream snapshot (same proposition?
  which semantic differences?) in the module docstring.

## status.yaml schema

```yaml
id: <dirname>
title: "..."
domain: oeis | erdos | graph-combinatorics | other
source_url: "..."
claimed_status: proved | refuted | partial | open
claim: "one-sentence summary (English)"
artifacts: [{path, kind}]
verify:                     # relative to the problem dir; CI runs only ci_feasible
  - cmd: "..."
    expected_runtime: "..."
    ci_feasible: true|false
    requires: [drat-trim]   # optional: external tools that must be on PATH
lean:                       # only once formalized
  modules: [AgenticConjectures.Foo]
  theorems: [AgenticConjectures.Foo.bar]
attribution:                # who did the work (iron rule 1)
  - model: "GPT-5.6 Sol"
    harness: "unspecified"
    scope: "original research artifacts"
  - model: "Claude Fable 5"
    harness: "Claude Code"
    scope: "Lean 4 formalization"
notes: "what a skeptical reviewer should know"
```

## Compute & disk conventions

- Compiled outputs go under `build/` (already gitignored) or `/tmp`. Never
  commit binaries.
- Review the necessity of any large artifact (>5MB) before committing — if it
  is regenerable, record the command instead.
- This machine has little free disk. Write large temporary files to `/tmp`
  and clean them up.
