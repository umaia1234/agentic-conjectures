/-!
# Agentic Conjectures — root module

Every Lean module under `AgenticConjectures/` must be imported here so that
`lake build` compiles the whole library. CI enforces this with
`scripts/check_imports.py`.

Layout per problem:
- `AgenticConjectures/<ProblemId>/Statement.lean` — faithful formal statement
  (may contain `sorry` while the problem is open; excluded from the no-sorry
  gate via an explicit allowlist in `status.yaml`).
- `AgenticConjectures/<ProblemId>/Proof.lean` — sorry-free proof or refutation.
-/
