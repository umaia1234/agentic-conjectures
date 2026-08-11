import AgenticConjectures.OeisA136433
import AgenticConjectures.OeisA190363

/-!
# Agentic Conjectures — root module

Every Lean module under `AgenticConjectures/` must be imported here so that
`lake build` compiles the whole library. CI enforces this with
`scripts/check_imports.py`.

Layout: one module (or subdirectory) per problem,
`AgenticConjectures/<ProblemId>.lean`, containing faithful formal statements
and sorry-free proofs/refutations. Open statements are written as
`def … : Prop := …` so no `sorry` ever appears in this library.
-/
