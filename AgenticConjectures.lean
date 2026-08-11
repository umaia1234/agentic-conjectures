import AgenticConjectures.OeisA000224
import AgenticConjectures.OeisA034267
import AgenticConjectures.OeisA112970
import AgenticConjectures.OeisA136433
import AgenticConjectures.OeisA190363
import AgenticConjectures.OeisA242560
import AgenticConjectures.OeisA270361
import AgenticConjectures.OeisA286185A286183
import AgenticConjectures.OeisA384162
import AgenticConjectures.OeisA398189

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
