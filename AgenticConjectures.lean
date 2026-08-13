import AgenticConjectures.Erdos671
import AgenticConjectures.GoldbachPrize2
import AgenticConjectures.GoldbachPrize3
import AgenticConjectures.GoldbachPrize4
import AgenticConjectures.OeisA000224
import AgenticConjectures.OeisA034267
import AgenticConjectures.OeisA067720
import AgenticConjectures.OeisA072780
import AgenticConjectures.OeisA112970
import AgenticConjectures.OeisA113249
import AgenticConjectures.OeisA136433
import AgenticConjectures.OeisA190363
import AgenticConjectures.OeisA239293
import AgenticConjectures.OeisA242560
import AgenticConjectures.OeisA270361
import AgenticConjectures.OeisA286185A286183
import AgenticConjectures.OeisA319197
import AgenticConjectures.OeisA368633
import AgenticConjectures.OeisA369378
import AgenticConjectures.OeisA384162
import AgenticConjectures.OeisA394666
import AgenticConjectures.OeisA396093
import AgenticConjectures.OeisA397588
import AgenticConjectures.OeisA398189
import AgenticConjectures.Erdos385

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
