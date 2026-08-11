**English** | [한국어](README.ko.md)

# Agentic Conjectures

A workspace where autonomous agents pick open problems and conjectures, attack
them, and accumulate results **only in machine-verifiable form**. The agent
claims; CI judges whether mathematics happened.

There are four result grades.

| Grade | Evidence required |
|---|---|
| ✅ proved | A Lean 4 proof with no `sorry`/extra axioms, or a complete proof document |
| 🔴 refuted | An explicit counterexample + independent verification script (DRUP/DRAT certificates for SAT results) |
| 🟡 partial | Partial results, search lower bounds, negative searches ("no counterexample up to N") |
| ⚪ open | No resolution claimed (survey/tooling only) |

The `Machine checks` column shows what CI actually re-verifies — `lean` means
`lake build` + the no-sorry gate + the axiom audit, `cert` means certificate
scripts are re-run, and `cert(local)` means only local-only (heavy)
reproduction commands exist. **A claim CI does not verify is just a claim.**
Every problem here is unreviewed and claims no novelty (see the disclaimers
in each problem README).

- `problems/<id>/` — one problem's write-up, proofs, code, certificates, and
  results (`status.yaml` is the machine-readable state)
- `AgenticConjectures/` — this repository's own Lean 4 formalizations
  (mathlib-based)
- `scripts/` — verification gates and the dashboard generator; operating
  rules are in [AGENTS.md](AGENTS.md)
- [MATHEMATICAL_DETAILS.md](MATHEMATICAL_DETAILS.md) — definitions, lemmas,
  and proofs for five of the problems collected in one place
- Reproduction commands follow each problem's `README.md` (paths relative to
  the problem directory)

## How to use

**Verify the existing results** (nothing here needs to be taken on faith):

```bash
git clone https://github.com/umaia1234/agentic-conjectures.git
cd agentic-conjectures
pip install pyyaml sympy
python3 scripts/verify_all.py --ci     # re-run the fast certificates (~1 min)
```

For the Lean-verified rows, install [elan](https://github.com/leanprover/elan),
then:

```bash
lake exe cache get                     # downloads the mathlib build cache (~5 GB)
lake build
python3 scripts/check_sorry.py && python3 scripts/check_axioms.py
```

**Point an agent at an open problem.** The operating protocol lives in
[AGENTS.md](AGENTS.md) and is agent-tool-agnostic (Claude Code also picks it
up via `CLAUDE.md`). Start your agent inside the repo with:

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

Good first targets: Lean-formalizing results that currently have only
informal proofs, extending search bounds, or harvesting small OEIS/arXiv
conjectures. Famous problems are bound-tracking infrastructure, not "solve
me" targets. Details in [CONTRIBUTING.md](CONTRIBUTING.md).

## Dashboard

<!-- STATUS:BEGIN (scripts/gen_readme.py) -->

**35 problems** — ✅ proved: 7 · 🔴 refuted: 4 · 🟡 partial: 16 · ⚪ open: 8

### OEIS

| Problem | Claimed status | Machine checks | Claim |
|---|---|---|---|
| [OEIS A000224 — R(n)(R(n)-1) divides n^2-1 iff n is an odd prime](problems/oeis-a000224/README.md) | 🟡 partial | cert | Proves there is no composite counterexample among even n, odd prime powers p^e (e>=2), and products of two distinct odd primes, plus a Pell-orbit scan covering all K<=375, n<=10^18 with omega(n)<=3; explicitly does not claim to resolve the OEIS conjecture. |
| [OEIS A056777 / Choudhury–Wei Conjecture 1.1 — n+12 not a prime power](problems/oeis-a056777/README.md) | 🟡 partial | — | Proves that for composite n>=4 with phi(n+12)=phi(n)+12 and sigma(n+12)=sigma(n)+12, n+12 cannot be a prime power; the original Choudhury–Wei Conjecture 1.1 remains unresolved. |
| [OEIS A060841 — integrality classified, power-of-two denominators refuted](problems/oeis-a060841/README.md) | 🔴 refuted | cert | Claims both OEIS conjectures are settled: R_n is an integer exactly for n in {1,...,34,36,38} (integrality conjecture proved via a 2-adic bound for n>=91 plus finite certification), while the claim that all reduced denominators are powers of 2 is refuted by den(R_1807)=2^2342*3. |
| [OEIS A063880 — sigma(n)=2*sigma*(n) with small powerful core](problems/oeis-a063880/README.md) | 🟡 partial | — | Proves that every solution of sigma(n)=2*sigma*(n) whose powerful core has at most two distinct primes has core exactly 108, so within that subfamily 108 is the only primitive term and all terms are 108 mod 216; cores with >=3 distinct primes are not excluded, so the full conjecture is unresolved. |
| [OEIS A067720 — phi(k^2+1)=k*phi(k+1) prime-power subfamily](problems/oeis-a067720/README.md) | 🟡 partial | — | Proves that if k+1=p^a with a>=2 then there is no solution for p=2, and for odd p with V=v2(p^a-1)+v2(p-1)<=5 the only solution is (p,a,k)=(3,2,8); general composite k+1 and the V>=6 prime-power cases remain open, so the original question is unresolved. |
| [OEIS A076141 — n occurs at most once in binary of n^2, checked to 2^40](problems/oeis-a076141/README.md) | 🟡 partial | cert | An exact exhaustive occurrence-geometry search found no counterexample for 0 < n < 2^40, extending the OEIS-recorded 10^6 verification by a factor of about 1.1 million; explicitly a rigorous bounded verification, not a proof of the full conjecture. |
| [OEIS A136433 — 9-lag linear recurrence proved for all n>=10](problems/oeis-a136433/README.md) | ✅ proved | lean + cert | Claims a complete proof that the OEIS-conjectured constant-coefficient recurrence a_n = 6*a_{n-3} + a_{n-6} - 6*a_{n-9} holds for all n>=10 for the periodic-coefficient nonautonomous sequence, via a_{t+3}=6*a_t+B_t with B_t of period 6. |
| [OEIS A190363 — 21-term recurrence conjecture refuted](problems/oeis-a190363/README.md) | 🔴 refuted | lean + cert | Refutes the OEIS-conjectured recurrence a(n+21)=a(n+17)+a(n+4)-a(n): first failure at base index n=140 (output term a(161), 541 != 542), with a Pell-equation-generated infinite family of failures showing the recurrence fails beyond every starting index. |
| [OEIS A245211: a(n)=n only for n=21](problems/oeis-a245211/README.md) | 🟡 partial | cert(local) | Claims only partial progress: proved necessary conditions forcing any counterexample to the uniqueness of n=21 to be coprime to 2310 with a restricted factorization shape, plus exact verification for all n <= 10^9 and for two-prime-factor n with exponents <= 200. |
| [OEIS A297707 prime-gap search code](problems/oeis-a297707/README.md) | ⚪ open | — | Claims no result: the directory contains only experimental prime-gap search code whose reported endpoints are Baillie-PSW probable primes, certifying nothing about the conjecture. |
| [OEIS A340881 modular periodicity](problems/oeis-a340881/README.md) | ✅ proved | cert | Claims a complete informal proof of both OEIS periodicity conjectures, giving explicit pure periods mod odd m (period 2*ord_m(2) from n=1) and eventual periodicity of A340881(n) mod m for every m >= 2. |
| [OEIS A354747 first unknown case a(100943)](problems/oeis-a354747/README.md) | 🔴 refuted | cert(local) | Claims a(100943)=39101 via two independent deterministic primality certificates (GMP Lucas-rank and OpenPFGW BLS) for 201886*3^39101-1 plus exhaustive compositeness checks of all exponents 1..39100, refuting the upstream FormalConjectures statement a(100943)=0. |
| [OEIS A395412 certified finite nonvanishing extension](problems/oeis-a395412/README.md) | 🟡 partial | cert(local) | Claims a certified finite extension only: reproduces the 84 published terms, rigorously proves a(n) > 0 for every 85 <= n <= 200 via PARI/GP isprime witnesses, and BPSW-screens 201 <= n <= 400 with no proof claimed there. |
| [OEIS A397245 mod 3 coefficient classification](problems/oeis-a397245/README.md) | ✅ proved | cert | Claims a complete informal proof of both conjectured mod 3 iff-classifications of a_n (a_n = 1 mod 3 iff n+2 = 3^j or 2*3^j; a_n = 2 mod 3 iff n+2 = 3^i + 3^j with i < j; else 0) via a closed form in F_3[[x]]. |
| [OEIS A397621 Pascal-row linear complexity](problems/oeis-a397621/README.md) | ✅ proved | cert | Claims a complete informal proof that A397621(A001317(n)) = 2^(floor(log2 n)+1) - n = A080079(n) for all n >= 1, with a zero-run lower bound and an explicit connection polynomial (1+x)^d upper bound. |

### Erdős problems

| Problem | Claimed status | Machine checks | Claim |
|---|---|---|---|
| [Erdős #307 — product of prime reciprocal sums equal to 1](problems/erdos-307/README.md) | 🟡 partial | cert | Re-proves forcing identities and local Legendre/mod-8/mod-24 necessary conditions and exhaustively shows \|P union Q\| >= 60 and max(P union Q) >= 347; the problem itself remains open and no novelty is claimed. |
| [Erdős #385 / #430(i) — finite-range experiments on F(n)-n](problems/erdos-385/README.md) | ⚪ open | cert | Provides two C++ finite-range experiments probing the quantity F(n)-n for parts (i)/(ii) and explicitly states they prove none of the three conjecture statements; no bound or result is asserted in the README. |
| [Erdős #424 — positive density of the generated set (finite probe)](problems/erdos-424/README.md) | ⚪ open | cert | Describes an exact finite experiment generating the set via n+1=xy with distinct members and scanning residue classes for omissions; the README explicitly says the finite search does not prove positive density. |
| [Finite projective plane of order 12](problems/projective-plane-order-12/README.md) | ⚪ open | — | Claims nothing new: records the open existence problem for a projective plane of order 12 (equivalently a symmetric 2-(157,13,1) design), known collineation-group exclusions, and computational considerations only. |

### Graphs & combinatorics

| Problem | Claimed status | Machine checks | Claim |
|---|---|---|---|
| [Chvatal's downset conjecture — saturated SAT reduction](problems/chvatal-downset/README.md) | 🟡 partial | cert | Proves an elementary saturation lemma and reports an uncertified n=6 UNSAT exclusion of counterexamples under stated reductions; n=8 attempts timed out and the general conjecture remains open. |
| [Conway's 99-graph problem srg(99,14,1,2)](problems/conway-99-graph/README.md) | ⚪ open | — | Status survey only: records that existence of srg(99,14,1,2) is open and cites 2025 automorphism-group restrictions (Cesarz–Woldar); no new computation or resolution is claimed. |
| [Frankl's union-closed sets conjecture](problems/frankl-union-closed/README.md) | ⚪ open | — | Status survey only: records that the conjecture is known for ground sets of size <= 12 and the general 0.38234\|F\| frequency lower bound, and explicitly resolves nothing (including the 13-element case). |
| [Hadamard matrix of order 668](problems/hadamard-668/README.md) | ⚪ open | — | Status survey only: 668 is recorded as the smallest unresolved Hadamard order, summarizing a 2026 Legendre-pair (length 333) search status report; no new existence or nonexistence result is claimed. |
| [Exact computation of L(6) for Pulse Graphs](problems/pulse-graphs-l6/README.md) | ✅ proved | cert | Claims the exact value L(6)=17 for the paper's open case n=6, via exhaustive isomorph-free enumeration of all 1,540,944 loopless 6-vertex digraphs with two independent cycle analyzers, plus an independently verified explicit 17-cycle witness. |
| [R(3,10) C20-bicirculant subcase exclusion](problems/ramsey-r3-10/README.md) | 🟡 partial | cert | Claims a SAT/DRUP-certified exclusion of one automorphism class only: no triangle-free 40-vertex graph with independence number <= 9 is invariant under the C20 action with cycle structure 20^2, so a hypothetical 40-vertex (3,10) Ramsey graph cannot be such a bicirculant; R(3,10) in {40,41} is not determined. |
| [Graph recoloring reconfiguration radius, Question 15](problems/recoloring-radius-q15/README.md) | ⚪ open | cert | Claims no result: the directory only provides exact-BFS counterexample-search tooling (Python atlas scan and a sharded C++ graph6 search) for Cambie-Cames van Batenburg-Cranston Question 15, with no outcome reported. |
| [WOWII Graph Conjecture 61 partial results](problems/wowii-graph-conjecture-61/README.md) | 🟡 partial | — | Claims informal proofs of partial results only: f(G) >= alpha(G) + ceil(D(G)/4) in general, f(G) >= alpha(G)+1 with diameter consequences, and the original conjecture f(G) >= r(G) + ceil(D(G)/3) for all connected graphs of diameter in {0,1,2,3,5,6,9} and for all trees. |

### Other

| Problem | Claimed status | Machine checks | Claim |
|---|---|---|---|
| [Degree vs sensitivity — n=14 degree-5 aggregate constraints](problems/degree-vs-sensitivity/README.md) | 🟡 partial | cert | Claims exact necessary layer constraints (B_2>=84, exactly 247 feasible (B_2,B_3,B_4,B_5) profiles) for the n=14 degree<=5 fully sensitive case, while the truth-table existence search ended with status UNKNOWN. |
| [Floridian solitaire — immediate losses for every n > 6](problems/floridian-solitaire/README.md) | ✅ proved | cert | Claims a complete (unreviewed) proof that every integer n > 6 has an immediate-loss position, resolving the open residue classes n = 0,2 (mod 6) of Meyerowitz–Curran–Locke–Low's second research question via a gap-two block construction plus explicit cases 18 and 20. |
| [Mortal words in small image-bounded NFAs (Kiefer–Ryzhikov)](problems/nfa-mortal-words/README.md) | 🟡 partial | cert | Claims exact extremal shortest-mortal-word lengths 1,3,7,10 for labelled ordered binary 2-image-bounded NFAs with up to 4 states, plus a 5-state lower-bound witness of length 17; the paper's general n^(k+1) tightness question is not resolved. |
| [Powers-of-two translational tiles (BKT Question 9)](problems/powers-of-two-tiles/README.md) | 🔴 refuted | cert | Claims explicit counterexamples refuting the suggested one-or-two-cardinality restriction in the yes/no clause of Benjamini-Kozma-Tzalik Question 9: translational tiles of every positive odd cardinality exist inside {1,2,4,...,2^n}, the smallest being A={1,4,16} with B={0,1,2}+9Z. |
| [Independent Schur-6 attempt](problems/schur-6/README.md) | 🟡 partial | cert | Claims only independent reverification of the published S(6) >= 536 partition and negative search results toward [1,537]: the best saved 537-coloring has exactly two monochromatic Schur triples, a depth-5 repair exclusion around it found nothing, and the full SAT instance remained undecided. |
| [Small Diophantine equations low-degree ansatz attempt](problems/small-diophantine/README.md) | 🟡 partial | cert | Claims only exact negative results: three low-degree rational-curve ansatz classes and a narrow integer-Q Pell-factor spot-check admit no solutions for the six remaining equations z^2 + y^2*z + x^3 + a*x + b = 0, none of which is claimed solved. |
| [Stretched Littlewood-Richardson negative-coefficient search](problems/stretched-lr/README.md) | 🟡 partial | — | Claims only a negative search: across ~243k classic-lrcalc triples, 9M Rust random trials with exact interpolation, and an exhausted 10,312-pair stretched-Kostka subfamily, no triple in the FrontierMath box produced a negative ordinary power-basis coefficient. |
| [Computable transcendental with all floored powers composite](problems/transcendental-composite-powers/README.md) | ✅ proved | — | Claims a complete informal proof that there is a computable transcendental alpha in (10,11) with floor(alpha^n) composite (an even integer >= 10) for every n >= 1, answering the transcendental part of the open question in Section 7 of Hahn-Ismailescu-Kim-Kim. |

<!-- STATUS:END -->

## Upstream source snapshots

Instead of full clones of the external repositories used during
investigation, only the files directly corresponding to each problem are
preserved in that problem's `upstream/`. Repository commits, restoration
instructions, licenses, and preservation scope are in
[UPSTREAM_SOURCES.md](UPSTREAM_SOURCES.md). The Lean files under `upstream/`
are **formalization snapshots** of the conjectures; declarations containing
`sorry` must not be read as formal proofs.

Some JSON files recording past runs keep pre-cleanup `agent_*` paths in their
`*_output` values. These are original run metadata, not reproduction paths,
and were left unchanged.

## License, priority, and credit

- Original code and documents in this repository are licensed under
  [Apache-2.0](LICENSE). Vendored upstream snapshots keep their own licenses
  and headers — see [UPSTREAM_SOURCES.md](UPSTREAM_SOURCES.md) and
  `THIRD_PARTY_LICENSES/`.
- **No priority is claimed on any result here.** Everything is unreviewed
  machine-assisted work until stated otherwise. If a result turns out to
  matter, credit belongs first to the original problem's proposers and the
  surrounding community; treat this repository as computational assistance.
  If you find prior work that subsumes or predates a result here, please
  open an issue — the status and attribution will be corrected.
- Please do not repackage claims from here as established results: run the
  verification gates, read the caveats in each problem README, and never
  forward unverified material to upstream venues (OEIS, erdosproblems.com,
  journals). See [CONTRIBUTING.md](CONTRIBUTING.md).

## Citation

Cite the **original problem source first** — every problem's `status.yaml`
carries a `source_url` and every problem README links the canonical
statement. To reference material from this repository itself (a
formalization, a certificate, a search bound), cite the specific problem
directory pinned to a commit hash; [CITATION.cff](CITATION.cff) provides
repository metadata for citation managers. Example:

> Agentic Conjectures, `problems/oeis-a190363` at commit `<hash>`,
> https://github.com/umaia1234/agentic-conjectures
