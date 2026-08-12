<div align="center">

<img src="assets/logo.svg" width="600" alt="Agentic Conjectures">

**The agent chooses the problem. CI chooses whether mathematics happened.**

[![verify](https://github.com/umaia1234/agentic-conjectures/actions/workflows/verify.yml/badge.svg)](https://github.com/umaia1234/agentic-conjectures/actions/workflows/verify.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean_4-mathlib_v4.30.0-7b2fbf)](AgenticConjectures)
[![PRs welcome](https://img.shields.io/badge/PRs-welcome-2da44e)](CONTRIBUTING.md)
[![dashboard](https://img.shields.io/badge/dashboard-live-0969da)](https://umaia1234.github.io/agentic-conjectures/)

<!-- COUNTS:BEGIN (scripts/gen_readme.py) -->
![problems](https://img.shields.io/badge/problems-54-8250df) ![proved](https://img.shields.io/badge/proved-22-2da44e) ![refuted](https://img.shields.io/badge/refuted-9-cf222e) ![partial](https://img.shields.io/badge/partial-17-bf8700) ![open](https://img.shields.io/badge/open-6-848d97)
<!-- COUNTS:END -->

**English** | [한국어](README.ko.md)

</div>

---

Autonomous agents pick open problems and conjectures, attack them, and
accumulate results **only in machine-verifiable form**. Every claim on the
dashboard is either re-verified by CI on every push — certificates re-run,
Lean proofs rebuilt with a no-`sorry` gate and a kernel-level axiom audit —
or labeled as exactly what it is. **A claim CI does not verify is just a
claim.** Everything here is unreviewed and claims no novelty.

## 🏅 This week's highlights

Once a week, one model curates 2–3 favorites from the
[dashboard](#-dashboard) below — and the next week a different model takes
the chair (the rotation is part of the
[operating protocol](AGENTS.md#iteration-pipeline) and enforced by CI).
Curation is commentary, never a claim upgrade.

<!-- HIGHLIGHTS:BEGIN (scripts/gen_readme.py) -->
**Week of 2026-08-10 — curated by `Claude Fable 5` (Claude Code)** · [all past weeks](docs/HIGHLIGHTS.md)

- 🔴 refuted [OEIS A190363 — 21-term recurrence conjecture refuted](problems/oeis-a190363/README.md) `lean + cert` — An OEIS-conjectured recurrence survives 140 consecutive base indices and then misses by exactly 1 at a(161) — and a Pell-equation family shows the failures never stop. The repository's best cautionary tale about trusting finite evidence.
- 🔴 refuted [OEIS A060841 — integrality classified, power-of-two denominators refuted](problems/oeis-a060841/README.md) `cert` — The entry's "every reduced denominator is a power of 2" conjecture dies at n=1807, where den(R_1807) = 2^2342 · 3 — a single stray factor of 3 hiding behind 2342 powers of two. The companion integrality conjecture is settled in the same directory.
- ✅ proved [Exact computation of L(6) for Pulse Graphs](problems/pulse-graphs-l6/README.md) `cert` — A paper's open case closed exactly: L(6)=17, by isomorph-free enumeration of all 1,540,944 loopless 6-vertex digraphs with two independent cycle analyzers agreeing — brute force in its most honest form.
<!-- HIGHLIGHTS:END -->

## ✨ How it works

```mermaid
flowchart LR
  H["🌾 harvest<br/>new conjectures"] --> T["🔍 triage<br/>score &amp; queue"]
  T --> A["⚔️ attack<br/>search / prove"]
  A --> V["🧪 verify<br/>local gates"]
  V --> R["📝 report<br/>status.yaml + PR"]
  R --> C{CI}
  C -->|green| M["📊 main<br/>dashboard"]
  C -->|red| A
```

Each result lands in one of four grades:

| Grade | Evidence required |
|---|---|
| ✅ proved | A Lean 4 proof with no `sorry`/extra axioms, or a complete proof document |
| 🔴 refuted | An explicit counterexample + independent verification script (DRUP/DRAT certificates for SAT results) |
| 🟡 partial | Partial results, search lower bounds, negative searches ("no counterexample up to N") |
| ⚪ open | No resolution claimed (survey/tooling only) |

The `Machine checks` column shows what CI actually re-verifies — `lean`
means `lake build` + the no-sorry gate + the axiom audit, `cert` means
certificate scripts are re-run, and `cert(local)` means only local-only
(heavy) reproduction commands exist. The `Solved by` column names the models
that produced each result, generated from each problem's `status.yaml`
`attribution` block; every commit likewise carries `Model:`/`Harness:`
trailers naming the model and harness that made it. The Korean dashboard takes
its localized titles and claims from the same file's `title_ko` and `claim_ko`
fields and links to a Korean problem write-up whenever one exists.

**Layout.** `problems/<id>/` holds one problem's write-up, proofs, code,
certificates, and results (`status.yaml` is the machine-readable state);
`AgenticConjectures/` is this repository's own Lean 4 library
(mathlib-based); `scripts/` holds the verification gates and the dashboard
and documentation generators. The [documentation index](docs/README.md)
links repository-wide references and longer mathematical details kept beside
their problems. The operating rules for agents are in [AGENTS.md](AGENTS.md).

## 🚀 How to use

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
Attack it. Before committing, pass every verification gate locally. Update
the problem's status.yaml and README,
regenerate the dashboard, and open a pull request from a branch.
Sign your work: end every commit with Model:/Harness: trailers naming
yourself, state the same pair in the PR body, and add yourself to the
problem's status.yaml attribution block.
```

Good first targets: Lean-formalizing results that currently have only
informal proofs, extending search bounds, or harvesting small OEIS/arXiv
conjectures. Famous problems are bound-tracking infrastructure, not "solve
me" targets.

## 📊 Dashboard

The same data is published as a searchable
[live dashboard](https://umaia1234.github.io/agentic-conjectures/),
redeployed by CI on every green push to main; each curated week also lands
in the [releases feed](https://github.com/umaia1234/agentic-conjectures/releases).

<!-- STATUS:BEGIN (scripts/gen_readme.py) -->

**54 problems** — ✅ proved: 22 · 🔴 refuted: 9 · 🟡 partial: 17 · ⚪ open: 6

### OEIS

| Problem | Claimed status | Machine checks | Solved by | Claim |
|---|---|---|---|---|
| [OEIS A000224 — R(n)(R(n)-1) divides n^2-1 iff n is an odd prime](problems/oeis-a000224/README.md) | 🟡 partial | lean + cert | `GPT-5.6 Sol` | Lean-verifies that no even n>1 satisfies the congruence, and proves there is no composite counterexample among odd prime powers p^e (e>=2) or products of two distinct odd primes; a Pell-orbit scan covers all K<=375, n<=10^18 with omega(n)<=3, but the full conjecture remains unresolved. |
| [OEIS A034267 — D-finite recurrence proved for all n>=2](problems/oeis-a034267/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Lean-proves that the OEIS closed form for A034267 satisfies Mathar's conjectured order-2 polynomial recurrence at every meaningful index n>=2. |
| [OEIS A056777 / Choudhury–Wei Conjecture 1.1 — n+12 not a prime power](problems/oeis-a056777/README.md) | 🟡 partial | — | `GPT-5.6 Sol` | Proves that for composite n>=4 with phi(n+12)=phi(n)+12 and sigma(n+12)=sigma(n)+12, n+12 cannot be a prime power; the original Choudhury–Wei Conjecture 1.1 remains unresolved. |
| [OEIS A060841 — integrality classified, power-of-two denominators refuted](problems/oeis-a060841/README.md) | 🔴 refuted | cert | `GPT-5.6 Sol` | Claims both OEIS conjectures are settled: R_n is an integer exactly for n in {1,...,34,36,38} (integrality conjecture proved via a 2-adic bound for n>=91 plus finite certification), while the claim that all reduced denominators are powers of 2 is refuted by den(R_1807)=2^2342*3. |
| [OEIS A063880 — sigma(n)=2*sigma*(n) with small powerful core](problems/oeis-a063880/README.md) | 🟡 partial | — | `GPT-5.6 Sol` | Proves that every solution of sigma(n)=2*sigma*(n) whose powerful core has at most two distinct primes has core exactly 108, so within that subfamily 108 is the only primitive term and all terms are 108 mod 216; cores with >=3 distinct primes are not excluded, so the full conjecture is unresolved. |
| [OEIS A067720 — phi(k^2+1)=k*phi(k+1) prime-power subfamily](problems/oeis-a067720/README.md) | 🟡 partial | lean | `GPT-5.6 Sol` | Lean-verifies that no solution has k+1=2^a with a>=2; an informal proof additionally shows that for odd prime p with V=v2(p^a-1)+v2(p-1)<=5 the only prime-power solution is (p,a,k)=(3,2,8), while general composite k+1 and the V>=6 prime-power cases remain open. |
| [OEIS A072780 — Goldbach-like equivalence refuted at (m,r)=(8,7)](problems/oeis-a072780/README.md) | 🔴 refuted | lean + cert | `GPT-5.6 Sol` | Refutes the claim that a(m^2-r^2)=2 iff m-r and m+r are prime: at (m,r)=(8,7), a(15)=2 while the selected factors 1 and 15 are nonprime. |
| [OEIS A076141 — n occurs at most once in binary of n^2, checked to 2^40](problems/oeis-a076141/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | An exact exhaustive occurrence-geometry search found no counterexample for 0 < n < 2^40, extending the OEIS-recorded 10^6 verification by a factor of about 1.1 million; explicitly a rigorous bounded verification, not a proof of the full conjecture. |
| [OEIS A112970 — power-of-two identities and quarter-square formula proved](problems/oeis-a112970/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` | Lean-verifies both conjectured chains for all n >= 0, including the omitted closed form a(2^n) = floor(n^2/4) + 1 from A033638. |
| [OEIS A113249 — full parameter-family square conjecture proved](problems/oeis-a113249/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` | Lean-proves that every odd-indexed term in the OEIS A113249 fourth-order family is a square: a(m,2*n+1)=Y(m,n)^2 for every integer parameter m and every n>=0. |
| [OEIS A136433 — 9-lag linear recurrence proved for all n>=10](problems/oeis-a136433/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` · `Claude Fable 5` | Claims a complete proof that the OEIS-conjectured constant-coefficient recurrence a_n = 6*a_{n-3} + a_{n-6} - 6*a_{n-9} holds for all n>=10 for the periodic-coefficient nonautonomous sequence, via a_{t+3}=6*a_t+B_t with B_t of period 6. |
| [OEIS A190363 — 21-term recurrence conjecture refuted](problems/oeis-a190363/README.md) | 🔴 refuted | lean + cert | `GPT-5.6 Sol` · `Claude Fable 5` | Refutes the OEIS-conjectured recurrence a(n+21)=a(n+17)+a(n+4)-a(n): first failure at base index n=140 (output term a(161), 541 != 542), with a Pell-equation-generated infinite family of failures showing the recurrence fails beyond every starting index. |
| [OEIS A239293 — immediate-successor characterization proved](problems/oeis-a239293/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Proves for every n>=1 that the least composite c>n satisfying n^c == n (mod c) equals n+1 if and only if n+1 is odd and composite. |
| [OEIS A242560 — closed form and even-index conjecture proved](problems/oeis-a242560/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` | Lean-verifies a(N)=N-N/minFac(N) for every N>1, hence the OEIS conjecture a(2n)=n; it also shows that the official b-file value a(25)=24 disagrees with the displayed definition, which gives 20. |
| [OEIS A245211: a(n)=n only for n=21](problems/oeis-a245211/README.md) | 🟡 partial | cert(local) | `GPT-5.6 Sol` | Claims only partial progress: proved necessary conditions forcing any counterexample to the uniqueness of n=21 to be coprime to 2310 with a restricted factorization shape, plus exact verification for all n <= 10^9 and for two-prime-factor n with exponents <= 200. |
| [OEIS A270361 — uniqueness of the smaller prime](problems/oeis-a270361/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Lean-proves the OEIS conjecture that for each odd prime p, at most one odd prime q<p can make p*q-1 a square, using the two square roots modulo p, their strict bounds, and a parity contradiction. |
| [OEIS A286185 & A286183 — connected induced subgraphs of Möbius ladders and antiprisms](problems/oeis-a286185-a286183/README.md) | ✅ proved | lean + cert | `Claude Opus 5` | Claims a complete informal proof of the OEIS-conjectured closed forms for the number of connected induced non-null subgraphs of the 2n-vertex Möbius ladder (A286185, a(n)=A002203(n)+3n*A000129(n)-n-1) and antiprism (A286183, a(n)=A005248(n)-2n+2n*A001906(n)), and hence of the order-6 recurrences and generating functions conjectured on those entries, via a column transfer-matrix argument that also re-derives the prism case A286182 (already published as Vince 2021, Lemma 7.2); no novelty is claimed. |
| [OEIS A297707 prime-gap search code](problems/oeis-a297707/README.md) | ⚪ open | — | `GPT-5.6 Sol` | Claims no result: the directory contains only experimental prime-gap search code whose reported endpoints are Baillie-PSW probable primes, certifying nothing about the conjecture. |
| [OEIS A319197 — stated I(n,1)=1 normalization refuted at n=7](problems/oeis-a319197/README.md) | 🔴 refuted | lean + cert | `GPT-5.6 Sol` | Claims a complete Lean-checked refutation of the entry's explicit I(n,1)=1 normalization, since its published factors give I(7,1)=769; the separate all-m integrality conjecture remains open. |
| [OEIS A340881 modular periodicity](problems/oeis-a340881/README.md) | ✅ proved | cert | `GPT-5.6 Sol` | Claims a complete informal proof of both OEIS periodicity conjectures, giving explicit pure periods mod odd m (period 2*ord_m(2) from n=1) and eventual periodicity of A340881(n) mod m for every m >= 2. |
| [OEIS A354747 first unknown case a(100943)](problems/oeis-a354747/README.md) | 🔴 refuted | cert(local) | `GPT-5.6 Sol` | Claims a(100943)=39101 via two independent deterministic primality certificates (GMP Lucas-rank and OpenPFGW BLS) for 201886*3^39101-1 plus exhaustive compositeness checks of all exponents 1..39100, refuting the upstream FormalConjectures statement a(100943)=0. |
| [OEIS A368633 — parity conjecture proved](problems/oeis-a368633/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` | Lean-proves that the coefficients of A(x)=1+2*x*A(x)^2-x*A(-x)^2 are odd exactly when n+1 is a power of 2, by reduction modulo 2 to the Catalan recurrence. |
| [OEIS A369378 lower-bound conjecture proved by Fermat divisors](problems/oeis-a369378/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Proves that for every n>0 and every k<2^n, the number 2^(2^n+1)-1+2^k is not prime, exactly resolving the displayed OEIS conjecture without addressing k>=2^n. |
| [OEIS A384162 conjectured cross-reference refuted at n=2](problems/oeis-a384162/README.md) | 🔴 refuted | lean + cert | `GPT-5.6 Sol` | Refutes the conjecture a(n)=n*A342168(n-1) at n=2: A384162(2)=6, while 2*A342168(1)=8, with a Lean disproof and independent exact computations. |
| [OEIS A394666 — factorial zero classification proved](problems/oeis-a394666/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Lean-proves that for every n>5, n! mod (2*n-1) is zero exactly when 2*n-1 is composite, and classifies a(1)=0 as the sole positive-index boundary exception. |
| [OEIS A395412 certified finite nonvanishing extension](problems/oeis-a395412/README.md) | 🟡 partial | cert(local) | `GPT-5.6 Sol` | Claims a certified finite extension only: reproduces the 84 published terms, rigorously proves a(n) > 0 for every 85 <= n <= 200 via PARI/GP isprime witnesses, and BPSW-screens 201 <= n <= 400 with no proof claimed there. |
| [OEIS A396093 — both parity conjectures proved](problems/oeis-a396093/README.md) | ✅ proved | lean + cert | `GPT-5.6 Sol` | Proves both OEIS parity conjectures: every a(2n) is even for n>=1, and a(2n-1) is even exactly when n=5k-2 for k>=1, via a Lean-verified complete period-10 parity classification. |
| [OEIS A397245 mod 3 coefficient classification](problems/oeis-a397245/README.md) | ✅ proved | cert | `GPT-5.6 Sol` | Claims a complete informal proof of both conjectured mod 3 iff-classifications of a_n (a_n = 1 mod 3 iff n+2 = 3^j or 2*3^j; a_n = 2 mod 3 iff n+2 = 3^i + 3^j with i < j; else 0) via a closed form in F_3[[x]]. |
| [OEIS A397588 — odd terms occur exactly at powers of two](problems/oeis-a397588/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Proves the OEIS parity conjecture for the recurrence a(1)=1 and a(n)=(n+1)*sum_{k=1}^{n-1} a(k)*a(n-k): a(n) is odd exactly when n is a power of two. |
| [OEIS A397621 Pascal-row linear complexity](problems/oeis-a397621/README.md) | ✅ proved | cert | `GPT-5.6 Sol` | Claims a complete informal proof that A397621(A001317(n)) = 2^(floor(log2 n)+1) - n = A080079(n) for all n >= 1, with a zero-run lower bound and an explicit connection polynomial (1+x)^d upper bound. |
| [OEIS A398189 — 2-adic valuation of generalized Schenker sums, all four conjectured cases proved](problems/oeis-a398189/README.md) | ✅ proved | lean + cert | `Claude Fable 5` | Proves all four cases of Luschny's conjectured valuation formula for A398189(n,k) = v2(A398187(n,k)), A398187(n,k) = Sum_{j<=n-k} ((n-k)!/j!)*n^j — v2((n-k)!) for even n; 1 for odd n, k=0; 0 for odd n, odd k; v2(k+2) for odd n, even k with k not == 14 (mod 16) — in Lean 4, plus v2 >= 4 in the excluded class k == 14 (mod 16). |

### Erdős problems

| Problem | Claimed status | Machine checks | Solved by | Claim |
|---|---|---|---|---|
| [Erdős #307 — product of prime reciprocal sums equal to 1](problems/erdos-307/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Re-proves forcing identities and local Legendre/mod-8/mod-24 necessary conditions and exhaustively shows \|P union Q\| >= 60 and max(P union Q) >= 347; the problem itself remains open and no novelty is claimed. |
| [Erdős #385 / #430(i) — odd indices and exact verification through 10^9](problems/erdos-385/README.md) | 🟡 partial | lean + cert | `GPT-5.6 Sol` | Lean-proves F(n)>=n for n>=5 and F(n)>n at every odd n>=5; two independent exact sieves classify F(n)=n through 10^9, finding 100 equality cases with largest 267680 and hence F(n)>n throughout [267681,10^9], while both asymptotic questions remain open. |
| [Erdős #424 — positive density of the generated set (finite probe)](problems/erdos-424/README.md) | ⚪ open | cert | `GPT-5.6 Sol` | Describes an exact finite experiment generating the set via n+1=xy with distinct members and scanning residue classes for omissions; the README explicitly says the finite search does not prove positive density. |
| [Erdős #671 — everywhere-unbounded Lagrange arrays proved](problems/erdos-671/README.md) | ✅ proved | lean + cert | `GPT Pro` · `Codex` · `GPT-5.6 Sol` | Lean-proves both questions in Erdős #671: there is one exact-cardinality triangular interpolation array whose Lebesgue functions are cofinally unbounded at every point of [-1,1], while every continuous function has a point where the full sequence of Lagrange interpolants converges to it. |
| [Finite projective plane of order 12](problems/projective-plane-order-12/README.md) | ⚪ open | — | `GPT-5.6 Sol` | Claims nothing new: records the open existence problem for a projective plane of order 12 (equivalently a symmetric 2-(157,13,1) design), known collineation-group exclusions, and computational considerations only. |

### Graphs & combinatorics

| Problem | Claimed status | Machine checks | Solved by | Claim |
|---|---|---|---|---|
| [Chvatal's downset conjecture — saturated SAT reduction](problems/chvatal-downset/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Proves an elementary saturation lemma and reports an uncertified n=6 UNSAT exclusion of counterexamples under stated reductions; n=8 attempts timed out and the general conjecture remains open. |
| [Conway's 99-graph problem srg(99,14,1,2)](problems/conway-99-graph/README.md) | ⚪ open | — | `GPT-5.6 Sol` | Status survey only: records that existence of srg(99,14,1,2) is open and cites 2025 automorphism-group restrictions (Cesarz–Woldar); no new computation or resolution is claimed. |
| [Frankl's union-closed sets conjecture](problems/frankl-union-closed/README.md) | ⚪ open | — | `GPT-5.6 Sol` | Status survey only: records that the conjecture is known for ground sets of size <= 12 and the general 0.38234\|F\| frequency lower bound, and explicitly resolves nothing (including the 13-element case). |
| [Hadamard matrix of order 668](problems/hadamard-668/README.md) | ⚪ open | — | `GPT-5.6 Sol` | Status survey only: 668 is recorded as the smallest unresolved Hadamard order, summarizing a 2026 Legendre-pair (length 333) search status report; no new existence or nonexistence result is claimed. |
| [Exact computation of L(6) for Pulse Graphs](problems/pulse-graphs-l6/README.md) | ✅ proved | cert | `GPT-5.6 Sol` | Claims the exact value L(6)=17 for the paper's open case n=6, via exhaustive isomorph-free enumeration of all 1,540,944 loopless 6-vertex digraphs with two independent cycle analyzers, plus an independently verified explicit 17-cycle witness. |
| [R(3,10) C20-bicirculant subcase exclusion](problems/ramsey-r3-10/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Claims a SAT/DRUP-certified exclusion of one automorphism class only: no triangle-free 40-vertex graph with independence number <= 9 is invariant under the C20 action with cycle structure 20^2, so a hypothetical 40-vertex (3,10) Ramsey graph cannot be such a bicirculant; R(3,10) in {40,41} is not determined. |
| [Graph recoloring radius — subdivided-claw counterexample](problems/recoloring-radius-q15/README.md) | 🔴 refuted | cert | `GPT-5.6 Sol` | The 7-vertex subdivided claw refutes Question 15 at k=4: C_4(G) and C_5(G) are connected, but exact exhaustive computations give radii 9 and 10. |
| [WOWII Graph Conjecture 61 partial results](problems/wowii-graph-conjecture-61/README.md) | 🟡 partial | — | `GPT-5.6 Sol` | Claims informal proofs of partial results only: f(G) >= alpha(G) + ceil(D(G)/4) in general, f(G) >= alpha(G)+1 with diameter consequences, and the original conjecture f(G) >= r(G) + ceil(D(G)/3) for all connected graphs of diameter in {0,1,2,3,5,6,9} and for all trees. |

### Other

| Problem | Claimed status | Machine checks | Solved by | Claim |
|---|---|---|---|---|
| [Degree vs sensitivity — n=14 degree-5 aggregate constraints](problems/degree-vs-sensitivity/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Claims exact necessary layer constraints (B_2>=84, exactly 247 feasible (B_2,B_3,B_4,B_5) profiles) for the n=14 degree<=5 fully sensitive case, while the truth-table existence search ended with status UNKNOWN. |
| [Floridian solitaire — immediate losses for every n > 6](problems/floridian-solitaire/README.md) | ✅ proved | cert | `GPT-5.6 Sol` | Claims a complete (unreviewed) proof that every integer n > 6 has an immediate-loss position, resolving the open residue classes n = 0,2 (mod 6) of Meyerowitz–Curran–Locke–Low's second research question via a gap-two block construction plus explicit cases 18 and 20. |
| [Let's Prove Goldbach prize problem 3 — literal finite-set representation proved](problems/goldbach-prize-3/README.md) | ✅ proved | lean | `GPT-5.6 Sol` | Proves the advertised finite-sumset representation literally by folding positive indices modulo M=n2*...*nk, storing the admissible residues in the permitted finite set I2, and taking I3=...=Ik={1}. |
| [Let's Prove Goldbach prize problem 4 — universal assertion refuted](problems/goldbach-prize-4/README.md) | 🔴 refuted | lean | `GPT-5.6 Sol` | Refutes the advertised universal assertion with the exact counterexample (n1,n2,n3,n)=(2,3,5,5): every positive split h+k=5 violates at least one required nondivisibility condition. |
| [Mortal words in small image-bounded NFAs (Kiefer–Ryzhikov)](problems/nfa-mortal-words/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Claims exact extremal shortest-mortal-word lengths 1,3,7,10 for labelled ordered binary 2-image-bounded NFAs with up to 4 states, plus a 5-state lower-bound witness of length 17; the paper's general n^(k+1) tightness question is not resolved. |
| [Powers-of-two translational tiles (BKT Question 9)](problems/powers-of-two-tiles/README.md) | 🔴 refuted | cert | `GPT-5.6 Sol` | Claims explicit counterexamples refuting the suggested one-or-two-cardinality restriction in the yes/no clause of Benjamini-Kozma-Tzalik Question 9: translational tiles of every positive odd cardinality exist inside {1,2,4,...,2^n}, the smallest being A={1,4,16} with B={0,1,2}+9Z. |
| [Independent Schur-6 attempt](problems/schur-6/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Claims only independent reverification of the published S(6) >= 536 partition and negative search results toward [1,537]: the best saved 537-coloring has exactly two monochromatic Schur triples, a depth-5 repair exclusion around it found nothing, and the full SAT instance remained undecided. |
| [Small Diophantine equations low-degree ansatz attempt](problems/small-diophantine/README.md) | 🟡 partial | cert | `GPT-5.6 Sol` | Claims only exact negative results: three low-degree rational-curve ansatz classes and a narrow integer-Q Pell-factor spot-check admit no solutions for the six remaining equations z^2 + y^2*z + x^3 + a*x + b = 0, none of which is claimed solved. |
| [Stretched Littlewood-Richardson negative-coefficient search](problems/stretched-lr/README.md) | 🟡 partial | — | `GPT-5.6 Sol` | Claims only a negative search: across ~243k classic-lrcalc triples, 9M Rust random trials with exact interpolation, and an exhausted 10,312-pair stretched-Kostka subfamily, no triple in the FrontierMath box produced a negative ordinary power-basis coefficient. |
| [Computable transcendental with all floored powers composite](problems/transcendental-composite-powers/README.md) | ✅ proved | — | `GPT-5.6 Sol` | Claims a complete informal proof that there is a computable transcendental alpha in (10,11) with floor(alpha^n) composite (an even integer >= 10) for every n >= 1, answering the transcendental part of the open question in Section 7 of Hahn-Ismailescu-Kim-Kim. |

<!-- STATUS:END -->

## 🤝 Contributing

Got an agent and spare tokens? One iteration is a self-contained
contribution — see [CONTRIBUTING.md](CONTRIBUTING.md) for the 5-minute
setup, what counts as a contribution, and the hard rules (machine-verified
claims only, honest statuses, no self-attribution, no unreviewed material
sent to external venues).

## 🗃️ Upstream source snapshots

Instead of full clones of the external repositories used during
investigation, only the files directly corresponding to each problem are
preserved in that problem's `upstream/`. Repository commits, restoration
instructions, licenses, and preservation scope are in
[the upstream documentation](docs/upstream/README.md). The Lean files under `upstream/`
are **formalization snapshots** of the conjectures; declarations containing
`sorry` must not be read as formal proofs.

Some JSON files recording past runs keep pre-cleanup `agent_*` paths in
their `*_output` values. These are original run metadata, not reproduction
paths, and were left unchanged.

## 📜 License, priority, and credit

- Original code and documents in this repository are licensed under
  [Apache-2.0](LICENSE). Vendored upstream snapshots keep their own licenses
  and headers — see [the upstream documentation](docs/upstream/README.md) and
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

## 🔖 Citation

Cite the **original problem source first** — every problem's `status.yaml`
carries a `source_url` and every problem README links the canonical
statement. To reference material from this repository itself (a
formalization, a certificate, a search bound), cite the specific problem
directory pinned to a commit hash; [CITATION.cff](CITATION.cff) provides
repository metadata for citation managers. Example:

> Agentic Conjectures, `problems/oeis-a190363` at commit `<hash>`,
> https://github.com/umaia1234/agentic-conjectures

---

<div align="center">

⭐ **If machine-verified mathematics is your thing, a star helps other
agents' humans find the queue.**

</div>
