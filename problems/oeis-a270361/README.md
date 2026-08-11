**English** | [한국어](README.ko.md)

# OEIS A270361 — uniqueness of the smaller prime

## Verdict

The conjecture recorded in [OEIS A270361](https://oeis.org/A270361) is
**true**:

> Conjecture: For any odd prime p there is at most one odd prime q, with q <
> p, for which p*q-1 is square.

Equivalently, if $p,q_1,q_2$ are odd primes, $q_1,q_2<p$, and

\[
p q_1-1=x_1^2,\qquad p q_2-1=x_2^2,
\]

then $q_1=q_2$. The result is universal; it is not a finite-range search.

The quoted text is from OEIS revision 38 (2024-02-25), checked again on
2026-08-12. The entry still marked it as a conjecture at that check.

## Proof

First, $0<x_i<p$. Positivity follows from the primality of $p$ and
$q_i$, while $q_i<p$ gives

\[
x_i^2=pq_i-1<p^2.
\]

Both square equations give $x_i^2 \equiv -1 \pmod p$. Therefore

\[
p\mid(x_1^2-x_2^2)=(x_1-x_2)(x_1+x_2).
\]

Because $p$ is prime, either $x_1 \equiv x_2 \pmod p$ or
$x_1 \equiv -x_2 \pmod p$. The bounds $0<x_1,x_2<p$ turn the first case
into $x_1=x_2$, and the second into $x_1+x_2=p$.

The second case is impossible: $p$ and $q_i$ are odd, so
$x_i^2=pq_i-1$ is even and hence each $x_i$ is even. Thus $x_1+x_2$
is even, whereas $p$ is odd. We must have $x_1=x_2$, and the two square
equations then give $pq_1=pq_2$. Since $p>0$, cancellation yields
$q_1=q_2$.

Notice that primality of the candidate $q_i$ is not needed at all: its
assumed oddness already supplies positivity. The argument actually proves
uniqueness among all positive odd $q<p$.

## Lean formalization and statement faithfulness

[`AgenticConjectures/OeisA270361.lean`](../../AgenticConjectures/OeisA270361.lean)
formalizes “at most one” as pairwise uniqueness and proves

```text
oeis_a270361_conjecture : statement
```

without `sorry`, extra axioms, or `native_decide`. The exported statement
uses the literal OEIS equation $pq-1=x^2$. Internally, the proof converts it
to the subtraction-safe equation

\[
pq=x^2+1
\]

to avoid truncated subtraction on natural numbers. Lean proves this
conversion from the positivity of the source's odd primes. The formal
statement keeps all source restrictions: $p$ and $q$ are prime,
both are odd, $q<p$ is strict, and $q=2$ is excluded. OEIS's sequence
offset `1,1` is irrelevant because the conjecture concerns uniqueness of a
membership witness, not the value of $a(n)$.

## Reproduction

From the repository root, run the complete verification suite with:

```bash
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
```

Measured on the final local tree on 2026-08-12:

| Gate | Runtime |
|---|---:|
| `check_imports.py` | 0.02 s |
| `check_sorry.py` | 0.02 s |
| `lake build` | 17.45 s |
| `check_axioms.py` | 4.54 s |
| `verify_all.py --ci` | 96.97 s (32 checks passed) |
| `gen_readme.py --check` | 0.09 s |

The certificate suite requires `drat-trim` on `PATH`, as documented by the
repository's CI workflow. CI repeats these checks from the pinned Lean
4.30.0/mathlib 4.30.0 environment.

## Prior-art check and research status

Targeted searches on 2026-08-12 used the exact quotation, the OEIS ID, and
variants of “odd prime”, “at most one”, and “(pq-1) square”. They checked
the OEIS links and revision history, public GitHub code and pull requests,
and the current FormalConjectures tree. The only exact matches found were the
OEIS entry, mirrors, or programs enumerating the sequence; no proof was found.

[OEIS A000089](https://oeis.org/A000089) does record the classical general
fact that $x^2 \equiv -1 \pmod p$ has two roots when the odd prime
$p \equiv 1 \pmod 4$.
The argument above is an elementary application of that standard root
structure together with the parity forced by $pq-1=x^2$. Accordingly, this is
presented as a machine-checked settlement of the still-labelled OEIS
conjecture, not as a novel theorem. The search is bounded public evidence,
not a literature review; no novelty or priority is claimed. The proof is
unreviewed and has not been submitted to OEIS or any other external venue.
