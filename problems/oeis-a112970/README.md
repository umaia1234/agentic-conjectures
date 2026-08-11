**English** | [한국어](README.ko.md)

# OEIS A112970 — power-of-two identities

## Verdict

Both conjectured chains are **proved** for every natural number $n$:

\[
a(2^n)=a(2^{n+1}+1)=\left\lfloor\frac{n^2}{4}\right\rfloor+1
\]

and

\[
a(2^n-1)=a(3\cdot2^n-1)=1.
\]

The first closed form is OEIS A033638. The result is formalized in Lean 4 and
checked without `sorry`, extra axioms, or `native_decide`.

## Canonical statement and prior art

[OEIS A112970](https://oeis.org/A112970), checked on 2026-08-12, defines
$a(0)=a(1)=1$, sets $a(m)=0$ at negative indices, and gives

\[
a(2m+1)=a(m),\qquad a(2m)=a(m)+a(m-2).
\]

At offset 0 it records the two chains above as conjectures. Its referenced
[A033638](https://oeis.org/A033638) is the quarter-square sequence
$\lfloor n^2/4\rfloor+1$.

The recurrence itself has published provenance. Theorem 4.1 of Northshield,
[“Sums across Pascal's triangle modulo
2”](https://soar.suny.edu/bitstreams/d770f1ab-549e-49a1-8442-f2f266ff36ed/download)
(Congressus Numerantium 200 (2010), pp. 35–52; theorem on preprint p. 14),
specializes at $(a,b)=(4,1)$ to exactly these odd and even recurrences. The
paper does not state A112970, A033638, the quarter-square formula, or any of
the special-index chains. The three claims involving only odd recurrence
steps are immediate corollaries; the quarter-square clause requires the
additional argument below.

A targeted prior-art check on 2026-08-12 searched the exact OEIS identifier,
the full displayed equation, the quarter-square formula, GitHub history and
code, and the public AlphaProof Nexus result tree. It found no earlier proof
of the closed form. [Formal Conjectures PR
#4450](https://github.com/google-deepmind/formal-conjectures/pull/4450) remains
open at the preserved commit: its three `sorry`-ending statements omit the
A033638 clause altogether. These are negative search results, not a
literature review or a novelty claim. This proof is unreviewed and has not
been submitted externally.

## Proof

The odd recurrence immediately gives

\[
a(2^{n+1}+1)=a(2^n).
\]

It also reduces $2^{n+1}-1$ to $2^n-1$ and
$3\cdot2^{n+1}-1$ to $3\cdot2^n-1$. Their respective base indices are 0 and
2, both with value 1, proving the second chain by induction.

For the missing closed form, put

\[
r_n=a(2^{n+1}-2).
\]

Writing $2^{n+3}-2=2(2^{n+2}-1)$, apply the even recurrence at this index and
then the odd recurrence to its second summand. This gives

\[
r_{n+2}=r_n+1.
\]

The bases $r_0=r_1=1$ therefore yield

\[
r_n=\left\lfloor\frac{n+2}{2}\right\rfloor.
\]

Now let $b_n=a(2^n)$. For $n\ge1$, the even recurrence gives

\[
b_{n+1}=b_n+a(2^n-2)
       =b_n+\left\lfloor\frac{n+1}{2}\right\rfloor.
\]

Starting from $b_0=1$ and using

\[
\left\lfloor\frac{(n+1)^2}{4}\right\rfloor
=\left\lfloor\frac{n^2}{4}\right\rfloor
 +\left\lfloor\frac{n+1}{2}\right\rfloor
\]

proves $b_n=\lfloor n^2/4\rfloor+1$. Lean proves the floor identity by the
even/odd decomposition of $n$.

## Statement faithfulness

[`AgenticConjectures/OeisA112970.lean`](../../AgenticConjectures/OeisA112970.lean)
copies the recursive definition from the pinned Formal Conjectures source,
apart from namespace, comments, and benchmark attributes. Its natural-number
guard returns zero when the even recurrence asks for $a(k-2)$ with $k<2$;
this exactly implements the OEIS convention $a(m)=0$ for negative $m$ and is
used at the $a(-1)$ boundary.

All theorem parameters range over $n\ge0$, matching the OEIS offset. Natural
division by 4 is floor division, so
`power_of_two_eq_a033638` states exactly
$a(2^n)=\lfloor n^2/4\rfloor+1$. The pinned upstream file formalizes only the
other three equalities; the A033638 theorem follows the canonical OEIS entry
and deliberately fills that omission.

## Machine verification and reproduction

The registered Lean theorems prove the universal claims. The standard-library
Python script independently evaluates the recurrence on integer indices,
including negative inputs, and checks both chains for $0\le n\le64$. This
finite audit is a transcription guard, not a substitute for the proof.

From the repository root, run:

```bash
lake build AgenticConjectures.OeisA112970
python3 problems/oeis-a112970/verify_identities.py --max-exponent 64
```

On the 2026-08-12 development run, the Python audit checked 377 memoized
recurrence states in 0.09 seconds. Repository CI also builds the module,
audits its axioms, and reruns the finite audit.
