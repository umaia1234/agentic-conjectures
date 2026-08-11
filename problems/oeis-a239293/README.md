**English** | [한국어](README.ko.md)

# OEIS A239293

[OEIS A239293](https://oeis.org/A239293) defines \(a(n)\) as the least
composite number \(c>n\) such that

\[
n^c \equiv n \pmod c.
\]

The entry states the following conjecture:

> Conjecture: a(n) = n+1 if and only if n+1 is an odd composite number.

## Result

The conjecture holds for every official sequence index \(n\ge 1\).

Put \(m=n+1\). Modulo \(m\), we have \(n\equiv-1\). If \(m\) is odd and
composite, then

\[
n^m\equiv(-1)^m=-1\equiv n\pmod m.
\]

Thus \(m\) is a qualifying composite, and it is automatically the least one
because no natural number lies strictly between \(n\) and \(n+1\).

Conversely, suppose \(a(n)=m\). Then \(m\) is composite and satisfies the
congruence. If \(m\) were even, the same residue calculation would give
\(n^m\equiv1\pmod m\), while the defining congruence gives
\(n^m\equiv-1\pmod m\). Hence \(m\mid2\), which is impossible for a composite
\(m>1\). Therefore \(m\) is odd.

## Lean formal proof

[`AgenticConjectures/OeisA239293.lean`](../../AgenticConjectures/OeisA239293.lean)
formalizes the sequence's least-candidate definition and proves, without
`sorry`, extra axioms, or `native_decide`:

```text
a_eq_succ_iff_odd_composite :
  ∀ n ≥ 1, a n = n + 1 ↔ Odd (n + 1) ∧ 1 < n + 1 ∧ ¬(n + 1).Prime
```

The definition uses the infimum of the qualifying natural numbers. This is an
attained minimum, not a default value for an empty set: the supporting theorem
`weakPseudoprimeAbove_nonempty` invokes mathlib's
`Nat.exists_infinite_pseudoprimes`, which supplies an arbitrarily large Fermat
pseudoprime for every positive base. Such a Fermat pseudoprime also satisfies
the weaker congruence used by A239293.

## Statement faithfulness

- The Lean theorem begins at \(n=1\), exactly matching the OEIS offset.
- “Composite” is represented by \(1<c\) and `¬c.Prime`.
- The condition \(n^c\equiv n\pmod c\) is equality in `ZMod c`, an equivalent
  representation of ordinary congruence.
- `a n` is the least element of exactly the composites \(c>n\) satisfying that
  congruence; nonemptiness is proved for every \(n\ge1\).
- There is no upstream Lean snapshot for this entry. The canonical OEIS
  wording above is therefore preserved here and in the module docstring.

## Verification and research status

As of 2026-08-12, the live OEIS entry (revision 27, offset 1) still labels the
equivalence a “Conjecture” and attributes it to Thomas Ordowski (2018). The same
entry already records the sufficient direction: if `n` is even and `n+1` is
composite, then `a(n)=n+1`. The linked
[Numericana weak-pseudoprime page](https://numericana.com/answer/pseudo.htm#weak)
likewise states that every odd composite `m` is a weak pseudoprime to base
`m-1`. Thus this repository does not claim to discover that direction.

Exact-phrase, A-number, and public GitHub code searches found no standalone
proof of the full equivalence. The only relevant public code hit was
[a PARI term generator](https://github.com/gfis/OEIS-prog/blob/fb375daf77829667fb7d46a43f3856dbfc5e8702/prog/gp/a239/A239293.gp),
not a proof. That negative search does not establish novelty. The Lean proof
is unreviewed, has not been confirmed by an OEIS editor, and has not been
submitted externally.

From the repository root, the proof and repository-wide gates can be
reproduced with:

```bash
lake env lean AgenticConjectures/OeisA239293.lean
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
```

On the development machine, direct module elaboration took 16.88 seconds. A
recorded warm-cache run of the six repository gates took approximately 277
seconds in total: 0.24 seconds for import reachability, 0.24 seconds for the
no-sorry scan, 26.45 seconds for `lake build`, 38.45 seconds for the axiom
audit, 211.36 seconds for the 35 existing CI-feasible certificate checks, and
0.19 seconds for dashboard freshness. The certificate sweep used `drat-trim`
from upstream commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, built under `/tmp` and not
committed to the repository.
