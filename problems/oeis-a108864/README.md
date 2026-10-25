**English** | [한국어](README.ko.md)

# OEIS A108864: 1155 is not the last odd term

## Verdict

[OEIS A108864](https://oeis.org/A108864) lists the numbers whose perfect
deficiency ([A109883](https://oeis.org/A109883)) is at most 10. Its only
comment asks:

> “Is 1155 the last odd number in this sequence?”

The answer is **no**. The odd number

\[
n_0=815634435=3\cdot5\cdot7\cdot11\cdot547\cdot1291
\]

has

\[
\sigma(n_0)=4\cdot6\cdot8\cdot12\cdot548\cdot1292=1631268864=2n_0-6,
\]

so its perfect deficiency is \(6\le10\). It is therefore a term after 1155.
The Formal Conjectures statement `OeisA108864.conjecture : ∀ n > 58, Even (a n)`
is false. `AgenticConjectures.OeisA108864.not_statement` proves its negation
in Lean 4, and an independent Python certificate rechecks the witness.

## Source statement

OEIS A108864 (revision #3, last edited Dec 15 2017; entry by Jason Earls,
Jul 12 2005), checked on 2026-10-24:

> Numbers n such that the perfect deficiency of n (A109883) is <= 10.
>
> Is 1155 the last odd number in this sequence?

The entry has offset 1 and 61 data terms, ending
`…, 1012, 1024, 1155, 1188, 1248`, so \(a(59)=1155\).
OEIS A109883 (revision #28) defines the perfect deficiency:

> Start subtracting from n its divisors beginning from 1 until one reaches a
> number smaller than the last divisor subtracted or reaches the last
> nontrivial divisor < n. Define this to be the perfect deficiency of n.

Its PARI program is
`a(n) = {my(r = n); fordiv(n, d, if (r < d, return (r)); r -= d;); 0;}`.

The [upstream snapshot](upstream/README.md)
(`FormalConjectures/OEIS/108864.lean` at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`) states:

```lean
def perfectDeficiency (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n

def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

theorem conjecture :
    ∀ n > 58, Even (a n) := by
  sorry
```

## Proof

**Key lemma.** Let \(n\ge2\), and let \(s(n)=\sigma(n)-n\) be the sum of the
proper divisors of \(n\). If \(s(n)\le n\), then `perfectDeficiency n`
\(=n-s(n)=2n-\sigma(n)\).

The fold visits \(d=0,1,\ldots,n\) and changes the remainder only at
divisors of \(n\). Suppose that every divisor below a proper divisor \(d\)
has been subtracted. The remainder is then
\(n-\sum_{d'<d,\ d'\mid n}d'\), which is at least \(d\) because
\(\sum_{d'\le d,\ d'\mid n}d'\le s(n)\le n\). So \(d\) is subtracted too. By
induction every proper divisor is subtracted, which leaves \(n-s(n)\). This
remainder is smaller than \(n\) because \(1\) is a proper divisor, so the
last candidate \(d=n\) is skipped.

**The witness.** \(n_0\) is squarefree with the six prime factors shown
above. By multiplicativity,
\(\sigma(n_0)=(3+1)(5+1)(7+1)(11+1)(547+1)(1291+1)=1631268864\), so
\(s(n_0)=815634429\le n_0\). The lemma gives perfect deficiency
\(n_0-s(n_0)=6\). Hence `A n₀` holds, and \(n_0\) is odd.

**The index.** `Nat.nth_count` gives `a (Nat.count A n₀) = n₀`. The 59
numbers \(1,2,\ldots,1155\) from the OEIS data are members of `A` below
\(n_0\), which kernel evaluation of the upstream fold checks. Hence
`Nat.count A n₀ ≥ 59 > 58`, and `conjecture` fails at index
`Nat.count A n₀`.

## Lean formalization

[`AgenticConjectures/OeisA108864.lean`](../../AgenticConjectures/OeisA108864.lean),
namespace `AgenticConjectures.OeisA108864`:

| Declaration | Content |
|---|---|
| `perfectDeficiency`, `A`, the `DecidablePred A` instance, `a` | the upstream definitions, term for term |
| `statement` | the type of upstream `conjecture`: `∀ n > 58, Even (a n)` |
| `foldl_range_eq` | if the proper divisors of `n` sum to at most `n`, then after the candidates `0, …, k - 1` (`k ≤ n`) the fold has subtracted exactly the divisors below `k` |
| `perfectDeficiency_eq` | key lemma: `2 ≤ n` and `∑ d ∈ n.properDivisors, d ≤ n` imply `perfectDeficiency n = n - ∑ d ∈ n.properDivisors, d` |
| `sigma_one_prime`, `sigma_witness` | \(\sigma(p)=p+1\) for prime \(p\); \(\sigma(815634435)=1631268864\) by multiplicativity |
| `sum_properDivisors_witness`, `perfectDeficiency_witness`, `A_witness` | the proper divisors of the witness sum to 815634429; its perfect deficiency is 6; `A 815634435` |
| `firstTerms`, `firstTerms_spec` | the 59 terms `1, …, 1155`: pairwise distinct, in `A`, and below the witness (`decide +kernel`) |
| `count_witness`, `a_count_witness` | `58 < Nat.count A 815634435` and `a (Nat.count A 815634435) = 815634435` |
| `not_statement` | **main theorem:** `¬ statement` |

`#print axioms AgenticConjectures.OeisA108864.not_statement` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The module contains no
`sorry` and no `native_decide`. The only large kernel evaluation is
`firstTerms_spec`, which takes about 11,500 fold steps. The fold is never
evaluated on the witness itself.

## Statement faithfulness

- **Definitions.** `perfectDeficiency`, `A`, the `DecidablePred A` instance,
  and `a` are copied term for term from the upstream snapshot, under the same
  `open Nat Finset Int`. `statement` is the type of upstream `conjecture`.
  Compiling without the Formal Conjectures utilities required three changes:
  - `import Mathlib` replaces `module`, `public import FormalConjecturesUtil`,
    and `@[expose] public section`;
  - the namespace gains the prefix `AgenticConjectures.`;
  - the `category`/`AMS` attributes and the five `test` theorems are dropped.

  None of these changes affects a proposition. As a check, the five upstream
  test proofs `a_0`–`a_4` were run verbatim (without their attributes)
  against the local definitions, and all of them succeed.
- **Index base.** `Nat.nth` is 0-indexed, so upstream `a 58` is OEIS
  \(a(59)=1155\), and `∀ n > 58` means “every term after 1155”. The
  certificate checks that exactly 59 terms are \(\le1155\), which confirms
  upstream's `a 58 = 1155`. The Lean proof does not need this fact; it needs
  only that at least 59 terms lie below the witness. A direct kernel
  computation of `Nat.count A 1155 = 58` exceeds Lean's default heartbeat
  budget, so the index base is checked only in Python.
- **The literal OEIS question.** Indexing aside, `A_witness` together with
  \(n_0\) being odd and \(n_0>1155\) shows directly that 1155 is not the last
  odd term.
- **Natural-number subtraction.** The fold computes `m - d` only under the
  guard `d ≤ m`, so the subtraction never truncates. In the key lemma,
  `n - ∑ d ∈ n.properDivisors, d` is a true difference under the lemma's
  hypothesis.
- **Boundary values.** `0 < n` excludes 0. For \(n=1\) the candidate
  \(d=n=1\) is subtracted, so the perfect deficiency is 0, matching
  A109883's \(a(1)=0\). This is why the key lemma assumes \(n\ge2\).
- **Upstream fold versus A109883.** Upstream skips any divisor larger than
  the remainder and continues; the A109883 PARI program stops at the first
  such divisor. The two agree because the divisors are visited in increasing
  order and the remainder never increases, so once one divisor is skipped,
  every later divisor is skipped too. The certificate confirms that the two
  agree for \(1\le n\le2000\) and reproduces all 61 OEIS data terms. The
  refutation itself uses only the upstream definition, and both semantics
  give 6 for \(n_0\).

## Machine verification and reproduction

From the repository root:

```bash
lake build AgenticConjectures.OeisA108864
python3 problems/oeis-a108864/a108864_certificate.py
```

On 2026-10-24 (Apple M5 Max, Mathlib already built), the module compiled in
about 7 seconds and the certificate ran in about 0.15 seconds.

The [certificate](a108864_certificate.py) uses only the Python standard
library and is independent of the Lean proof. It:

- transcribes the upstream fold literally, including Lean's
  `0 ∣ n ↔ n = 0`, and compares it with the A109883 PARI program for
  \(1\le n\le2000\);
- recomputes the OEIS data terms up to 1248, the index base
  \(a(58)=1155\) (0-indexed), and the Lean `firstTerms` list;
- factors \(n_0\) by trial division, proves the six factors prime by trial
  division, enumerates the 64 divisors in two independent ways, and checks
  \(\sigma(n_0)=\prod_{p\mid n_0}(p+1)=2n_0-6\);
- evaluates the perfect deficiency of \(n_0\) under both semantics and checks
  the parity and the index bound.

## What is not claimed

- The exact index of \(n_0\), that is, the value of
  `Nat.count A 815634435`, is not determined. Only the bound \(>58\) is
  proved.
- It is not claimed that \(n_0\) is the smallest odd term after 1155.
- Nothing is claimed about whether A108864 has finitely or infinitely many
  odd terms.

## Prior art and submission status

The arithmetic fact \(\sigma(n_0)=2n_0-6\) has long been known. \(n_0\)
appears in [A087485](https://oeis.org/A087485) (odd \(m\) with
\(2m-\sigma(m)=6\)), [A141548](https://oeis.org/A141548) (deficiency 6),
[A077374](https://oeis.org/A077374) (odd \(m\) with
\(|\sigma(m)-2m|\le10\)), and [A088012](https://oeis.org/A088012). Given the
key lemma, its membership in A108864 follows in one line. On 2026-10-24, the
A108864 entry still asked the question. None of the 15 OEIS entries that
contain 815634435 mentions A108864, and no other entry cross-references
A108864. This search is not evidence of novelty. The result is unreviewed,
no novelty is claimed, and nothing has been submitted to OEIS, Formal
Conjectures, or any other external venue; such submissions need human
approval.
