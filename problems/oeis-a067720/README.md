**English** | [한국어](README.ko.md)

# OEIS A067720

## Partial theorem

The original problem asks whether \(k=8\) is the only solution of

\[
\varphi(k^2+1)=k\varphi(k+1)
\]

for which \(k+1\) is composite. This folder decides the following
subfamily in which \(k+1\) is a prime power.

> Let \(k+1=p^a\) with \(p\) prime and \(a\ge2\). If \(p=2\), there is
> no solution. If \(p\) is odd and
> \[
> V:=v_2(p^a-1)+v_2(p-1)\le5
> \]
> then the unique solution is \((p,a,k)=(3,2,8)\).

The proof is in [PROOF.md](PROOF.md). Both parts are now kernel-checked in
Lean (see the Lean section below), together with two extensions. The odd
case holds for \(V\le6\), and it holds for every \(V\) when \(k^2+1\) is a
product of two primes. These results do not treat general composite
\(k+1\). They also leave open the odd prime powers with \(V\ge7\) for which
\(k^2+1\) has at least three prime factors. They are therefore not a
resolution of the full original conjecture.

## Lean formalization

[`AgenticConjectures/OeisA067720.lean`](../../AgenticConjectures/OeisA067720.lean)
(namespace `AgenticConjectures.OeisA067720`) copies the upstream membership
predicate exactly. It proves the following without `sorry`, extra axioms,
or `native_decide`:

| Declaration | Content |
|---|---|
| `A` | the upstream predicate `OeisA67720.A`, term for term: `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)` |
| `power_two_add_one_not_solution` | \(p=2\): no member has \(k+1=2^a\) with \(a\ge2\) |
| `a_eight` | `A 8`, i.e. \(\varphi(65)=48=8\varphi(9)\), by kernel `decide` |
| `odd_prime_power_solution_of_two_prime_factors` | every \(V\): if \(k+1=p^a\) with \(p\) an odd prime and \(a\ge2\), `A k` holds, and \(k^2+1=qr\) with \(q,r\) prime, then \((p,a,k)=(3,2,8)\) |
| `odd_prime_power_solution_iff_of_two_adic_le_six` | **main theorem**: for \(k+1=p^a\) with \(p\) an odd prime, \(a\ge2\) and \(V\le6\), `A k ↔ p = 3 ∧ a = 2 ∧ k = 8` |
| `odd_prime_power_solution_iff_of_two_adic_le_five` | the odd-prime theorem of [PROOF.md](PROOF.md) (\(V\le5\)), as a corollary of the \(V\le6\) theorem |

### The power-of-two case

```text
power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k
```

The proof writes \(k=2t+1\) and \(k^2+1=2N\) with \(N\) odd. It then uses
\(\varphi(2N)=\varphi(N)\le N\) and proves the strict inequality

\[
N < k\,2^{a-1}=k\varphi(2^a),
\]

contradicting the defining A067720 equation.

### Odd prime powers

```text
odd_prime_power_solution_iff_of_two_adic_le_six {p a k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 6) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8

odd_prime_power_solution_of_two_prime_factors {p a k q r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a) (hA : A k) (hq : q.Prime)
    (hr : r.Prime) (hM : k ^ 2 + 1 = q * r) : p = 3 ∧ a = 2 ∧ k = 8
```

`odd_prime_power_solution_iff_of_two_adic_le_five` has the same form as the
first statement, with `≤ 5` in place of `≤ 6`.

The Lean proof follows [PROOF.md](PROOF.md). Write \(M=k^2+1\). The
equation reads \(\varphi(M)=k\,p^{a-1}(p-1)\). No prime factor of \(M\)
divides \(k\), \(p\) or \(p-1\), so \(M\) is squarefree (equation (2)).
Every prime factor of \(M\) is \(1\bmod 4\) (equation (3)), and
\(v_2(\varphi(M))=V\) (equation (5)). The Lean proof deviates from
PROOF.md's presentation in two places:

- Instead of counting \(\omega(M)\) through inequality (4), the proof peels
  off least prime factors (`Nat.minFac`): \(M=qm\), \(m=rs\), \(s=tu\).
  Squarefreeness makes each split coprime, so \(\varphi\) multiplies, and
  each prime factor contributes a factor \(4\). \(M\) is not prime. If
  \(s=1\), it has exactly two prime factors. If \(u\ne1\), then
  \(2^8\mid\varphi(M)\).
- In the two-prime case, PROOF.md uses that \(f(x)=x(S-x)\) is increasing
  on \([0,S/2]\). The Lean proof uses instead the equivalent integer
  inequalities \((x-q)(r-x)\ge0\) and \((q-x-1)(r-x-1)\ge0\). It then
  evaluates them with PROOF.md's estimates (8)–(12): at \(x=p\) when
  \(a\ge3\), and at \(x=p+1\) when \(a=2\) and \(p>3\).

The two-prime case never uses the bound on \(V\). This is why
`odd_prime_power_solution_of_two_prime_factors` holds for every \(V\).

**From \(V\le5\) to \(V\le6\).** This step is not in PROOF.md. Suppose
\(V=6\) and \(M=qrt\) has exactly three prime factors; every other case
is already excluded. We have \(v_2(\varphi(M))=\sum v_2(q_i-1)=6\), and each
term is at least \(2\). So every \(q_i\equiv5\pmod 8\), and
\(M\equiv5^3\equiv5\pmod 8\). On the other hand, \(p-1\mid p^a-1=k\) gives
\(v_2(p-1)\le v_2(k)\). So \(6=V\le2v_2(k)\), hence \(8\mid k\) and
\(M=k^2+1\equiv1\pmod 8\), a contradiction. The Lean proof splits this the
same way. If one of \(q,r,t\) is \(1\bmod 8\), then \(2^7\mid\varphi(M)\),
contradicting \(V\le6\). Otherwise the residues modulo \(8\) clash as above.

The same idea does not reach \(V=7\). There, three prime factors with
2-adic valuations \(2,2,3\) give \(M\equiv1\pmod 8\), which is consistent
with \(8\mid k\).

For orientation, here is \(V\) in terms of \(p\) and \(a\), by the standard
lifting-the-exponent lemma. This is not part of the Lean development.
\(V=2\) when \(p\equiv3\pmod 4\) and \(a\) is odd. \(V=1+v_2(p+1)+v_2(a)\)
when \(p\equiv3\pmod 4\) and \(a\) is even. \(V=2v_2(p-1)+v_2(a)\) when
\(p\equiv1\pmod 4\).

### Statement faithfulness

- `A k` is exactly the upstream proposition
  `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`; there is no sequence
  indexing or subtraction convention to translate.
- The hypotheses `2 ≤ a` and `k + 1 = 2 ^ a` are precisely the \(p=2\),
  \(a\ge2\) subfamily. They exclude the prime boundary case \(a=1\).
- In the odd-prime theorems, `p.Prime` and `p ≠ 2` say that \(p\) is an odd
  prime. `2 ≤ a` and `k + 1 = p ^ a` fix \(k=p^a-1\) with \(a\ge2\), again
  excluding the prime case \(a=1\).
- \(V\) is written as `padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1)`.
  Since \(p\ge3\), neither natural-number subtraction is truncated, and both
  arguments are nonzero. So `padicValNat 2` is the ordinary 2-adic
  valuation \(v_2\) on them.
- "The unique solution is \((3,2,8)\)" is encoded as the biconditional
  `A k ↔ p = 3 ∧ a = 2 ∧ k = 8` under these hypotheses. \((3,2,8)\) itself
  satisfies them (\(V=v_2(8)+v_2(2)=4\)), and `a_eight` checks
  \(\varphi(65)=8\varphi(9)\).
- In `odd_prime_power_solution_of_two_prime_factors`, the hypothesis
  `k ^ 2 + 1 = q * r` allows \(q=r\). The proof rules that case out by
  squarefreeness.
- Nothing here covers arbitrary composite \(k+1\), or the odd prime powers
  with \(V\ge7\) for which \(k^2+1\) has at least three prime factors. Nor
  does it cover the upstream universal claim that every member other than
  \(k=8\) has \(k+1\) prime.

## Status of the source and scope of verification

- [OEIS A067720](https://oeis.org/A067720) revision #18, checked on
  2026-08-11, asked "is \(8\) the only additional value?", and the
  [b-file](https://oeis.org/A067720/b067720.txt) provided the first
  10000 terms.
  The length of the b-file is not the range of the conjecture or of
  this proof.
- On the same day,
  [`67720.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)
  at FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670` likewise marked this
  statement as `category research open`.
- This folder contains no finite-search certificate. The power-of-two
  exclusion and the odd-prime \(V\le6\) classification are kernel-checked
  in Lean. The latter contains the \(V\le5\) theorem of
  [PROOF.md](PROOF.md); its \(V=6\) step is described above and is not part
  of PROOF.md.
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub at the time, but this is
  only a negative search result. We do not assert novelty before peer
  review.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`67720.lean`](upstream/67720.lean). The global statement that `k+1` is
prime except for `k=8` is a **conjecture statement** written as
`by sorry`, not a formal proof, and this folder treats only the
prime-power subfamily specified above.

## Reproduction

From the repository root:

```bash
lake env lean AgenticConjectures/OeisA067720.lean
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
python3 scripts/gen_upstream_docs.py --check
python3 scripts/check_docs.py
```

Measured on the development machine on 2026-10-24 with a warm mathlib
cache:

- direct module elaboration: 11.2 seconds;
- `lake build AgenticConjectures.OeisA067720` after the change: 14.5 seconds
  wall time, 10 seconds of it for the module itself;
- the subsequent full `lake build`: 10.5 seconds;
- the axiom audit over all 84 registered theorems: 8.1 seconds;
- import reachability, the banned-construct scan, and
  `verify_all.py --ci --only oeis-a067720`: under 0.1 seconds each. This
  problem has no certificate checks.

The documentation gates took under 0.2 seconds each.
