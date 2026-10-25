**English** | [한국어](README.ko.md)

# OEIS A110566 — not every odd number occurs

## Verdict

The conjecture is **refuted**. [OEIS A110566](https://oeis.org/A110566) is

\[
a(n)=\frac{\operatorname{lcm}(1,2,\ldots,n)}{\operatorname{den}(H_n)},\qquad
H_n=\sum_{j=1}^{n}\frac1j\qquad(n\ge1).
\]

For every \(n\), the 3-adic valuation satisfies

\[
v_3\bigl(a(n)\bigr)\le 3 .
\]

So \(81=3^4\) is never a term, and neither is any odd multiple of 81. The
bound is sharp: \(a(66)=27\). The result is formalized in Lean 4 against the
term-for-term upstream statement. The Lean proof uses no `sorry`, no extra
axioms, and no `native_decide`.

## Canonical statement

The OEIS entry (revision #39, May 17 2023, checked on 2026-10-24) defines the
sequence as “lcm{1,2,...,n}/denominator of harmonic number H(n)” with offset
1. It contains the comment:

> “It is conjectured that every odd number occurs in this sequence (see
> A112822 for the first occurrence of each of them). - Jianing Song, Nov 28
> 2022”

The Formal Conjectures snapshot in [`upstream/`](upstream/README.md)
(`FormalConjectures/OEIS/110566.lean` at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`) states it as follows, under
`open Nat Finset Rat`:

```lean
def a (n : ℕ) : ℕ :=
  (Icc 1 n).lcm id / (harmonic n).den

theorem conjecture :
  ∀ m : ℕ, Odd m → ∃ n > 0, a n = m := by
  sorry
```

## Proof

Write \(v=v_3\), \(L_n=\operatorname{lcm}(1,\ldots,n)\), and
\(k(n)=\lfloor\log_3 n\rfloor\).

1. **From \(H_n\) to \(a(n)\).** The denominator of \(H_n\) divides \(L_n\),
   so \(L_n=a(n)\operatorname{den}(H_n)\). Also \(v(L_n)=k(n)\), and
   \(v(H_n)=v(\operatorname{num})-v(\operatorname{den})\ge-v(\operatorname{den}(H_n))\).
   Hence
   \[
   v\bigl(a(n)\bigr)=k(n)-v\bigl(\operatorname{den}(H_n)\bigr)\le k(n)+v(H_n)=:f(n).
   \]
2. **The 3-adic step.** Put \(m=\lfloor n/3\rfloor\). Separating the multiples
   of 3 gives
   \[
   H_n=\frac{H_m}{3}+R_n,\qquad R_n=\sum_{j\le n,\;3\nmid j}\frac1j,\qquad v(R_n)\ge0 .
   \]
   Suppose \(n\ge3\) and \(v(H_m)\le0\). Then \(v(H_m/3)=v(H_m)-1<0\le v(R_n)\),
   so \(v(H_n)=v(H_m)-1\). Since \(k(n)=k(m)+1\), this gives \(f(n)=f(m)\).
3. **Induction over the base-3 tree.** Use strong induction on \(n\). If
   \(m\notin\{2,7,22\}\), step 2 applies. Otherwise \(n\) is one of the nine
   numbers \(6,7,8,21,22,23,66,67,68\), which are checked directly together
   with the roots \(n=1,2\):

   | \(n\) | \(H_n\) (reduced) | \(v(H_n)\) | \(k(n)\) | \(f(n)\) |
   |---|---|---|---|---|
   | 2 | \(3/2\) | 1 | 0 | 1 |
   | 6 | \(49/20\) | 0 | 1 | 1 |
   | 7 | \(363/140\) | 1 | 1 | 2 |
   | 8 | \(761/280\) | 0 | 1 | 1 |
   | 21 | \(18858053/5173168\) | 0 | 2 | 2 |
   | 22 | \(19093197/5173168\) | 1 | 2 | 3 |
   | 23 | \(444316699/118982864\) | 0 | 2 | 2 |
   | 66 | \(209060999005535159677640233/43787662374178602500420800\) | 0 | 3 | 3 |
   | 67 | \(14050874595745034300902316411/2933773379069966367528193600\) | 0 | 3 | 3 |
   | 68 | \(14094018321907827923954201611/2933773379069966367528193600\) | 0 | 3 | 3 |

   The induction yields two facts. First, \(v(H_n)>0\) exactly for
   \(n\in\{2,7,22\}\); this is the known result of Eswarathasan and Levine
   for \(p=3\). Second, \(f(n)\le3\) for every \(n\).
4. **Conclusion.** By step 1, \(v(a(n))\le f(n)\le3\). Hence \(81\nmid a(n)\)
   for every \(n\). Since 81 is odd, the conjecture fails.

## Lean formalization

[`AgenticConjectures/OeisA110566.lean`](../../AgenticConjectures/OeisA110566.lean)
(namespace `AgenticConjectures.OeisA110566`):

| Declaration | Statement |
|---|---|
| `a` | upstream definition, verbatim: `(Icc 1 n).lcm id / (harmonic n).den` |
| `statement` | upstream conjecture, verbatim: `∀ m : ℕ, Odd m → ∃ n > 0, a n = m` |
| `not_statement` | `¬ statement` (witness \(m=81\)) |
| `not_eightyone_dvd_a` | \(\forall n,\ 81\nmid a(n)\) |
| `padicValNat_a_le` | \(\forall n,\ v_3(a(n))\le3\) |
| `padicValRat_harmonic_add_log_le` | \(\forall n,\ v_3(H_n)+\lfloor\log_3 n\rfloor\le3\) |
| `padicValRat_harmonic_pos_iff` | \(v_3(H_n)>0\iff n\in\{2,7,22\}\) |
| `padicValRat_harmonic_step` | \(n\ge3,\ v_3(H_{\lfloor n/3\rfloor})\le0\Rightarrow v_3(H_n)=v_3(H_{\lfloor n/3\rfloor})-1\) |
| `den_dvd_lcm` | \(\operatorname{den}(H_n)\mid\operatorname{lcm}(1,\ldots,n)\) |
| `a_6`, `a_66` | \(a(6)=3\) (upstream test `a_6`) and \(a(66)=27\) (the bound is attained) |

Proof notes:

- \(v(R_n)\ge0\) is proved by induction on \(n\) for
  \(R_n:=H_n-H_{\lfloor n/3\rfloor}/3\). Going from \(n\) to \(n+1\) either
  leaves \(R\) unchanged (when \(3\mid n+1\)) or adds \(1/(n+1)\) with
  \(3\nmid n+1\). No finset splitting is needed.
- \(v_3(\operatorname{lcm}(1,\ldots,n))=\lfloor\log_3 n\rfloor\) is mathlib's
  `Nat.factorization_lcmUpto`. Here `Nat.lcmUpto n` is definitionally
  `(Icc 1 n).lcm id`.
- `norm_num` evaluates the ten explicit harmonic numbers. The two sanity
  values use kernel `decide +kernel` on the upstream definition.
- `#print axioms not_statement` reports only `propext`, `Classical.choice`,
  and `Quot.sound`.

## Statement faithfulness

- **Definitions.** `a` and `statement` are copied verbatim, with the same
  `open Nat Finset Rat`. The `module`/`public import`/`@[expose]` scaffolding
  becomes `import Mathlib`. The metadata attributes `@[category …]` and
  `@[AMS …]` are dropped. Formal Conjectures defines no other `harmonic`, so
  `harmonic` is mathlib's \(H_n=\sum_{i<n}1/(i+1)\).
- **Index base.** OEIS has offset 1 and upstream quantifies over `n > 0`; this
  file uses the same quantifier. The Lean value `a 0 = 1` (empty lcm 1,
  \(H_0=0\) with denominator 1) is never used by the statement. The bound
  `padicValNat_a_le` holds for \(n=0\) as well.
- **Natural-number division.** `/` in `a` is floor division on ℕ. It is exact
  because `den_dvd_lcm` proves \(\operatorname{den}(H_n)\mid L_n\), so `a n` is
  the exact quotient used by OEIS (A003418/A002805).
- **Denominator.** `Rat.den` is the denominator in lowest terms, which matches
  OEIS “denominator of harmonic number H(n)” (A002805).
- **No subtraction** occurs in the statement. The witness is \(m=81\), which
  is `Odd` via \(81=2\cdot40+1\).
- **Versions.** Upstream pins Lean/mathlib `v4.33.1` (mathlib revision
  `0df444a360eaa60ab8c11dca51a86af692955474`); this repository uses
  `v4.30.0`. On 2026-10-24 the definition of `harmonic` at that revision was
  checked to be identical to ours. `Finset.lcm`, `Finset.Icc`, and `Rat.den`
  are basic notions (lcm of a finite set, integer interval, reduced
  denominator) whose meaning does not depend on the version.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.OeisA110566
python3 problems/oeis-a110566/a110566_certificate.py
python3 problems/oeis-a110566/a110566_certificate.py --limit 300000   # optional, slow
```

Measured on 2026-10-24 (Apple M5 Max, shared machine):

- The Lean module built in 8.1 s on top of the cached mathlib build.
- The certificate with defaults took about 4 s.
- `--limit 100000` took 42 s.
- `--limit 300000` took 403 s (about 7 minutes).

[`a110566_certificate.py`](a110566_certificate.py) uses only the Python
standard library. It is a numerical cross-check, not part of the proof. It
checks:

- the ten reduced fractions hard-coded in the Lean proof and their 3-adic
  valuations;
- the 90 OEIS DATA terms \(a(1..90)\);
- the definition \(L_n/\operatorname{den}(H_n)\) against Vrabec's independent
  formula \(\gcd(L_n, L_nH_n)\) for \(n\le3000\);
- for \(n\) up to `--limit` (default 30000):
  - \(v_3(L_n)=\lfloor\log_3 n\rfloor\);
  - \(v_3(a(n))\le3\);
  - \(\{n : v_3(H_n)>0\}=\{2,7,22\}\);
  - the step recursion.

During development, a separate exploratory gmpy2 run confirmed
\(\max v_3(a(n))=3\) for \(n\le300000\). That run also matched all 10000
terms of the [official b-file](https://oeis.org/A110566/b110566.txt).

## What is not claimed

- Nothing is claimed about which odd numbers do occur. For example, the first
  occurrences of 35, 47, 51, 69, and 73 are still listed as unknown (`?`) in
  [A112822](https://oeis.org/A112822).
- No bound of the form \(v_p(a(n))\le c_p\) is claimed for primes \(p\ge5\).
  The same method may apply where the set \(\{n: v_p(H_n)>0\}\) is known to
  be finite, but it was not attempted here.
- The certificate script does not replace the Lean proof.

## Prior art and submission status

The OEIS entry (revision #39, checked on 2026-10-24) still lists the
conjecture and records no counterexample. [A112822](https://oeis.org/A112822)
(first occurrence of \(2n-1\), revision #18) lists values up to
\(2n-1=77\). The theorem here implies that A112822 has no term for
\(2n-1=81\), because 81 never occurs.

The key ingredient, \(\{n : v_3(H_n)>0\}=\{2,7,22\}\), reproduces a known
result: A. Eswarathasan and E. Levine, “p-integral harmonic sums”, *Discrete
Mathematics* 91 (1991), 249–257. The short step from that result to
\(v_3(a(n))\le3\) was found during the 2026-10-24 harvest triage. Prior art
was checked only on OEIS (A110566, A112822, A112810); no wider literature
search was done for this specific refutation. No novelty is claimed. The
result is unreviewed and has not been reported to OEIS, because external
submissions need human approval.
