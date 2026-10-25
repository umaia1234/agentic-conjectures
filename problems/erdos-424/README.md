**English** | [한국어](README.ko.md)

# Erdős problem #424: exact counts through 10^10 and Lean-checked structure

Upstream statement (FormalConjectures docstring, from
[erdosproblems.com/424](https://www.erdosproblems.com/424)):

> Let $a_1 = 2$ and $a_2 = 3$ and continue the sequence by appending to
> $a_1, \ldots, a_n$ all possible values of $a_i a_j - 1$ with $i \neq j$.
> Is it true that the set of integers which eventually appear has positive
> density?

Write $S$ for this set (upstream `generatedSet`; OEIS
[A005244](https://oeis.org/A005244) lists it as a sequence) and
$A(N)=\#\{n\le N : n\in S\}$. Ben Green's open problem 63 is the same question.
**It remains open, and nothing here settles it.** This directory records
Lean-checked structural facts and an exact computation of $S\cap[0,10^{10}]$.
Finite data cannot prove or refute positive density.

## Verified outcomes

### Lean: residue obstruction and polynomial bounds

[`Erdos424.lean`](../../AgenticConjectures/Erdos424.lean) restates the three
upstream definitions verbatim. It proves the theorems below without `sorry`,
extra axioms, or `native_decide`; they depend only on `propext`,
`Classical.choice` and `Quot.sound`.

| Declaration | Statement |
|---|---|
| `mem_generatedSet_iff` | $n\in S \iff n=2 \lor n=3 \lor \exists\,x\ne y\in S,\ n=xy-1$ |
| `lt_mul_sub_one` | for distinct $x,y\in S$: $x<xy-1$ and $y<xy-1$ |
| `two_le_of_mem` | $n\in S\Rightarrow n\ge2$ |
| `mod_three_ne_one` | $n\in S\Rightarrow n\not\equiv1\pmod 3$ |
| `three_mul_countingFn_le` | $3A(N)\le2N$ for every $N$ |
| `le_two_thirds_of_tendsto` | if $A(N)/N\to\alpha$ then $\alpha\le2/3$ |
| `pow_two_add_one_mem`, `generatedSet_infinite` | $2^k+1\in S$ for $k\ge1$; $S$ is infinite |
| `le_sixteen_mul_countingFn_sq` | $N\le16\,A(N)^2$ for $N\ge5$, i.e. $A(N)\ge\sqrt N/4$ |
| `not_mem_of_prime_succ` | $n+1$ prime, $n\ge4\Rightarrow n\notin S$ |
| `three_mul_prime_sub_one_not_mem` | $p$ prime, $p\equiv1\pmod3\Rightarrow 3p-1\notin S$ |
| `infinite_nonmembers_zero_mod_three`, `infinite_nonmembers_two_mod_three` | both admissible classes $0$ and $2\pmod 3$ contain infinitely many non-members |

The lower bound $\sqrt N/4$ is far from the linear growth seen numerically and
is no step towards positive density. The data stay below the upper bound
$2/3$: the ratio is $0.5474$ at $10^{10}$.

### Exact computation through $N=10^{10}$

Two independent programs compute the full bitset of $S\cap[0,10^{10}]$
(1.25 GB):

- [`erdos424_ascending.cpp`](erdos424_ascending.cpp) (A) scans $y$ upwards
  and pushes $xy-1$ for every smaller member $x$. This is valid because both
  factors of a member are smaller than it (`lt_mul_sub_one`).
- [`erdos424_generations.cpp`](erdos424_generations.cpp) (B) evaluates the
  upstream generations $A_0=\{2,3\}$, $A_{k+1}=A_k\cup\{xy-1\}$ literally. It
  uses semi-naive evaluation on two bit planes and stops when a generation adds
  nothing.

They agree on everything they print: the 64-bit hash of the whole bitset, the
counts at every checkpoint $c\cdot10^k$ ($c=1,2,5$), the per-class counts
modulo 26 moduli up to 36, and the first 100 non-members. Both also equal a
literal Python transcription of the upstream recursion up to $10^5$, bit for
bit. All of these values, together with B's generation profile, are in
[`counts_result.json`](counts_result.json).

| $N$ | $A(N)$ | $A(N)/N$ | share of the $\approx 2N/3$ admissible $n\not\equiv1\ (3)$ |
|---:|---:|---:|---:|
| $10^2$ | 23 | 0.230000 | 0.348485 |
| $10^3$ | 250 | 0.250000 | 0.375375 |
| $10^4$ | 3,207 | 0.320700 | 0.481098 |
| $10^5$ | 39,843 | 0.398430 | 0.597651 |
| $10^6$ | 457,599 | 0.457599 | 0.686399 |
| $10^7$ | 4,952,270 | 0.495227 | 0.742841 |
| $10^8$ | 51,899,129 | 0.518991 | 0.778487 |
| $10^9$ | 535,276,618 | 0.535277 | 0.802915 |
| $10^{10}$ | 5,473,663,856 | 0.547366 | 0.821050 |

From the checkpoint $200$ on, $A(N)/N$ increases at every recorded checkpoint.
The gains over the last three decades are $0.024$, $0.016$ and $0.012$. Every
class $n\bmod 6$ rises at every decade from $10^3$ on (see
[details](DETAILS.md#5-data-by-residue-class)). At $10^{10}$ the odd admissible
classes are about 97% full, the class $2\pmod 6$ is 86% full, and the class
$0\pmod 6$ is only 48% full.

### Structure of the complement

- Smallest non-members outside the class $1\pmod 3$: 6, 8, 11, 12, 15, 18,
  20, 21, 23, 24, 29, 30, 32, 35, 36, …
- For every modulus $m\le 1000$, the least set of residues containing $2,3$
  and closed under $(a,b)\mapsto ab-1$ is exactly the set of classes
  $\not\equiv1\pmod 3$ (checked by the wrapper; CI covers $m\le300$). So no
  further residue obstruction can come from this closure argument. At $10^{10}$, every class $\not\equiv1\pmod3$ modulo each
  of the 26 recorded moduli is occupied. The sparsest such classes are those
  of $n\equiv0\pmod 6$ (e.g. $0\pmod{30}$: 36% full). Some classes are almost
  full: $17\pmod{36}$ is 99.99% full.
- Call an admissible $n$ *unfactorable* if $n+1$ has no factorization $xy$
  with $2\le x<y$ and $x,y\not\equiv1\pmod 3$. By `mod_three_ne_one`, such
  $n$ (other than 2, 3) are never members. They are exactly the even $n$ whose
  $n+1$ has a restricted prime factorization (described in
  [DETAILS](DETAILS.md#4-the-arithmetic-part-of-the-complement)). Classical
  estimates give them density zero, but they thin out only like
  $1/\sqrt{\log N}$. [`erdos424_factorable.cpp`](erdos424_factorable.cpp)
  counts them without computing $S$. The rest of the complement consists of
  *dynamic* misses: admissible factorizations exist, but no pair of factors
  lies in $S$.

Shares of all $n\le N$. Here $E$ counts the unfactorable admissible
non-members and $D$ the dynamic misses; the class $1\pmod 3$ is the remaining
third.

| $N$ | $A(N)/N$ | arithmetic $E(N)/N$ | dynamic $D(N)/N$ | arithmetic share of the admissible complement |
|---:|---:|---:|---:|---:|
| $10^{2}$ | 0.2300 | 0.1900 | 0.2400 | 0.442 |
| $10^{3}$ | 0.2500 | 0.1560 | 0.2600 | 0.375 |
| $10^{4}$ | 0.3207 | 0.1344 | 0.2115 | 0.389 |
| $10^{5}$ | 0.3984 | 0.1193 | 0.1489 | 0.445 |
| $10^{6}$ | 0.4576 | 0.1087 | 0.1004 | 0.520 |
| $10^{7}$ | 0.4952 | 0.1005 | 0.0709 | 0.586 |
| $10^{8}$ | 0.5190 | 0.0940 | 0.0537 | 0.636 |
| $10^{9}$ | 0.5353 | 0.0886 | 0.0428 | 0.674 |
| $10^{10}$ | 0.5474 | 0.0840 | 0.0353 | 0.704 |

From $10^6$ on, the arithmetic part makes up more than half of the
admissible complement (70% at $10^{10}$), and it decays slowly. The dynamic
part decays faster. Since $E$ has density zero, $A(N)/N\to2/3$ would follow
if the dynamic misses also had density zero. Neither that nor any positive
lower density is proved.

## Reproduction

From the repository root:

```bash
python3 problems/erdos-424/verify_counts.py                 # N = 10^9 (CI)
python3 problems/erdos-424/verify_counts.py --limit 10000000000
python3 problems/erdos-424/verify_counts.py --part sieves --closure-limit 1000
lake build AgenticConjectures.Erdos424
```

The wrapper compiles the three C++ programs with `g++ -O3 -std=c++17`. It
checks A against B, both against the Python reference, the factorable counts
against a Python divisor enumeration, and everything against
[`counts_result.json`](counts_result.json). Runtimes were measured on
2026-10-24 on a shared Apple M5 Max with load average 8 to 87; under lower load
they are shorter.

| Command | Wall time | Peak memory |
|---|---:|---:|
| `verify_counts.py --part sieves` ($10^9$, closure $m\le300$; CI) | 29 s | 0.25 GB |
| `verify_counts.py --part factorable` ($10^9$; CI) | 22 s | 0.13 GB |
| `verify_counts.py --limit 10000000000` | 700 s | 2.5 GB |
| within it: A, B, factorable at $10^{10}$ | 136 s, 249 s, 313 s | 1.26, 2.51, 1.25 GB |
| `--closure-limit 1000` instead of 300 | about +11 s | |
| `erdos424_probe 1000000 500` | 1.3 s | |
| `lake build AgenticConjectures.Erdos424` (module only) | 15 s | |

## Statement faithfulness

`nextGeneration`, `sequenceSet` and `generatedSet` are copied verbatim from
the [upstream snapshot](upstream/README.md). The research statement
`erdos_424 : answer(sorry) ↔ generatedSet.HasPosDensity` is not restated,
because `Set.HasPosDensity` comes from `FormalConjecturesForMathlib`, which is
not available here. The module instead defines
`countingFn N = (generatedSet ∩ Set.Iic N).ncard`, so $A(N)$ counts
$n\le N$. Counting $n<N$ changes $A(N)$ by at most one, so no limit changes.
Every member is at least 2, so $x\cdot y\ge6$ for distinct members and the
natural-number subtraction $x\cdot y-1$ never truncates. "Distinct" is value
inequality $x\ne y$, as upstream; since $S$ is a set, this matches $i\ne j$ in
the original sequence. The C++ programs use the same convention and the same
truncation-free arithmetic: they accept $N\le2^{40}$, so every product they
form stays far below $2^{64}$.

## What is not claimed

- Positive density (or its negation) of $S$. The increasing ratios are
  evidence, not proof. The slowly decaying arithmetic part shows that any
  limit would be approached very slowly.
- That the class $1\pmod 3$ is the only residue obstruction for all moduli.
  The closure check covers $m\le1000$ only.
- Novelty. The mod-3 obstruction and the family $2^k+1$ are elementary and
  likely known. No literature search beyond the upstream references was done
  for this update.

## Earlier probe

[`erdos424_probe.cpp`](erdos424_probe.cpp) is the original exact probe. Its
outcome had not been recorded. On 2026-10-24,
`erdos424_probe 1000000 500` printed `count 457599 density 0.457599`, the
last non-members `999996` (class 0) and `999992` (class 2) modulo 3, and no
candidate class. So up to $10^6$, every residue class modulo every
$m\le500$ still has a non-member above $1000$. The count agrees with
$A(10^6)$ above. The run took about 1.3 s.
