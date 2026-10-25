**English** | [한국어](README.ko.md)

# Uniqueness of crystal components (arXiv:1601.03081)

## The conjecture

M. Abrate, S. Barbero, U. Cerruti and N. Murru, *The Biharmonic mean*,
[arXiv:1601.03081](https://arxiv.org/abs/1601.03081) (v1, 12 January 2016), define

B(a, b) = ((a + b)² + (ab + 1)²) / (2(a + 1)(b + 1)).

Their Definition 5 calls an odd number n a **crystal** if n = ab with a, b > 1 and B(a, b) ∈ ℕ.
The smallest crystal is 35 = 5 · 7, where B(5, 7) = 1440 / 96 = 15.

In the concluding section the authors conjecture that no other pair c, d > 1 with n = cd has
B(c, d) ∈ ℕ, that is, "the components of the crystals are unique", and remark that a proof or a
counterexample does not seem easy. Formal Conjectures states this as `crystals_components_unique`,
tagged `research open`, at commit `c094b97`:

```lean
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

theorem crystals_components_unique (n a b c d : ℕ)
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  sorry
```

The exact upstream file is kept in [upstream/](upstream/README.md).

## Result

**Status: partial.** The conjecture is not proved. What is established:

1. **Lean: equivalent conditions** (the paper's Proposition 1; the first two are also in the open
   Formal Conjectures PR #7051). For odd a, b > 1, n = ab is a crystal iff
   (a + 1)(b + 1) ∣ (a + b)², iff (a + 1)(b + 1) ∣ (n + 1)², and, with u = (a + 1)/2 and
   v = (b + 1)/2, iff u ∣ (v − 1)² and v ∣ (u − 1)².
2. **Lean: the classification** (the paper's Theorems 4 and 5). n = ab is a crystal iff
   (a + 1)/2 and (b + 1)/2, in some order, are consecutive terms, both at least 2, of
   u₀ = 0, u₁ = 1, u_{m+2} = (k − 2)u_{m+1} − u_m + 2 for some integer k. One can take
   k = (a + b)² / ((a + 1)(b + 1)), which is an integer ≥ 3. In closed form,
   {a + 1, b + 1} = {2kp², 2(p + r)²} with p, r ≥ 1 and (p + r)² = kpr + 1, where (p, r) are
   consecutive terms of a Lucas sequence.
3. **Lean: the reduction.** Every crystal satisfies (a + b)² = k(n + 1 + a + b), so n and k
   determine {a, b}. The conjecture is therefore equivalent to: *all crystal factorizations of the
   same n have the same k.*
4. **Lean: three cases.** Two crystals with the same n and the same k coincide; k = 3 occurs only
   for 35 = 5 · 7; and two crystals of the j = 1 family {2k − 1, 2(k − 1)² − 1} never share n.
5. **Computer-assisted; Lean modulo one computed fact.** The k = 4 family
   {2t² − 1, 2(t + 1)² − 1} and the j = 1 family share only n = 119 = 7 · 17, which is one
   crystal in both families. Lean proves this (`eq_of_crystalK_eq_four_of_j1`) from the list of
   integral points of an elliptic curve of rank 2, which is computed in Sage/PARI and enters the
   theorem as an explicit hypothesis (`EllipticCurveIntegralPoints`).
6. **Computation.** Two independent programs find no collision among the 3,493,319,443,273
   crystals n ≤ 2¹²⁷ − 1. One of them extends the check of the j ≥ 2 crystals to n ≤ 10⁴⁰.

Every crystal falls into exactly one of four classes, by its invariant k and its position j in the
chain of its k (the j-th crystal of the k-chain is the pair (u_{j+1}, u_{j+2}) above):

| Class | Definition | Components {a, b} | Crystals n ≤ 2¹²⁷ − 1 |
| --- | --- | --- | ---: |
| F3 | k = 3 | {5, 7} | 1 |
| F4 | k = 4 | {2t² − 1, 2(t + 1)² − 1}, t ≥ 2 | 2,553,802,832 |
| F1 | k ≥ 5, j = 1 | {2k − 1, 2(k − 1)² − 1} | 3,490,731,829,162 |
| S | k ≥ 5, j ≥ 2 | from the recurrence | 33,811,278 (j ≤ 43) |

Which pairs of classes are known not to share n:

| Pair | Status |
| --- | --- |
| any two crystals with the same k | Lean, `eq_of_crystalK_eq` |
| F3 with any crystal | Lean, `eq_of_crystalK_eq_three` |
| F1 with F1 | Lean, `eq_of_j1` |
| F4 with F1 | Lean, `eq_of_crystalK_eq_four_of_j1`, assuming the integral points of an elliptic curve computed by [`ec_k4_j1.py`](ec_k4_j1.py) (Sage/PARI) |
| S with F1, F4 or S of a different k | **open**; no collision for n ≤ 2¹²⁷ − 1 (two programs) or n ≤ 10⁴⁰ (one program) |

What remains open is the last row: a crystal of class S sharing its n with a crystal of a
different k.

## Proof idea

1. **Divisibility.** Write D = (a + 1)(b + 1) and s = a + b, so that ab + 1 = D − s. For odd a,
   s² + (ab + 1)² = 2(s² + D · ((a − 1)/2)(b − 1)), so 2D divides it iff D ∣ s².
   And (ab + 1)² = s² + D(D − 2s), so D ∣ s² iff D ∣ (n + 1)².
2. **The (u, v) form.** With a + 1 = 2u and b + 1 = 2v, D = 4uv and s = 2(u + v − 1), so the
   condition is uv ∣ (u + v − 1)², which splits into u ∣ (v − 1)² and v ∣ (u − 1)². Put
   k = (u + v − 1)²/(uv); then k ≥ 3, because (u + v − 1)² − 2uv = (u − 1)² + (v − 1)² − 1 > 0.
3. **Vieta descent.** For fixed y, the two roots x, x′ of (x + y − 1)² = kxy satisfy
   x + x′ = (k − 2)y + 2 and xx′ = (y − 1)². Replacing the larger coordinate by its partner
   descends to the pair (1, k), and climbing back up gives the recurrence. This proves
   Theorems 4 and 5 of the paper (the paper cites Theorem 4 from its reference [1]).
4. **Closed form.** With L the Lucas sequence L₀ = 0, L₁ = 1, L_{i+2} = (k − 2)L_{i+1} − L_i,
   one has u_{2i} = kL_i² and u_{2i+1} = (L_i + L_{i+1})², and consecutive terms satisfy
   L_{i+1}² − (k − 2)L_iL_{i+1} + L_i² = 1, which is (p + r)² = kpr + 1 for (p, r) = (L_i, L_{i+1}).
5. **Reduction.** a + b = 2(u + v − 1) and D = n + 1 + (a + b), so (a + b)² = k(n + 1 + a + b).
   For fixed n and k this quadratic has one positive root, so a + b and ab = n fix {a, b}.
6. **Cases.** For k = 3 the chain is 1, 3, 4, 3, 1, …, so the only crystal is 5 · 7. On the
   j = 1 family n = (2k − 1)(2(k − 1)² − 1) is strictly increasing in k. For k = 4 against
   j = 1, equal n means (2X − 1)² = 4K³ − 10K² + 6K + 1 with X = t(t + 1); this is the
   elliptic curve y² = x³ − 10x² + 24x + 16 with x = 4K and y = 4(2X − 1). Its integral points
   give K ∈ {0, 1, 4, 21, 300}, and only K = 4 has X of the form t(t + 1) with t ≥ 2.

[DETAILS.md](DETAILS.md) gives every step, the elliptic-curve argument, the algorithms and their
completeness arguments, and remarks on why the remaining case is hard.

## Lean formal proof

[`AgenticConjectures/CrystalComponentsUnique.lean`](../../AgenticConjectures/CrystalComponentsUnique.lean)
records the open statement as `statement` and proves the results below. It uses no `sorry`, no
extra axioms and no `native_decide`, and `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`. The one computed fact, the list of integral points of an
elliptic curve, is the `def` `EllipticCurveIntegralPoints` and appears only as a hypothesis of
`eq_of_crystalK_eq_four_of_j1`; it is not an axiom.

| Declaration | Content |
| --- | --- |
| `IsCrystalWithComponents`, `isCrystalWithComponents_35_5_7` | The upstream definition and test case, term for term. |
| `statement` | The upstream theorem, universally quantified (not proved). |
| `dvd_biharmonic_iff`, `dvd_sq_add_iff_dvd_mul_add_one_sq` | 2(a + 1)(b + 1) ∣ (a + b)² + (ab + 1)² ⟺ (a + 1)(b + 1) ∣ (a + b)² (a odd) ⟺ (a + 1)(b + 1) ∣ (ab + 1)². |
| `isCrystal_iff_dvd_sq_add`, `isCrystal_iff_dvd_succ_sq` | Proposition 1 as characterizations of `IsCrystalWithComponents`. |
| `isCrystal_iff_uv_dvd`, `isCrystal_iff_uv` | The (u, v) form: uv ∣ (u + v − 1)², and u ∣ (v − 1)² ∧ v ∣ (u − 1)². |
| `crystalK`, `IsCrystalWithComponents.sq_add_eq_mul`, `.three_le_crystalK` | k = (a + b)² / ((a + 1)(b + 1)); (a + b)² = k(n + 1 + a + b); k ≥ 3. |
| `eq_of_crystalK_eq` | Two crystal factorizations of the same n with the same k coincide. |
| `statement_iff_crystalK_eq` | The conjecture ⟺ every two crystal factorizations of the same n have the same k. |
| `IsCrystalWithComponents.eq_five_seven_of_crystalK_eq_three`, `.eq_five_seven_of_eq_35`, `eq_of_crystalK_eq_three` | k = 3 only for {5, 7}, and nothing else shares n = 35. |
| `seqU`, `seqU_invariant`, `sq_eq_mul_iff_seqU` | The paper's sequence u(w), and Theorem 4: the positive solutions of (x + y − 1)² = wxy are the consecutive pairs, in either order. |
| `IsCrystalWithComponents.exists_seqU`, `isCrystal_iff_seqU` | Theorem 5: the classification of crystals by the recurrence. |
| `lucas`, `lucas_cassini`, `lucas_nonneg_lt`, `seqU_lucas` | The Lucas sequence and u_{2i} = wL_i², u_{2i+1} = (L_i + L_{i+1})². |
| `isCrystal_iff_kpr`, `crystalK_eq_of_kpr` | Closed form {a + 1, b + 1} = {2kp², 2(p + r)²} with (p + r)² = kpr + 1, and then k = `crystalK a b`. |
| `isCrystal_iff_pronic` | Crystal ⟺ n + 1 = kq(q + 1) and a + b = k(q + 1) for some k, q. |
| `IsCrystalWithComponents.crystalK_eq_four_iff` | k = 4 exactly for {(a + 1)/2, (b + 1)/2} = {t², (t + 1)²}, t ≥ 2. |
| `IsCrystalWithComponents.j1`, `eq_of_j1` | If a + 1 = 2k then b + 1 = 2(k − 1)², and two such crystals of the same n coincide. |
| `EllipticCurveIntegralPoints` | Not proved (the Sage/PARI output): every integral point of y² = x³ − 10x² + 24x + 16 has x ∈ {0, 3, 4, 6, 10, 16, 19, 84, 1200}. |
| `eq_of_crystalK_eq_four_of_j1` | Assuming `EllipticCurveIntegralPoints`, a crystal with k = 4 and a j = 1 crystal of the same n coincide. |

## Statement faithfulness

- **Definition.** `IsCrystalWithComponents` is the Formal Conjectures definition term for term.
  It encodes B(a, b) ∈ ℕ as divisibility of the numerator by the (nonzero) denominator, and
  "odd n with n = ab" exactly as in Definition 5.
- **Statement.** `statement` is the upstream theorem with its arguments n, a, b, c, d and both
  hypotheses universally quantified; the conclusion `({a, b} : Finset ℕ) = {c, d}` is unchanged.
  It says that the two unordered pairs of components agree, which is the paper's "different from
  the couple a, b".
- **Natural-number division.** `crystalK a b` is defined with `ℕ` division, which truncates. For a
  crystal the division is exact (`IsCrystalWithComponents.sq_add_eq`), so it equals the paper's
  Q(a, b); every theorem that uses `crystalK` assumes a crystal.
- **Subtraction.** The sequences `seqU` and `lucas` live in ℤ, so their recurrences involve no
  truncated subtraction. The only `ℕ` subtraction is `crystalK a b - 1` in
  `IsCrystalWithComponents.j1`, where k ≥ 3.
- **Order and index range.** The paper writes Theorem 4 as (x, y) = (u_n, u_{n−1}) with n ≥ 1,
  and Theorem 5 with a the later term. The equation is symmetric and (u₁, u₀) = (1, 0) is not a
  positive pair, so the Lean versions allow both orders and require both terms to be positive
  (Theorem 4) or at least 2 (Theorem 5).
- **Toolchain.** This repository builds with Lean and mathlib `v4.30.0`; Formal Conjectures at
  `c094b97` pins `v4.33.1`. The definition uses only `Odd`, `∣`, `*` and `^` on `ℕ`, and the
  statement only `Finset` insertion, whose meaning is the same in both versions. The file has not
  been compiled against `v4.33.1`.
- **Adaptations** (also listed in the module docstring): `import Mathlib` instead of
  `public import FormalConjecturesUtil`; the `module` keyword, `@[expose] public section` and the
  `@[category …]`/`@[AMS …]` attributes are dropped; the namespace `Arxiv.«1601.03081»` becomes
  `AgenticConjectures.CrystalComponentsUnique`.

## Computation

The computations rely on the Lean classification for completeness, except `direct_check.py`.

- [`crystal_search.c`](crystal_search.c) (implementation A): C with 128-bit integers. For each
  k ≥ 5 it walks the Lucas pairs (p, r), lists the S crystals in both orientations, sorts them,
  and inverts the closed forms of F1 and F4 exactly on every S member and on every F4 member.
  All products saturate at 2¹²⁸ − 1, which exceeds every admissible bound X ≤ 2¹²⁷ − 1.
- [`crystal_exact.py`](crystal_exact.py) (implementation B): Python with exact integers and the
  standard library only. It walks the (u, v) recurrence instead of the Lucas pairs and uses
  integer roots instead of floating-point estimates. It shares no code with A.
- [`direct_check.py`](direct_check.py): enumerates every u ≥ 2 and every divisor v ≥ u of
  (u − 1)², tests the original definition, and classifies the crystals it finds. It does not use
  the classification, so it also checks the classification itself, up to 10¹⁴.
- [`ec_k4_j1.py`](ec_k4_j1.py): the F4-against-F1 elliptic-curve computation.

All programs print the class sizes, the largest j, the total, a checksum of the S members (their
sum mod 2⁶⁴) and the number of collisions. Measured on an Apple M5 Max (shared with other jobs);
full outputs are in [logs/](logs/crystal_search.log).

| Bound X | Program | Crystals n ≤ X | S members (largest j) | Collisions | Time |
| --- | --- | ---: | ---: | ---: | ---: |
| 10¹² | A, B, `direct_check.py` | 7,266 | 264 (12) | 0 | 0.1 s, 0.02 s, 2.4 s |
| 10¹⁴ | A, B, `direct_check.py` | 32,094 | 622 (14) | 0 | < 0.1 s, 0.02 s, 32 s |
| 10³⁴ | A (4 threads), B | 135,949,335,491 | 4,847,868 (38) | 0 | 2.4 s, 18 s |
| 2¹²⁷ − 1 | A (4 threads), B | 3,493,319,443,273 | 33,811,278 (43) | 0 | 26 s (89 s CPU, 1.1 GB), 168 s (1.9 GB) |
| 10⁴⁰ | B | 13,579,235,391,289 | 76,240,507 (45) | 0 | 353 s (4.3 GB) |

- At every bound the programs agree on every class count and on the S checksum.
- A checks every F4 member against F1. B does so up to the bound given by `--f4-limit` (10²⁴ for
  X = 10³⁴, 10³⁰ for the larger bounds); the elliptic-curve computation covers this pair for all
  n anyway. Beyond 2¹²⁷ − 1 only B ran, so the S row of the 10⁴⁰ run has a single implementation.
- `ec_k4_j1.py` runs in about 2 s. It proves rank 2 with PARI `ellrank`, shows that the two points
  found generate the Mordell–Weil group (an index bound of 5.96 from a lower bound for canonical
  heights, then PARI `ellsaturation` at all primes up to 100), and lists the integral points with
  Sage. It also checks the result against a direct search over K ≤ 10⁶.

## Prior art and status

Checked on 2026-10-25 (UTC):

- **The paper.** arXiv shows v1 only. OpenAlex (W4293570946) lists no citing work, and arXiv
  searches for the biharmonic mean find no follow-up.
- **Formal Conjectures.** `crystals_components_unique` is `research open` at `c094b97` and on
  `main` `37f0808`. The open
  [google-deepmind/formal-conjectures#7051](https://github.com/google-deepmind/formal-conjectures/pull/7051)
  (last updated 2026-10-10) formalizes Proposition 1, including the equivalences that
  `dvd_biharmonic_iff`, `dvd_sq_add_iff_dvd_mul_add_one_sq`, `isCrystal_iff_dvd_sq_add` and
  `isCrystal_iff_dvd_succ_sq` prove here, and leaves the recurrence characterization of Section 3
  of the paper as a TODO. No other issue or pull request there claims progress.
- **Elsewhere.** The statement is part of the FC100 open subset. GitHub code search finds copies
  of it in benchmark and tracker repositories, but no proof or counterexample. Zenodo has no
  matching record. OEIS has no sequence of crystals; A210494 (biharmonic numbers)
  is the related sequence that the paper mentions.
- **What the paper already has.** Proposition 1 and the classification (Theorems 4 and 5, with
  Theorem 4 taken from Abrate, Barbero, Cerruti and Murru, *Polynomial sequences on quadratic
  curves*, Integers, 2015). The Lean proofs of these are formalizations of known results. The
  reduction to k, the case results and the computations were not found in the sources above.

Not finding a result does not establish novelty, and none is claimed. No human has reviewed this
work; it was produced by an AI model and is checked only by the Lean kernel, by PARI/Sage, and by
the cross-checks above. It has not been submitted to Formal Conjectures or anywhere else; any
external submission needs human approval.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.CrystalComponentsUnique
python3 scripts/check_axioms.py
```

Once mathlib is built, the module compiles in about 7 s.

From this directory (the C program needs a C compiler; `ec_k4_j1.py` needs Sage, or the pip
packages passagemath-schemes, passagemath-pari and passagemath-symbolics):

```bash
python3 direct_check.py 1e12
python3 direct_check.py 1e14
python3 crystal_exact.py 1e34 --f4-limit 1e24
python3 crystal_exact.py 2^127-1 --f4-limit 1e30
python3 crystal_exact.py 1e40 --f4-limit 1e30
cc -O2 -o /tmp/crystal_search crystal_search.c -lm -lpthread && /tmp/crystal_search 1e34 2
/tmp/crystal_search max 4
sage -python ec_k4_j1.py
```

CI reruns the bounds 10¹² and 10³⁴ and compares them with
[`logs/summary_1e12.txt`](logs/summary_1e12.txt) and [`logs/summary_1e34.txt`](logs/summary_1e34.txt).
