**English** | [한국어](README.ko.md)

# Hadamard matrix of order 668

Status checked as of: 2026-08-11.

## Problem

The question is whether, among `668 x 668` matrices `H` with entries `+1` or
`-1`, there exists one satisfying

```text
H H^T = 668 I
```

## Current status and known partial results

The Hadamard conjecture predicts the existence of such matrices at every
order that is a multiple of 4. A 2023 peer-reviewed paper and a 2026 status
report both record 668 as the smallest unresolved order.

On the sufficient-condition route of searching for a Legendre pair of
length 333, the 2026 status report reports the following.

- It exhaustively enumerated the 12,017,243 PSD-compatible configurations
  of the 9-compression.
- The best `L1` PSD error obtained from the 37-compression heuristic
  was 236.

It contains no new result deciding the existence or nonexistence of an
order-668 matrix.

This repository adds exhaustive computations for one structured subclass:
Legendre pairs of length 333 that are invariant under a multiplier subgroup.
They are described in
[Multiplier-invariant Legendre pairs of length 333](#multiplier-invariant-legendre-pairs-of-length-333).
They exclude 72 of the 80 multiplier classes and decide nothing about order
668 itself.

## Caution on logical scope

If a Legendre pair of length 333 exists, a Hadamard matrix of order 668 can
be constructed. However, an arbitrary Hadamard matrix of order 668 is not
necessarily of this form. Therefore the "equivalently" in the status
report's abstract must not be used as a logical equivalence for the full
existence problem.

Each structured subspace — Legendre-pair, Goethals--Seidel, Williamson, and
so on — can be searched with PSD filters, meet-in-the-middle, SAT, or SMT.
An UNSAT in one construction class is not a nonexistence proof for the full
Hadamard problem.

## Multiplier-invariant Legendre pairs of length 333

Computed on 2026-10-24. The code, data and logs are in [`legendre/`](legendre/).

### Exact statement

A Legendre pair of length 333 is a pair of maps `A, B : Z/333 -> {+1, -1}`
with `PAF_A(s) + PAF_B(s) = -2` for every `s != 0`, where
`PAF_A(s) = sum_x A(x) A(x+s)`. Every such pair has
`sum(A)^2 + sum(B)^2 = 2`, and negating one sequence keeps the pair a pair, so
we normalize to `sum(A) = sum(B) = 1`. The multiplier group `(Z/333)^*` has
order 216, is isomorphic to `C6 x C36`, and has 80 subgroups. For a subgroup
`H`, let `C(H)` be the set of normalized Legendre pairs with `A(hx) = A(x)` and
`B(hx) = B(x)` for all `h` in `H` and all `x`.

**Claim.** `C(H)` is empty for 72 of the 80 subgroups. It is open for the 8
subgroups `<10,112>`, `<184>`, `<121>`, `<211>`, `<10>`, `<112>`, `<73>` and
the trivial group (which is the unrestricted problem).

Two other symmetry types reduce to these classes.

- If `A` is `H1`-invariant and `B` is `H2`-invariant, the pair lies in
  `C(H1 ∩ H2)`.
- If `A` is `H`-invariant and `B = A∘μ` for a multiplier `μ`, then `B` is also
  `H`-invariant because the group is abelian. The pair therefore lies in
  `C(H)`.

### Class table

Subgroups are written by generators mod 333. The columns give the number of
`H`-orbits on `Z/333` and the orders of the images `H9` of `H` in `(Z/9)^*` and
`H37` of `H` in `(Z/37)^*`. The criteria are explained below the table.

| H | order | orbits | H9 | H37 | excluded by |
|---|---:|---:|---:|---:|---|
| the 50 subgroups containing some `h = 2 (mod 3)` | | | | | mod 3 |
| `<4,19>` | 108 | 10 | 3 | 36 | mod 37, sum |
| `<4,7>` | 54 | 15 | 3 | 18 | T111 |
| `<13>` | 36 | 14 | 3 | 36 | mod 37, sum |
| `<22>` | 36 | 14 | 3 | 36 | mod 37, sum |
| `<19>` | 36 | 18 | 1 | 36 | mod 37, sum |
| `<10,31>` | 36 | 20 | 3 | 12 | sum, C37(12) |
| `<7,16>` | 27 | 25 | 3 | 9 | T111 |
| `<4>` | 18 | 23 | 3 | 18 | T111 |
| `<58>` | 18 | 23 | 3 | 18 | T111 |
| `<28>` | 18 | 27 | 1 | 18 | search |
| `<10,85>` | 18 | 35 | 3 | 6 | T111 |
| `<88>` | 12 | 32 | 3 | 12 | sum, C37(12) |
| `<214>` | 12 | 32 | 3 | 12 | sum, C37(12) |
| `<82>` | 12 | 36 | 1 | 12 | sum, C37(12) |
| `<31>` | 12 | 50 | 3 | 4 | C37(4), A37 |
| `<7>` | 9 | 41 | 3 | 9 | T111 |
| `<16>` | 9 | 41 | 3 | 9 | T111 |
| `<46>` | 9 | 45 | 1 | 9 | search |
| `<10,112>` | 9 | 65 | 3 | 3 | **open** |
| `<85>` | 6 | 59 | 3 | 6 | C111, search |
| `<175>` | 6 | 59 | 3 | 6 | C111, search |
| `<64>` | 6 | 63 | 1 | 6 | lift search |
| `<184>` | 6 | 95 | 3 | 2 | **open** |
| `<154>` | 4 | 90 | 1 | 4 | C37(4) |
| `<121>` | 3 | 113 | 3 | 3 | **open** |
| `<211>` | 3 | 113 | 3 | 3 | **open** |
| `<10>` | 3 | 117 | 1 | 3 | **open** |
| `<112>` | 3 | 185 | 3 | 1 | **open** |
| `<73>` | 2 | 171 | 1 | 2 | **open** |
| `{1}` | 1 | 333 | 1 | 1 | **open** |

### Exclusion criteria

Every criterion below is an exact consequence of the pair equations.
Floating-point power spectra (PSD) are used only to discard a candidate whose
computed `PSD(k)` exceeds `668 + 1e-6`. The accumulated rounding error is
below `1e-9`. Every pair condition is checked with exact integer PAF values.

- **mod 3** (Theorem 1 of the 2026 report). If `h = 2 (mod 3)`, the
  3-compression `(u, v, w)` of `A` (sums over `x = 0, 1, 2 mod 3`) has
  `v = w`. Then `PSD_A(111) = (u - v)^2`, and the same holds for `B`. But
  `PSD_A(111) + PSD_B(111) = 668 = 4 * 167` is not a sum of two squares. This
  excludes every subgroup outside `K3 = ker((Z/333)^* -> (Z/3)^*)`. `K3` has
  order 108 (`C3 x C36`) and contains 30 subgroups. The report's Section 6.2
  calls this kernel `C2 x C36` of order 72.
- **mod 37** (the report's remark after Theorem 1). If `H` maps onto
  `(Z/37)^*`, the 37-compression is `(c0, x, ..., x)` and
  `PSD_A(9k) = (c0 - x)^2` for `37 ∤ k`. The same contradiction follows.
- **sum.** No sign assignment on the orbits has sum 1. This is an exact DP
  over the orbit sizes.
- **T111.** `PSD_A(111) = N(u, v, w) = u^2 + v^2 + w^2 - uv - vw - wu`. Here
  `u + v + w = 1` and each entry is a sum of 111 signs. `N(u, v, w)` and
  `668 - N(u, v, w)` must both be such norms. That leaves 16 admissible values
  (16, 64, ..., 652). No orbit sign vector with sum 1 attains one of them.
  `subgroup_table.py` counts this with two independent exact DPs.
- **A37.** If `H9 = <4>`, the 9-compression `a` is constant on `{1,4,7}` and
  on `{2,5,8}`, and `PSD_A(37) = N(a0, a3, a6)` must also be admissible. For
  `<31>` the count is 0.
- **C37(m).** The 37-compression `c` (`c_r` = sum of `A(x)` over
  `x = r mod 37`) is constant on the cosets of `H37`, which has order `m`. The
  pair satisfies `PAF_c + PAF_d = -18` off zero and `sum c^2 + sum d^2 = 650`.
  Two programs enumerate these exhaustively: `comp_pairs.cpp`
  (meet-in-the-middle with exact PAF matching) and `comp37_exact.py` (plain
  exact enumeration). For `m = 4, 6, 9, 12, 18, 36` both report 0, 2, 40, 0,
  2 and 0 admissible `c`, and the two lists are identical. The cases
  `m = 4, 12, 36` are therefore empty.
- **search** (`<28>`, `<46>`). Two exhaustive meet-in-the-middle programs.
  - `lp_orbit_search.cpp` splits the orbits into two halves and keys them by
    the exact 3-compression. Its examined count equals an exact DP count.
  - `lp_column_search.cpp` splits the classes `x mod 37`, fixes the
    37-compression to an admissible `c`, and keys them by the 3-compression.

  The survivors of the first program that have an admissible `c` coincide
  exactly with the survivors of the second (`crosscheck_survivors.py`). Neither
  program finds a pair.
- **C111** (`<85>`, `<175>`). This criterion uses the 3-compression to length
  111, `A'(y) = A(y) + A(y+111) + A(y+222)`.
  - Pair equations: `PAF_A' + PAF_B' = -6` off zero and
    `sum A'^2 + sum B'^2 = 662`.
  - Constraints on `A'`. It is invariant under `H mod 111`, and its
    37-compression lies in C37(6), which has 2 vectors. Its
    sum of squares is at most 551, its 3-compression is admissible, and
    `PSD_A'(k) = PSD_A(3k) <= 668`.
  - These two groups permute the fibres `{37, 148, 259}` and
    `{74, 185, 296}` transitively. Hence `A'(37)` and `A'(74)` are `±3`.
  - Of the 4,000,000 candidates, 58,464 pass the exact filters and 4,296 pass
    the PSD filter. No compressed pair exists.

  `lp_comp111.cpp` and `lp_comp111_check.py` agree on every intermediate
  count. Full-length searches with `lp_column_search.cpp` in 9-compression
  mode also find no pair. Each search examines 56,833,665,984 sign vectors,
  keyed by the 630 admissible `<4>`-invariant 9-compressions from
  `comp9_pairs.py` (two methods).
- **lift search** (`<64>`). This group acts trivially on `Z/9`, so `A'(37)`
  and `A'(74)` are free. Of the 24,000,000 candidates, 648 admissible
  compressions `A'` remain (3,888 ordered compressed pairs; listed in
  `data/adm111_h64.txt`). Every `<64>`-invariant `A` with one of these
  compressions was enumerated, 45,112,963,608 sign vectors in total, by two
  programs:
  - `lp_lift111.cpp`, whose count equals the product of the per-orbit choice
    counts: 5,159,376 PSD survivors and no pair;
  - `lp_column_search.cpp` in `a111` mode: the same 45,112,963,608 sign
    vectors, an identical set of 5,159,376 PSD survivors, and no pair.

**Positive controls** (`controls.py`). Every search program must reproduce
brute-force pair counts, so none of the controls can pass vacuously.

- `lp_orbit_search`: 972 ordered pairs at length 9 and 7,098 at length 13.
- Length 63 with `H = <2>`: 144 ordered pairs, found by `lp_orbit_search`,
  by `lp_column_search` in `u3` and `a111` modes, and by `lp_lift111`.
- Length 63 with `H = <11>`: 24 ordered pairs, found by the same programs.
- `lp_comp111` reports the 3-compression of every length-63 pair as
  admissible.

### Reproduction

Commands run from `problems/hadamard-668`. Runtimes were measured on an Apple
laptop. The thread counts are the last numeric arguments.

```text
python3 legendre/subgroup_table.py                                 # 10 s, class table
python3 legendre/comp9_pairs.py 37 legendre/data/adm9_h4.txt       # 6 s
g++ -O2 -std=c++17 -pthread -o /tmp/h668_cp legendre/comp_pairs.cpp
for m in 4 6 9 12 18 36; do /tmp/h668_cp 37 9 $m 1; done           # < 1 s each
for m in 4 6 9 12 18 36; do python3 legendre/comp37_exact.py $m; done  # m=4: 57 s with numpy
g++ -O2 -std=c++17 -o /tmp/h668_c111 legendre/lp_comp111.cpp
/tmp/h668_c111 333 85 legendre/data/adm37_m6.txt                   # < 1 s (also 175, 64)
python3 legendre/lp_comp111_check.py 333 85 legendre/data/adm37_m6.txt  # 3 s, needs numpy (64: 16 s)
g++ -O2 -std=c++17 -pthread -o /tmp/h668_A legendre/lp_orbit_search.cpp
g++ -O3 -std=c++17 -pthread -o /tmp/h668_B legendre/lp_column_search.cpp
g++ -O2 -std=c++17 -pthread -o /tmp/h668_lift legendre/lp_lift111.cpp
python3 legendre/controls.py /tmp/h668_A /tmp/h668_B /tmp/h668_c111 /tmp/h668_lift  # 1 s
/tmp/h668_A 333 28 3 16 - /tmp/s28A; /tmp/h668_B 37 28 legendre/data/adm37_m18.txt u3 - 3 /tmp/s28B
/tmp/h668_A 333 46 3 22 - /tmp/s46A                                 # 31 s, ~3 GB
/tmp/h668_B 37 46 legendre/data/adm37_m9.txt u3 - 3 /tmp/s46B       # 18 s
python3 legendre/crosscheck_survivors.py 46 legendre/data/adm37_m9.txt /tmp/s46A /tmp/s46B
/tmp/h668_B 37 85 legendre/data/adm37_m6.txt a9 legendre/data/adm9_h4.txt 3 -   # 21 min
/tmp/h668_B 37 175 legendre/data/adm37_m6.txt a9 legendre/data/adm9_h4.txt 3 -  # 18 min
/tmp/h668_lift 333 64 legendre/data/adm111_h64.txt 3                # 59 s
/tmp/h668_B 37 64 legendre/data/adm37_m6.txt a111 legendre/data/adm111_h64.txt 3 -  # 250 s, ~36 GB
```

The logs of these runs are in [`legendre/logs/`](legendre/logs/). Survivor files
are not committed because they reach 1.3 GB. The commands above regenerate them.

### What is not claimed

- Nothing is claimed about the existence of a Hadamard matrix of order 668.
  Nothing is claimed about Legendre pairs of length 333 without multiplier
  symmetry either, because the open classes include the unrestricted problem
  `C({1})`.
- The exclusions are computer results, except for mod 3 and mod 37, which are
  short proofs. Every computational exclusion was re-derived by two
  independent implementations, and positive controls pass. Nothing is formally
  verified or peer reviewed.
- No novelty is claimed. The 2026 report proposes this multiplier-orbit route
  (Section 6.2, with simulated annealing) but reports no per-subgroup results.
  The literature beyond that report was not checked.
- The secondary target, Goethals–Seidel quadruples of length 167, was not
  attempted.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the Lean
declaration asking for existence at exactly `k=167`, i.e. order 668. That
declaration is an open problem statement containing `sorry`, and the
structured-search status above is not its answer.

## Evidence

- [Three-dimensional Hadamard matrices of Paley type](https://www.sciencedirect.com/science/article/pii/S107157972300148X),
  *Finite Fields and Their Applications* 92 (2023), 102306.
- Chojecki,
  [Computational Search for a Hadamard Matrix of Order 668 via Legendre Pairs of Length 333](https://www.ulam.ai/research/frontier-had.pdf),
  March 2026 (non-peer-reviewed status report).
