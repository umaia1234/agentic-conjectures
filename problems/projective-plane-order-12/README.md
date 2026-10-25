**English** | [한국어](README.ko.md)

# Finite projective plane of order 12

Date of verification: 2026-08-11 (survey); 2026-10-24 (certified
reproductions below).

## Problem

We ask whether a finite projective plane of order 12 exists. This is
equivalent to the existence of a symmetric `2-(157,13,1)` design. Using
a `157 x 157` zero-one incidence matrix `A` whose row and column sums
are 13, the condition can be written as

```text
A A^T = 12 I + J
```

## Current status and known partial results

The primary 2026 sources record 12 as the smallest order whose existence
status is unknown. A 2023 paper ruled out collineation groups of
order 4, and combined with earlier results the only possible full
collineation group orders are 1, 2, and 3.

This directory claims no new existence or nonexistence result. Its
status `partial` refers only to the certified reproductions of classical
exclusions of highly symmetric planes of order 12 described below.

## Computational perspective

The incidence condition lends itself well to formulation as exact cover
or SAT, but the number of variables is large. Because of the known
symmetry-exclusion results, the comparatively easy searches that assume
a large cyclic symmetry are already blocked. Hence a canonical search
handling trivial or very small automorphism groups is the key
bottleneck.

## Certified reproductions of classical exclusions (2026-10-24)

Everything in this section reproduces known results (Singer, Hall,
Evans--Mann, Bose, Hoffman, Gordon; see the references). Nothing here is
new, and nothing here decides whether a plane of order 12 exists. The
multiplier theorem is not used anywhere.

### 1. No cyclic plane: no `(157,13,1)` difference set in `Z_157`

**Claim.** No 13-element subset `D` of `Z_157` has every nonzero residue
as a difference `d - d'` (`d, d'` in `D`) exactly once. By Singer's
correspondence: no projective plane of order 12 has a cyclic collineation
group acting regularly on its 157 points.

*Normalisation.* Translates `D + c` and dilates `uD` (`u` a unit) of a
difference set are difference sets. The difference 1 occurs exactly once,
so some translate contains 0 and 1 (method A). Method B uses the affine
normal form: `0, 1` lie in `D` and the third smallest element `t` of `D`
equals the least ratio `(c - a)/(b - a)` (as an integer in `[0, v)`) over
distinct `a, b, c` in `D` with `b - a` a unit. Mapping a minimising triple
to `0, 1, t` puts any difference set into this form, and `t >= 3` because
ratio 2 would repeat a difference.

Three independent methods:

- **A** (`ds_enumerate.cpp`): plain backtracking over all sets that
  contain `{0, 1}` and have pairwise distinct differences, with no further
  pruning, counting them by size. The largest such sets have 11 elements
  (2,052,820 of them); there are none with 12 or 13 elements.
- **B** (`ds_search_normalized.cpp`): a separate implementation that
  searches only the normal form, with bitset bookkeeping and a Golomb-type
  gap bound. It finds no solution (21,979,581 nodes), and none with 12
  elements either. Where solutions exist the two methods agree exactly: the
  2,052,820 eleven-element sets of method A, filtered by the normal form,
  are exactly the 133,091 sets of method B (`crosscheck_ab.py`).
- **C** (SAT): `ds_cnf.py` encodes normal-form difference sets (variables
  `x_i`, one pair variable per element and difference class with an
  exactly-one constraint per class, units `x_0, x_1`, ratio clauses up to
  5). The independent audit `audit_ds_cnf.py` re-justifies every one of the
  1,062,698 clauses. CaDiCaL 3.0.1 reports UNSAT and drat-trim (commit
  `2e3b2dc`) reports `s VERIFIED`. The 15.5 MB formula and the 320 MB proof
  are not committed; the formula regenerates deterministically (SHA-256
  `731268546c33d2f0f5bc86ec84559adefc9c943a37d880f787633a34c92d8999`).

Controls (`verify_difference_sets.py controls`): for `q = 2, 3, 4, 5, 7,
8, 9` method A finds `phi(q^2+q+1)/(3e)` sets (`q = p^e`), the number of
Singer difference sets containing `{0, 1}`; method B equals method A
filtered by the normal form; for `q = 6, 10` both find nothing.

### 2. No cyclic affine plane: no `(13,11,12,1)` relative difference set in `Z_143`

**Claim.** No 12-element subset `D` of `Z_143` has every element outside
`N = 13 Z_143` (the subgroup of order 11) as a difference exactly once and
no element of `N` other than 0 as a difference. By Bose's correspondence:
no affine plane of order 12 has a cyclic collineation group of order 143
that fixes a point and acts regularly on the other 143 points.

The same three methods (with `N` excluded from the differences):
method A finds sets with `{0, 1}` of at most 10 elements (25,068 of size
10, none of size 11 or 12); method B finds no solution (346,794 nodes);
the SAT formula (ratio clauses up to 6, 764,295 clauses) is UNSAT. The SAT
refutation is committed as a certificate that CI re-checks: `rds143_core.cnf`
is the drat-trim core of the refutation (36,827 clauses of the formula,
each re-justified by `audit_ds_cnf.py`) and `rds143_core.drat` is a
trimmed proof (20,213 lemmas, 1.8 MB) that drat-trim verifies in about 2 s.
`make_rds143_certificate.sh` regenerates both files. Controls: for
`q = 3, 4, 5, 7, 8, 9, 11` method A finds `phi(q^2-1)/(2e)` sets, the
number of Bose relative difference sets containing `{0, 1}`; for
`q = 6, 10` both methods find nothing.

### 3. Collineations of prime order at least 13 (Lean), and the order-13 case

The Lean module `AgenticConjectures/ProjectivePlaneOrder12.lean` proves,
for every projective plane of order 12:

- `order13_fixed_antiflag`: a collineation of order 13 fixes exactly one
  point and exactly one line, and the point is not on the line;
- `prime_gt_13`: a collineation of prime order `p > 13` has `p = 157` and
  fixes no point and no line.

So the only primes at least 13 that can divide the order of a collineation
group are 13 and 157, and an element of order 157 generates a group acting
regularly on the points, which is the cyclic case of part 1 (this last step,
Singer's correspondence, is not formalized). The proof is fixed-point
counting: on any invariant set, an element of prime order `p` fixes a
number of elements congruent to its size modulo `p`. For `p = 13` a fixed
line carries 0 or 13 fixed points, two fixed points span a pointwise fixed
line, and a further fixed point off that line forces the identity; so there
are 0, 1 or 13 fixed points and `157 = 1 (mod 13)` leaves exactly one.
Dually there is exactly one fixed line, and it cannot pass through the
fixed point, since then all 13 lines through the point would be fixed. For
`p > 13` every fixed line is fixed pointwise, and `157 - 1 = 2^2 * 3 * 13`,
`157 - 13 = 2^4 * 3^2` leave only 0 fixed points and `p = 157`.
(Informally, order 7 is impossible by the same counting plus Bruck's
subplane theorem; orders 2, 3, 5 and 11 are not treated here.)

| Declaration | Statement |
|---|---|
| `Collineation P L` | permutations `pts`, `lns` with `pts p ∈ lns l ↔ p ∈ l` |
| `card_fixed_modEq` | `σ ^ p = 1`, `p` prime: fixed points ≡ all elements (mod `p`) |
| `card_fixed_on_line_modEq` | fixed points on a fixed line ≡ `order + 1` (mod `p`) |
| `pts_eq_one_of_fixed_off_line` | a pointwise fixed line plus a fixed point off it force `c.pts = 1` (when every fixed line is fixed pointwise or has no fixed point) |
| `order13_fixed_antiflag` | `order = 12`, `c.pts ^ 13 = 1`, `c.pts ≠ 1` ⇒ unique fixed point `x₀`, unique fixed line `l₀`, `x₀ ∉ l₀` |
| `prime_gt_13` | `order = 12`, `p` prime, `13 < p`, `c.pts ^ p = 1`, `c.pts ≠ 1` ⇒ `p = 157`, no fixed point, no fixed line |

*Faithfulness.* Planes are mathlib's `Configuration.ProjectivePlane P L`
with `ProjectivePlane.order P L = 12`, the notion quantified over in the
upstream `Erdos723.erdos_723.variants.eq_12` (`pp.order = 12`). A
collineation preserves incidence in both directions; "order `p`" is
`c.pts ^ p = 1` and `c.pts ≠ 1`, and the module shows that then also
`c.lns ^ p = 1` and `c.lns ≠ 1`. The theorems are conditional statements
about a hypothetical plane; they do not assert that one exists.

*Order 13 (search not completed).* With the antiflag `(P, l)` of
`order13_fixed_antiflag` and a generator `g`, the orbits are `{P}`, `{l}`,
the 13 points of `l`, the 13 lines through `P`, and 11 further point and
11 further line orbits of length 13. Choose `R` on `l`, put `M = PR`, let
`Q_i` be the point of the `i`-th point orbit on `M` and `L_j` the line of
the `j`-th line orbit through `R`. The plane is then equivalent to 12
permutations `pi_s` (`s` in `Z_13 \ {0}`) of `{0, ..., 10}` such that for
every `delta != 0` and all `i, i'` exactly one `s` outside `{0, delta}`
satisfies `pi_s(i) = pi_{s-delta}(i')` (details in `antiflag_cnf.py`).
`antiflag_cnf.py` encodes this with `pi_1 = id` and `pi_2` in interval form
(both from relabelling the orbits), and `antiflag_decode.py` rebuilds and
checks the whole plane from a model. Controls with the same encoding:
orders 2, 4, 8 are SAT and the decoded planes pass the check; orders 3, 5,
6, 7 are UNSAT, as they should be (no plane of order 6; the planes of
orders 3, 5, 7 are Desarguesian, and for odd `q` the group `PGL(3, q)`
has no element of order `q + 1` that fixes an antiflag and is regular on
its line, because `-1` has norm 1 in `GF(q^2)`). The order-12 instance
(9,438 variables, 231,188 clauses) ran 3.8 h in CaDiCaL 3.0.1 (about
1.4 * 10^8 conflicts) without an answer and was stopped. Nothing is
claimed for collineations of order 13; the literature excludes them
(Janko--van Trung).

### Reproduction

Run in this directory; times measured on an Apple M5 Max shared with
other jobs. CI runs the first five commands of the table.

| Command | What it checks | Time |
|---|---|---|
| `python3 verify_difference_sets.py controls` | controls of parts 1 and 2 | 11 s |
| `python3 verify_difference_sets.py affine` | part 2, methods A and B | 10 s |
| `python3 verify_difference_sets.py planar` | part 1, method B | 24 s |
| `python3 audit_ds_cnf.py 143 12 13 6 rds143_core.cnf` | part 2, clause audit | < 1 s |
| `drat-trim rds143_core.cnf rds143_core.drat` | part 2, DRAT proof | 2 s |
| `python3 verify_difference_sets.py planar-full` | part 1, method A count profile | 15-25 min |
| `sh make_rds143_certificate.sh` | regenerates the part 2 certificate (byte-identical in our run) | 8 min |

Part 1, A versus B for 11-element sets (about 17 min):

```sh
mkdir -p build
g++ -O3 -std=c++17 -o build/ds_enumerate ds_enumerate.cpp
g++ -O3 -std=c++17 -o build/ds_search_normalized ds_search_normalized.cpp
build/ds_enumerate 157 11 157 > build/a157_k11.out          # 15 min
build/ds_search_normalized 157 11 157 > build/b157_k11.out  # 50 s
python3 crosscheck_ab.py 157 157 build/a157_k11.out build/b157_k11.out
```

Part 1, method C (about 15 min, 320 MB proof):

```sh
python3 ds_cnf.py 157 13 157 build/pds157.cnf 5
python3 audit_ds_cnf.py 157 13 157 5 build/pds157.cnf
cadical build/pds157.cnf build/pds157.drat     # exit code 20 (UNSAT), 5 min
drat-trim build/pds157.cnf build/pds157.drat   # s VERIFIED, 11 min
```

Part 3, controls of the order-13 encoding (seconds):

```sh
for n in 2 3 4 5 6 7 8; do
  python3 antiflag_cnf.py $n build/af$n.cnf --interval
  cadical -q build/af$n.cnf > build/af$n.out; echo "n=$n exit=$?"  # 10 SAT, 20 UNSAT
done
python3 antiflag_decode.py 8 build/af8.out
```

### What is not claimed

- Nothing about the existence of a projective plane of order 12, and
  nothing about planes whose collineation group has order 2 or 3 or is
  divisible by 5, 11 or 13.
- No novelty: parts 1 and 2 are classical (they also follow from the
  multiplier theorem and from published computer verifications of the
  prime power conjecture for these objects), and the Lean statements are
  elementary.
- The SAT certificate of part 1 is checked locally only; CI re-runs
  method B for part 1, methods A and B for part 2, the controls, and the
  part 2 certificate.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the `eq_12`
Lean declaration of Erdős problem 723 and the pinned commit information.
The declaration is an existence-problem statement with a `sorry`, and
this directory provides no new existence or nonexistence result.

## References

- Alexeev--Mixon,
  [Forbidden Sidon subsets of perfect difference sets](https://arxiv.org/html/2510.19804v2)
  (2026 edition).
- Akiyama--Suetake--Tanaka,
  [Projective planes of order 12 do not have a collineation group of order 4](https://doi.org/10.1002/jcd.21869),
  *Journal of Combinatorial Designs* 31 (2023), 87--123.
- J. Singer, A theorem in finite projective geometry and some applications
  to number theory, *Trans. Amer. Math. Soc.* 43 (1938), 377--385.
- M. Hall Jr., Cyclic projective planes, *Duke Math. J.* 14 (1947),
  1079--1090.
- T. A. Evans and H. B. Mann, On simple difference sets, *Sankhya* 11
  (1951), 357--364.
- R. C. Bose, An affine analogue of Singer's theorem, *J. Indian Math. Soc.*
  6 (1942), 1--15.
- A. J. Hoffman, Cyclic affine planes, *Canad. J. Math.* 4 (1952),
  295--301.
- R. H. Bruck, Difference sets in a finite group, *Trans. Amer. Math. Soc.*
  78 (1955), 464--481 (subplane theorem).
- D. M. Gordon, The prime power conjecture is true for n < 2,000,000,
  *Electron. J. Combin.* 1 (1994), R6.
- Z. Janko and Tran van Trung, The full collineation group of any
  projective plane of order 12 is a {2, 3}-group, *Geom. Dedicata* 12
  (1982), 101--110.
