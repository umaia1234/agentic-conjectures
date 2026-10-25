**English** | [한국어](README.ko.md)

# Certified symmetric subcases of R(3,10)

Status: **computationally certified, but not peer reviewed**.

This directory records exact searches related to the open Ramsey-number
problem `R(3,10) in {40,41}`.  They do **not** determine `R(3,10)`.

## Broader problem and current status

`R(3,10)` is the least `n` such that every `n`-vertex graph contains either
a triangle or an independent set of size 10.  Its value is 40 or 41: Exoo's
39-vertex construction gives the lower bound 40, while Angeltveit's 2025
computation gives the upper bound 41 after treating roughly 150 billion
`(3,8)` graphs at a cost of about three CPU-years.  The 2026 dynamic survey
retains this interval and records at least 43 million 39-vertex `(3,10)`
graphs.

A single triangle-free 40-vertex graph of independence number at most 9 would
prove the value 41.  A certified exhaustive exclusion of all such graphs would
prove the value 40.  The results below exclude only a few automorphism
classes of that search space.

## Excluded classes at a glance

| Class | Group acting semiregularly | Orbits | Extra clauses | Proof re-checked in CI |
|---|---|---|---|---|
| C20 bicirculant | `C20` | 2 x 20 | none | yes |
| `c10xc2-2orb` | `C10 x C2` | 2 x 20 | none | yes |
| `dic5-2orb` | `Dic5` | 2 x 20 | none | yes |
| `f20-2orb` | `F20` | 2 x 20 | none | yes |
| `d10-2orb` | `D10` | 2 x 20 | none | yes |
| `c10-4orb` | `C10` | 4 x 10 | normalisation lemma | yes |
| `d5-4orb` | `D5` | 4 x 10 | normalisation lemma | no, local check only |
| `q8-5orb` | `Q8` | 5 x 8 | normalisation lemma | no, local check only |
| `c8-5orb` | `C8` | 5 x 8 | normalisation lemma | no, local check only |

The C20 bicirculant certificate is described first, as originally recorded;
the other classes are in
[Further semiregular classes](#further-semiregular-classes).

## C20 bicirculant: certified statement

Let a cyclic group of order 20 act on 40 vertices with two orbits

`A_0,...,A_19` and `B_0,...,B_19`,

by simultaneously increasing both subscripts modulo 20.  There is no graph
invariant under this action that is both triangle-free and has independence
number at most 9.

Equivalently, a hypothetical 40-vertex `(3,10)` Ramsey graph cannot have an
automorphism whose cycle structure is `20^2`.  In graph-theory terminology,
this excludes the semiregular two-orbit `C20` bicirculant class.

No claim of literature novelty is made.  A targeted source search did not
locate this exact subcase, but it has not been peer reviewed.  The simpler
one-orbit circulant exclusion in `search_circulant_r310.py` is already implied
by stronger published cyclic-graph results and is included only as an
independent sanity check.

## C20 bicirculant: encoding

The action has exactly 40 undirected edge orbits:

- variables 1--10 select cyclic distances 1--10 inside the `A` orbit;
- variables 11--20 do the same inside `B`;
- variables 21--40 select the 20 offsets `A_i -- B_(i+d)`.

The preferred, no-auxiliary-variable certificate has 40 variables and 15,804
clauses:

- 444 distinct negative clauses forbid every triangle after quotienting by
  the action;
- 15,360 positive clauses each come from a concrete 10-vertex set and require
  at least one of its pairs to be an edge.

Only a subset of all 10-set clauses is needed: every target graph must satisfy
each such valid clause, and this subset together with the triangle clauses is
already UNSAT.  The clauses were found by SAT+CEGAR.  At each iteration an
exact bit-set search found an independent 10-set in the current model and
added its blocking clause.

## C20 bicirculant: certificate artifacts

| File | Purpose | SHA-256 |
|---|---|---|
| `c20_final_nopb.cnf` | 40-variable DIMACS formula | `d60efdded33920e02fcb60eb14bf3cb3b6d8990b5043a74e8ec716e617b33710` |
| `c20_separators_nopb.txt` | concrete 10-set behind each positive clause | `30f1f231d96f3cf37aac19654361b863b20dfb24ba3720af355db974b84e933d` |
| `c20_nopb_unsat.drup` | Glucose 4.2 UNSAT proof | `4ff189f48b9b818f7113dae09fda6d492d43d360f047e5d9a8d737332fc53108` |
| `c20_result_nopb.json` | generator statistics and hashes | -- |

`audit_c20_certificate.py` uses only the Python standard library.  It checks
that the first 444 clauses are exactly the quotient of all 40-vertex triangle
constraints and that every remaining clause exactly matches the concrete
10-set on the corresponding separator-file line.  This connects the DIMACS
formula to the claimed graph problem independently of the generator.

Four separate PySAT backends report UNSAT: Glucose 4.2, Lingeling, MiniSat
2.2, and MapleSAT.  The DRUP proof has 34,864 lines.  Official `drat-trim` at
commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` verified it with the result
`s VERIFIED` (8,114 input clauses and 21,645 lemmas in the proof core, 366,859
resolution steps).

## C20 bicirculant: reproduce the checks

From `/home/user/projects/agentic-conjectures`:

```bash
python problems/ramsey-r3-10/audit_c20_certificate.py \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  problems/ramsey-r3-10/c20_separators_nopb.txt
```

Expected status: `SEMANTICS VERIFIED`.

The search used Python 3.13.12, `python-sat==1.9.dev13`, and
`pypblib==0.0.4`.  To cross-solve the existing formula and regenerate the
proof:

```bash
python -m venv problems/ramsey-r3-10/.venv
problems/ramsey-r3-10/.venv/bin/pip install \
  'python-sat[pblib]==1.9.dev13'
problems/ramsey-r3-10/.venv/bin/python \
  problems/ramsey-r3-10/verify_c20_cnf.py \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  --proof problems/ramsey-r3-10/c20_nopb_unsat.drup
```

To verify the proof using the independent official checker:

```bash
git clone https://github.com/marijnheule/drat-trim.git /tmp/drat-trim-r310
git -C /tmp/drat-trim-r310 checkout \
  2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C /tmp/drat-trim-r310
/tmp/drat-trim-r310/drat-trim \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  problems/ramsey-r3-10/c20_nopb_unsat.drup
```

To regenerate the formula through the CEGAR search:

```bash
problems/ramsey-r3-10/.venv/bin/python \
  problems/ramsey-r3-10/search_c20_bicirculant_r310.py \
  --solver cadical195 --omit-degree-encoding \
  --cnf-output problems/ramsey-r3-10/c20_final_nopb.cnf \
  --witness-output problems/ramsey-r3-10/c20_separators_nopb.txt \
  --json-output problems/ramsey-r3-10/c20_result_nopb.json
```

The generator's SAT-model order can depend on solver/version.  A regenerated
valid certificate need not be byte-identical; semantic audit plus an
independently verified UNSAT proof is the substantive check.

## Further semiregular classes

Added on 2026-10-24 with the generalised tools `search_symmetric_r310.py`,
`cegar_symmetric_r310.cpp`, `audit_symmetric_certificate.py` and
`build_symmetric_certificate.py`; certificates are in `symmetric/`.

### Certified statements

Let `H` be a group of order `m` dividing 40, put `k = 40/m`, and let `H` act
on the vertex set `{0,...,k-1} x H` by left multiplication,
`g.(j, x) = (j, g x)`.  This action is semiregular (no non-identity element
fixes a vertex) with `k` orbits of size `m`.  Every semiregular action of `H`
on 40 points is permutation-isomorphic to it: send `(j, x)` to `x.v_j` for
representatives `v_j` of the orbits.

For each class in the table there is **no graph on this vertex set that is
invariant under the action, triangle-free, and of independence number at
most 9**.  Equivalently, no 40-vertex `(3,10)`-graph has a group of
automorphisms isomorphic to `H` that acts semiregularly with `k` orbits.

| Class | `H` | Orbits | Variables | Triangle clauses | Normalisation clauses | 10-set clauses | Proof lemmas | Proof (xz) | drat-trim |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| `c10xc2-2orb` | `C10 x C2` | 2 x 20 | 42 | 444 | -- | 3,168 | 25,148 | 0.33 MB | 0.6 s |
| `dic5-2orb` | `Dic5` | 2 x 20 | 40 | 444 | -- | 2,474 | 12,668 | 0.17 MB | 0.2 s |
| `f20-2orb` | `F20` | 2 x 20 | 44 | 492 | -- | 8,772 | 89,487 | 1.17 MB | 5.0 s |
| `d10-2orb` | `D10` | 2 x 20 | 50 | 484 | -- | 21,660 | 324,773 | 4.36 MB | 38 s |
| `c10-4orb` | `C10` | 4 x 10 | 80 | 968 | 27 + 93 | 22,146 | 276,690 | 4.25 MB | 28 s |

`Dic5` is the dicyclic group `<x, y | x^10 = 1, y^2 = x^5, y x y^-1 = x^-1>`,
`F20 = AGL(1,5)` is the Frobenius group of the maps `z -> a z + b` of `Z/5`
(`a != 0`), and `D10`, `D5` are the dihedral groups of orders 20 and 10.  The
two-orbit certificates are pure (triangle clauses and 10-set clauses only),
like the C20 certificate; the four- and five-orbit certificates add the
clauses of the normalisation lemma below.  "Proof lemmas" counts the clauses of the
committed binary DRAT proof; the drat-trim times are local wall-clock times
on a heavily loaded shared machine (Apple M5 Max).

For the next three classes the DRAT proofs are far larger than the 5 MB
per-file limit, so only the separator lists are committed.  CI re-runs the
audit, which checks the separators and that the formula it writes has the
recorded SHA-256; the proof itself is regenerated with CaDiCaL 3.0.1 and
checked with drat-trim locally (command in `status.yaml`, not run in CI).

| Class | `H` | Orbits | Variables | Triangle clauses | Normalisation clauses | 10-set clauses | Proof lemmas | Proof size | drat-trim |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| `d5-4orb` | `D5` | 4 x 10 | 88 | 984 | 27 + 9 | 125,459 | 3,417,647 | 178 MB | 2,120 s |
| `q8-5orb` | `Q8` | 5 x 8 | 100 | 1,220 | 28 + 60 | 269,223 | 5,281,325 | 290 MB | 4,955 s |
| `c8-5orb` | `C8` | 5 x 8 | 100 | 1,225 | 28 + 60 | 292,542 | 6,422,834 | 360 MB | 5,349 s |

The proof columns describe the raw CaDiCaL `--unsat` proof that the local
commands below regenerate and that drat-trim checked ("Proof lemmas" is the
lemma count drat-trim reports; for `d5-4orb` the time is drat-trim's reported
verification time).  For `d5-4orb` the build step also extracted a 127 MB
core-lemma proof (2,517,278 lemmas, 40.6 MB after xz, drat-trim 407 s),
recorded in `symmetric/d5-4orb.build.json`.  The `d5-4orb` separators were
trimmed in three core rounds (168,651 to 125,459); the `q8-5orb` and
`c8-5orb` lists are the untrimmed search output.

### Consequences (pen-and-paper, not machine-checked)

1. Up to isomorphism the groups of order 20 are `C20`, `C10 x C2`, `D10`,
   `Dic5` and `F20`.  Together with the C20 certificate, the pure two-orbit
   certificates therefore exclude every group of order 20 acting
   semiregularly with two orbits.
2. Hence no 40-vertex `(3,10)`-graph is a Cayley graph.  If a group `G` of
   order 40 acts regularly, its Sylow 5-subgroup `P` is normal (the number of
   Sylow 5-subgroups divides 8 and is 1 mod 5), so `PQ` is a subgroup of
   order 20 for any subgroup `Q` of order 4 of a Sylow 2-subgroup; `PQ` acts
   semiregularly with two orbits and item 1 applies.
3. `c10-4orb` excludes every automorphism whose cycles all have length 10
   (cycle type `10^4`).  The squares of automorphisms of cycle type `20^2`,
   the fourth powers of cycle type `40^1`, and the elements of order 10 of a
   semiregular `C10 x C2`, `D10` or `Dic5` all have this cycle type, so
   `c10-4orb` alone re-covers the circulant case, the C20 certificate and
   three of the two-orbit classes.  It does not cover `F20`, which has no
   element of order 10.
4. `c10-4orb` and `d5-4orb` together exclude both groups of order 10, so no
   40-vertex `(3,10)`-graph has a semiregular automorphism group of order 10.
   A group of order 20 or 40 has a normal Sylow 5-subgroup `P` and an
   involution `t`, so `P<t>` is a subgroup of order 10, and subgroups of
   semiregular groups are semiregular.  These two classes alone therefore
   re-cover items 1 and 2, but only through the normalisation lemma.
5. `c8-5orb` excludes every automorphism of cycle type `8^5`, and with it
   every automorphism of cycle type `40^1` (its fifth power has type `8^5`).
   `q8-5orb` excludes the semiregular `Q8` actions.  The other groups of
   order 8 (`C4 x C2`, `C2^3`, `D4`) are not covered.

### Method

The encoding generalises the C20 one: one Boolean variable per `H`-orbit on
the 780 vertex pairs, the quotient of all 9,880 triangle clauses, and one
positive clause per concrete 10-vertex set `S`, namely "some pair of `S` is an
edge".  Such a clause holds in every graph of independence number at most 9,
however `S` was found, so the search heuristics never affect soundness.

- `search_symmetric_r310.py` defines the classes by generators and writes
  the search instance, the normalisation blocks and the final CNF; it also
  trims separator lists to a drat-trim core and has `check-sat`, an exact
  independence-number check for a model should one ever be found.
- `cegar_symmetric_r310.cpp` is the search back end on the CaDiCaL 3.0.1 C++
  API.  With `--up` it is an IPASIR-UP external propagator: whenever the
  pairs currently assigned false contain a 10-clique (an independent 10-set
  forced by the partial assignment) it adds that 10-set clause, and every
  complete model gets an exact independence-number check, so a run ends
  either with UNSAT or with a genuine `(3,10)`-graph.  Without `--up` it runs
  the model-by-model CEGAR loop of the C20 search, adding short separator
  clauses found by branch and bound.  The two-orbit separator lists came from
  the loop (`--k 1`), the four- and five-orbit lists from `--up` together
  with the normalisation clauses (`--extra`).
- Core trimming: CaDiCaL proves the current formula UNSAT with a DRAT proof,
  `drat-trim -c` extracts an UNSAT core, and only separators whose clause is
  in the core are kept.
- Final certificate: the audit writes the DIMACS formula, CaDiCaL 3.0.1
  (`--unsat`) proves it UNSAT with a DRAT proof, `drat-trim -C -l` extracts
  the core lemmas as a binary DRAT proof, and drat-trim verifies that proof
  again.  Only the core-lemma proof is committed (xz-compressed).  For
  `q8-5orb` and `c8-5orb` (`--no-proof-output`) drat-trim checks the raw
  CaDiCaL proof once and nothing but the separators is stored.
- `build_symmetric_certificate.py` runs the whole pipeline for one class.

### Normalisation lemma (four- and five-orbit classes)

An `H`-invariant graph is determined by its connection sets
`D_ij = { x^-1 y : (i, x) ~ (j, y) }`.  Two kinds of vertex maps commute with
every `g.` and therefore send invariant graphs to isomorphic invariant graphs:

- the right translation of a single orbit, `(j, x) -> (j, x h)` with the other
  orbits fixed, which replaces `D_0j` by `D_0j h` and `D_jj` by `h^-1 D_jj h`
  and leaves `D_00` and every `D_0l` with `l != j` unchanged;
- a relabelling of the orbits, `(j, x) -> (pi(j), x)`, which permutes the
  internal sets `D_jj`.

Call a position `{d, d^-1}` of an internal set *stable* if every conjugation
maps it to itself.  All positions are stable when `H` is abelian (five for
`C10`, four for `C8`) and for `Q8` (the only conjugates of `x` are `x` and
`x^-1`); for `D5` only the two rotation pairs are.  Let the *key* of orbit `j` be the vector of its
internal variables at the stable positions.  Given any invariant graph, first
relabel the orbits so that the keys are lexicographically non-decreasing,
then for `j = 1, ..., k-1` with `D_0j` nonempty translate orbit `j` by
`h = d^-1` for some `d` in `D_0j`.  Translations change no key and no earlier
`D_0l`, so the result is isomorphic to the original graph and satisfies

- (n) `e` is in `D_0j` whenever `D_0j` is nonempty (`j >= 1`): the binary
  clauses `-x((0,e),(j,d)) OR x((0,e),(j,e))`, `(k-1)(m-1)` of them (27 for
  four orbits of size 10, 28 for five orbits of size 8);
- (s) `key_0 <= key_1 <= ... <= key_(k-1)`: one clause per forbidden
  configuration "equal prefix, then 1 against 0", without auxiliary
  variables.

So a `(3,10)`-graph in the class would yield a model of the normalised
formula, and UNSAT of that formula excludes the class.  The audit checks the
hypotheses mechanically (both commutation properties and the stability of
the key positions) and rebuilds both blocks; the lemma itself is the hand
argument above.

### Audit

`audit_symmetric_certificate.py` uses only the Python standard library and
does not import the search code.  For a class it

1. builds the group from its full multiplication law, checks the group
   axioms, and checks the invariants that identify it among the groups of its
   order (abelian or not, element-order histogram);
2. builds the action of every element and checks that it is faithful and
   semiregular;
3. recomputes the pair orbits, the triangle clauses, the normalisation blocks
   (when requested) and one clause per separator line, after checking that
   each line lists ten distinct vertices;
4. checks that a given DIMACS file is exactly this formula (`--check-cnf`) or
   writes it (`--write-cnf`).

The committed proofs refer to the formula written by the audit, so the CNF
files are not committed; they are regenerated byte for byte.

SHA-256 of the committed files (each `<class>.build.json` beside them
records the final build step: CaDiCaL options, timings and drat-trim
summary):

```text
cb3fc8a19d1d46e6609cdd34e910852a7c30a0d192157feff77829676c0afa71  symmetric/c10xc2-2orb.separators.txt.xz
9196015b435c8375f456c9784b307cec0c0201bb60439d987578165b0a008fdc  symmetric/c10xc2-2orb.drat.xz
3e5fc65b37fe5f90c62b9e4b654a7b316ced9221859e011f6afdb691cdcf9a53  symmetric/dic5-2orb.separators.txt.xz
9ebefa3ba909637f8318aa9d27e0e79900be7d2fa3169ff53a4c27e9f21f957a  symmetric/dic5-2orb.drat.xz
be22cb0267a612c635c6ed13757449b8ae098e8091e40ee509af269a383f743c  symmetric/f20-2orb.separators.txt.xz
da23988d3099b2e060b93080f912bf08a6e8ff69c38a13a3699acf4ccbfca5c7  symmetric/f20-2orb.drat.xz
ae0ae1d6f6f2280f642b0bc0e7d2d57834f3f20e6a1218cc754fb62882b48ad7  symmetric/d10-2orb.separators.txt.xz
6c31867abaa1b341ccc61e022ed98542c03dd733bb8f08e180dad4e4f11bc437  symmetric/d10-2orb.drat.xz
2bd4e27729718573138f392768530c9ed37bedf360fbe09ff744d8a90038f352  symmetric/c10-4orb.separators.txt.xz
3575294b1feb798cbd28a1254c5af41d26c26ef789425470259f5b2d17190e03  symmetric/c10-4orb.drat.xz
28d2d9ce4085b3282b17713c37e57b6b4b87814d1ec7937a92e0dd5569bb4dc0  symmetric/d5-4orb.separators.txt.xz
8f7355a5c2b5b435724597360deb35d3cdd251fcd6037cccc088b0a00f6e976c  symmetric/q8-5orb.separators.txt.xz
189b55136dd823bbfb41b1effcd37e30002fcd77498cd3db2607451b603cb462  symmetric/c8-5orb.separators.txt.xz
```

SHA-256 of the CNF files written by the audit with the commands below:

```text
e55ec00928f6c250e4ac993044f324282921f7ef04598a8c008959673678c16d  /tmp/r310-c10xc2-2orb.cnf
855674742fcf30e55e1f88de2ae6547096ef2004cdb40f0726d1147d82f2c105  /tmp/r310-dic5-2orb.cnf
dc4d776d2decf023f3aca0209f462f16e3bc15373b56702d8e6af512be7bccf8  /tmp/r310-f20-2orb.cnf
9d6bc946c4e7350819d74a82fbb9809a9297b040711f87410ad4b1ce9639f6a5  /tmp/r310-d10-2orb.cnf
73e3f95d8707846eaf75d12957f5b09d94a10a8c5c3deb0f5d24bdea22be1d02  /tmp/r310-c10-4orb.cnf
7c6e1822ef33c1c073c1d8fe6fa25bedfc080f44050291325da6738558c99c2c  /tmp/r310-d5-4orb.cnf
42a69ef999a4c653e1268ece7e020c6c99dac91848b9f851497af19c34026beb  /tmp/r310-q8-5orb.cnf
071704c2b10c71893e9e06e564863184fbc28ce05f73ce3eb0227a2cb8b934c1  /tmp/r310-c8-5orb.cnf
```

SHA-256 of the raw CaDiCaL 3.0.1 `--unsat` proofs that drat-trim checked for
the three classes whose proofs are not committed (regenerating the
`d5-4orb` proof with the command below reproduced it byte for byte on the
same machine; other builds or platforms may produce a different valid proof):

```text
f8905f653ff412ec6e9bb4962d6d5327009bc0c799e04a2bd4ceaaecdd652fe3  /tmp/r310-d5-4orb.drat (178,315,102 bytes)
5189558b0c0f3a1d26628379bae66c20a90381ed9c5f55a268ac80e36ecb8160  /tmp/r310-q8-5orb.drat (289,693,016 bytes)
fc039656b902c4af9f4f0758c8c4d6a03a85fdd08f1ff2ae75415eae756cc2d9  /tmp/r310-c8-5orb.drat (360,045,378 bytes)
```

### Reproduce the checks

From `problems/ramsey-r3-10`, with `drat-trim` on `PATH`:

```bash
python3 audit_symmetric_certificate.py f20-2orb \
  symmetric/f20-2orb.separators.txt.xz --write-cnf /tmp/r310-f20-2orb.cnf
xz -dc symmetric/f20-2orb.drat.xz | drat-trim /tmp/r310-f20-2orb.cnf -i
```

Expected: `"status": "SEMANTICS VERIFIED"` and `s VERIFIED`.  For
`c10-4orb` add `--normalised --sorted-orbits` to the audit call.  The
`verify` entries of `status.yaml` run these commands for the five classes
with committed proofs (each under 25 s locally).

For `d5-4orb`, `q8-5orb` and `c8-5orb` the proof has to be regenerated
(local only; needs the `cadical` binary, whose exit code 20 means UNSAT):

```bash
python3 audit_symmetric_certificate.py d5-4orb symmetric/d5-4orb.separators.txt.xz \
  --normalised --sorted-orbits --write-cnf /tmp/r310-d5-4orb.cnf \
  --expect-sha256 7c6e1822ef33c1c073c1d8fe6fa25bedfc080f44050291325da6738558c99c2c
cadical -q --unsat /tmp/r310-d5-4orb.cnf /tmp/r310-d5-4orb.drat
drat-trim /tmp/r310-d5-4orb.cnf /tmp/r310-d5-4orb.drat
```

The first command alone is the CI check for these classes.  Locally the
audit takes 2-4 s.  On the loaded shared machine CaDiCaL took about 4-8 min
for `d5-4orb` and 46 min each for `q8-5orb` and `c8-5orb`, and drat-trim
about 35 min (`d5-4orb`), 83 min (`q8-5orb`) and 89 min (`c8-5orb`).

To regenerate a certificate from scratch (local only; needs a C++17
compiler, CaDiCaL >= 2.0 as library and binary, and drat-trim; point
`--cadical-prefix` at the CaDiCaL installation, default `/opt/homebrew`):

```bash
python3 build_symmetric_certificate.py dic5-2orb --outdir /tmp/r310-symmetric
python3 build_symmetric_certificate.py c10-4orb --normalise --outdir /tmp/r310-symmetric
```

Measured locally on the loaded machine: the `dic5-2orb` example takes about
6 s and the `c10-4orb` example about 5 minutes (search 30 s, three trimming
rounds, final proof; it ends with 23,062 separators, the committed list had
one more trimming round).  The searches behind the committed four- and
five-orbit lists took 50 s (`c10-4orb`), 15 min (`d5-4orb`), 44 min
(`q8-5orb`) and 54 min (`c8-5orb`); for `d5-4orb` the three trimming rounds
and the final proof took about two more hours.  The committed separator
lists come from scratch runs of the same back end, so a regenerated
certificate is valid but need not be byte-identical.

### Attempted without a result

- `c5-8orb` (`C5` with eight orbits, 156 variables, normalisation clauses
  included): the `--up` search had collected 2.26 million separators after
  5.2 hours without finishing and was stopped.  It ran past the 90-minute
  budget only because the session supervising it was interrupted.  An
  exclusion would cover every automorphism of cycle type `5^8`.
- Not attempted: `C4 x C2`, `C2^3` and `D4` with five orbits, `C4` and
  `C2 x C2` with ten orbits, and fixed-point-free involutions (`C2` with 20
  orbits, 400 variables).  The generator, back end and audit already define
  these classes (`c4xc2-5orb`, `c2xc2xc2-5orb`, `d4-5orb`, `c4-10orb`,
  `c2xc2-10orb`, `c2-20orb`).

### What is not claimed

- `R(3,10)` is not determined.
- Only the listed semiregular actions are excluded.  Automorphisms with fixed
  points or with cycles of different lengths (for example an involution with
  fixed points) are not covered, and neither are the classes attempted
  without a result.
- The normalisation lemma and the consequences above are pen-and-paper
  arguments; what is machine-checked is that the audited formulas are UNSAT.
- For `d5-4orb`, `q8-5orb` and `c8-5orb` drat-trim checked the proofs on one
  local machine only; CI checks the separators and the formula hash, not the
  proof.
- No literature novelty is claimed.

### Literature note

- Circulant graphs: the one-orbit cyclic case is implied by published
  cyclic-graph results (see above); `c10-4orb` re-covers it.
- Cayley and vertex-transitive graphs: Holt and Royle enumerated all
  vertex-transitive graphs on fewer than 48 vertices, so consequence 2 (no
  40-vertex Cayley `(3,10)`-graph) can in principle be read off that census
  and is presumably known; we did not look for an explicit statement.
- We are not aware of a published treatment of the multi-orbit classes
  above, but this addition did not include a new literature search beyond
  the sources cited here, so no novelty is claimed.

## Published context

- Vigleik Angeltveit, [R(3,10) <= 41](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p30/pdf/), *Electronic Journal of Combinatorics* 32(4), 2025, #P4.30.
- Stanislaw Radziszowski, [Small Ramsey Numbers, revision 18](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/), *Electronic Journal of Combinatorics*, 24 April 2026.
- Derek Holt and Gordon Royle, A census of small transitive groups and vertex-transitive graphs, *Journal of Symbolic Computation* 101 (2020).
