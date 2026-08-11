# A certified C20-bicirculant subcase of R(3,10)

Status: **computationally certified, but not peer reviewed**.

This directory records an exact search related to the open Ramsey-number
problem `R(3,10) in {40,41}`.  It does **not** determine `R(3,10)`.

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
prove the value 40.  The result below excludes only one automorphism class of
that search space.

## Certified statement

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

## Encoding

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

## Certificate artifacts

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

## Reproduce the checks

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

## Published context

- Vigleik Angeltveit, [R(3,10) <= 41](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p30/pdf/), *Electronic Journal of Combinatorics* 32(4), 2025, #P4.30.
- Stanislaw Radziszowski, [Small Ramsey Numbers, revision 18](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/), *Electronic Journal of Combinatorics*, 24 April 2026.
