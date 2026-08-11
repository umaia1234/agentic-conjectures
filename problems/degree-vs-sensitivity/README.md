# Degree versus sensitivity: exact n=14 aggregate constraints

## Outcome and scope

The [FrontierMath problem](https://epoch.ai/frontiermath/open-problems/degree-sensitivity-boolean)
asks for a Boolean multilinear polynomial improving the known exponent
`log(6)/log(3)`.  The first unresolved fully sensitive parameter set examined
here is `n=14`, `degree<=5`, normalized by

```text
f(0)=0 and f(e_i)=1 for i=1,...,14.
```

No such truth table was found and no nonexistence proof was obtained.  The
result of the full search is therefore **UNKNOWN**.  This note records exact
necessary conditions that substantially shrink that case; it does not claim
that the conditions are new to the literature.

## Exact layer bounds

Let `B_t` be the number of inputs of Hamming weight `t` on which `f=1`, and
put `q(t)=B_t/binom(14,t)`.  Symmetrizing a degree-five multilinear polynomial
shows that `q` is a univariate polynomial of degree at most five, with
`q(0)=0`, `q(1)=1`, and `0<=q(t)<=1` on all integer layers.

Interpolating `q(2)` at nodes `(0,1,5,9,13,14)` gives coefficients

```text
(-22/65, 231/208, 77/240, -11/80, 21/208, -11/195).
```

Choosing the endpoints of the unknown `[0,1]` values according to coefficient
sign gives `q(2)>=11/12`.  Hence

```text
B_2 >= 84,
```

so at most seven of the 91 pair inputs can be zero.  Two further exact
interpolations, retaining `q(2)`, give

```text
300 B_3 - 1925 B_2 >= -108801,
 21 B_3 -  180 B_2 <=  -11375.
```

There is a stronger integrality consequence.  Interpolation from layers
`0,...,5` expresses every later `B_t` as an integer linear form in
`B_0,...,B_5`.  Exhausting the resulting two-dimensional integer intervals
leaves exactly 247 possible `(B_2,B_3,B_4,B_5)` profiles:

| `B_2` | possible `B_3` interval | profiles |
|---:|---:|---:|
| 84 | 178 | 1 |
| 85 | 184--186 | 5 |
| 86 | 190--195 | 11 |
| 87 | 196--204 | 24 |
| 88 | 203--212 | 31 |
| 89 | 210--221 | 42 |
| 90 | 215--229 | 58 |
| 91 | 222--238 | 75 |

In the most constrained case the complete layer vector is forced to

```text
(B_0,...,B_14) =
(0,14,84,178,123,28,525,1716,2478,1974,878,186,7,0,1).
```

Run the dependency-free exact certificate and enumeration with:

```bash
python3 problems/degree-vs-sensitivity/degree_sensitivity_pair_bound.py
```

Every displayed rational identity and cleared integer inequality is asserted
inside the script.

## Truth-table search

`degree_sensitivity_cpsat.py` represents all 16,384 Boolean truth values and
computes the full Möbius transform through 114,688 shared subtraction
equations.  All coefficients above degree five are fixed to zero.  It also
adds the 247-profile table and a safe symmetry split according to the maximum
degree of the graph of zero-valued pairs.

A six-variable degree-three regression instance is found and independently
verified in about 0.02 seconds.  For the target case, unsplit HiGHS and CP-SAT
runs and the two extreme graph branches (`0` and `7`) all ended at their time
limits with status `UNKNOWN`; no certificate file was emitted.  In particular,
the 120-second strengthened runs did not decide either extreme branch, and the
six intermediate branches were not exhausted.

One reproduction command, after installing OR-Tools in a disposable virtual
environment, is:

```bash
python -m venv /tmp/degree-sat-venv
/tmp/degree-sat-venv/bin/pip install ortools
/tmp/degree-sat-venv/bin/python \
  problems/degree-vs-sensitivity/degree_sensitivity_cpsat.py \
  --n 14 --degree 5 --max-zero-degree 7 --time-limit 120 --workers 4
```

`UNKNOWN` is only a timeout status.  It is neither evidence that a construction
exists nor evidence that none exists.
