# Floridian solitaire: immediate losses for every `n > 6`

This directory contains an unreviewed solution of the second research question
in Meyerowitz--Curran--Locke--Low, *Floridian Solitaire: A New Variant of
Bulgarian Solitaire*, arXiv:2608.08313v1. The paper supplies immediate losses
for odd `n` and for `n = 1 (mod 3)`, and leaves `n = 0,2 (mod 6)` open.

**Result.** Every integer `n > 6` has an immediate-loss position, hence a
losing position.

For the formerly open classes, the construction uses `r` parts whose distinct
sizes form the gap-two block

\[
r+2+2\delta,r+4+2\delta,\ldots,r+2+2\delta+2h,
\qquad \delta\in\{0,1\}.
\]

Any selection that can leave a separated partition must select a nonempty
lower prefix of whole size classes. The reduced smallest class is therefore
\(r+1+2\delta\), while the output has \(p=r+1\) parts. It contains the
forbidden \(p\)-part (\(\delta=0\)) or \((p+2)\)-part (\(\delta=1\)), so no
selection is legal. For even \(r\), the two block families realize every even
total, in steps of two, in

\[
J_r=[r^2+2r,2r^2+r],\qquad I_r=[r^2+4r,2r^2+3r].
\]

Together these cover the open residue classes except 18 and 20; explicit
immediate losses there are \((1,5,5,7)\) and \((4,4,6,6)\).

## Files

- [`PROOF.md`](PROOF.md): definitions, full construction, exact interval
  coverage, exceptional cases, and completion using the paper's families.
- [`INDEPENDENT_PROOF.md`](INDEPENDENT_PROOF.md): independently written second
  derivation.
- [`verify.py`](verify.py): literal exhaustive alpha-selection checker, also
  comparing the paper's \(T(n)\) test with a direct \(\Omega\) move.
- [`verify_independent.py`](verify_independent.py): a separately implemented
  checker using whole-size-class choices.

## Reproduction and recorded checks

From the repository root, run:

```bash
python3 problems/floridian-solitaire/verify.py
python3 problems/floridian-solitaire/verify_independent.py
```

The default range is \(n=7,\ldots,500\). The final 2026-08-11 run of
`verify.py` checked all 494 witnesses and 334,670 nonempty selection
profiles, finding no legal move. It also checked the \(T(n)\) criterion
against direct \(\Omega\) evaluation for every separated intermediate. The
independent checker covered all 494 sizes, including the 165 formerly open
residue-class cases. A separate indexed subset audit of the new residue
classes reached \(n=10000\).

`verify.py` accepts `--start`, `--end`, and `--show-witnesses`; for
example:

```bash
python3 problems/floridian-solitaire/verify.py --start 18 --end 20 --show-witnesses
```

This result was developed separately from pre-existing work elsewhere in this
workspace. Targeted public searches through 2026-08-11 found no earlier posted
answer, but that is not a literature review or a priority claim. The theorem
and computations have not been peer reviewed.
