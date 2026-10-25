# Small Diophantine equations: independent low-degree attempt

## Outcome

No solution meeting Epoch's threshold was found.  In particular, this folder
does **not** claim that any of the six remaining equations has been solved.
It records exact negative results for three low-degree rational-curve ansatz
classes and a small exact spot-check of a Pell-factor ansatz.  A later section
adds an exact finiteness result: every curve `z = A(y)` with `A` a rational
polynomial of degree at most 5 carries only finitely many integer points.

The equations are

```text
z^2 + y^2*z + x^3 + a*x + b = 0
```

for

```text
(a,b) = (0,-2), (-1,-1), (0,-3), (0,3), (-1,-2), (-1,2).
```

The primary sources are Epoch AI's
[problem page](https://epoch.ai/frontiermath/open-problems/small-diophantine)
and its [March 2026 note on the two polynomial families already found](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf).
Epoch asks for three distinct integer solutions with `|x| > 10^50` as a
machine-checkable proxy for infinitude.

## Exact negative results

Run:

```bash
python problems/small-diophantine/analyze_ansatze.py
```

The script performs exact `QQ` arithmetic and checks:

1. The unbalanced polynomial ansatz

   ```text
   deg(x), deg(y), deg(z) = (2,1,3)
   ```

   in one parameter, with nonzero leading coefficient of `y`.  After the top
   three coefficients are eliminated, the last equations split into two
   branches.  For `a=0`, each branch has an immediate rational obstruction.
   For `a=-1`, eliminating the remaining variable gives monic sextics with no
   rational roots for all three relevant constants `b=-1,-2,2`.

2. Every rational nonvertical affine line on each of the six cubic surfaces.
   An affine parameter change puts such a line in the form

   ```text
   x=-d^2*T, y=d^3*T+D0, z=T+V0.
   ```

   A lexicographic Groebner basis gives a univariate polynomial in `d`; none
   of the six polynomials has a rational root.

3. The generic branch with `x,y,z` all quadratic in one parameter.  Its
   coefficient equations reduce to

   ```text
   a=(39U^2+216U-16)/(3*q^8*U^2)
   b=(918U^3+2088U^2-4320U-128)/(27*q^12*U^3).
   ```

   For `a=0`, the required quadratic in `U` has nonsquare discriminant.  For
   `a=-1`, eliminating `q` gives a degree-six polynomial with no rational
   roots for `b=-1,-2,2`.  The symmetric branch reduces to the affine-line
   case above.

These are ansatz obstructions only; they say nothing about the existence of
more complicated curves or non-parametric infinite families.

## Pell-factor attempt

Instead of forcing the discriminant to be a square polynomial, one can try

```text
y(t)^4 - 4*(x(t)^3+a*x(t)+b) = G(t)^2 R(t),
```

where `R(t)=v^2` is an indefinite Pell equation.  The smallest nonsplit
choice examined here is

```text
x=-D*t^2+C,
y=t+Q,
G=2*D*t^2-L*t+J,
R=D*t^2+L*t+M.
```

`search_pell_factor.py` uses exact Groebner elimination for the following
integer `Q` spot-checks:

```text
(a,b)= (0,-2): Q=-5,-4,-3,-2,-1,1,2
(a,b)= (0,-3): Q=1
(a,b)= (0, 3): Q=1,2
(a,b)=(-1,-2): Q=2
```

In each case the final polynomial in `D` has degree 48 and no rational root.
This range is deliberately stated narrowly: rational `Q`, other integer `Q`,
and higher-degree Pell factorizations remain untested.

Run the spot-check (it can take roughly a minute and substantial memory):

```bash
python problems/small-diophantine/search_pell_factor.py
```

## Curves on which z is a polynomial in y

This section was added by Claude Opus 5.5 (Claude Code) on 2026-10-24.  It is
an exact finiteness statement for one explicit class of curves.  It produces
no solutions and solves none of the equations.

### Statement

For `A` in `QQ[y]` let `C_A` be the curve cut out on the surface by
`z = A(y)`.

**Claim.** For each of the six pairs `(a,b)` and every `A` in `QQ[y]` with
`deg A <= 5`, the curve `C_A` contains only finitely many integer points.  So
no infinite set of integer solutions lies on a single curve of this form.

The finer statements behind the claim are listed below; `Q = 2A + y^2`
throughout.

* `a = 0`, `deg A = 2`.  `C_A` has genus 0 and one place at infinity exactly
  when `y^4 - 4b - Q^2 = lam*(y-r)^3*(y-s)`.  These `A` correspond one-to-one
  to the affine rational points `(r,k)` of `C_b : k^2 = r^4 - 4b`, via

  ```text
  Q = k + (2r^3/k)(y-r) + (r^2(r^4-12b)/k^3)(y-r)^2.
  ```

  `C_b` maps birationally to `E_b : Y^2 = X^3 + 16bX`, by
  `(r,k) -> (2(k+r^2), 4r(k+r^2))`.
  * `b = -3`: `E_{-3}` has rank 0 (2-isogeny descent with local obstructions
    at 2 and 3) and torsion `{O,(0,0)}`.  So `C_{-3}` has no affine rational
    point, and no such curve exists.
  * `b = -2, 3`: `E_b` has a point of infinite order, so there are infinitely
    many such curves, each with a polynomial parametrisation over `QQ`.  For
    example:

    ```text
    b=-2: A(y) = -(y^2-16y-44)/27,   x = 729U^4/26 + 252U/13,  y = 729U^3/26 + 239/13
    b= 3: A(y) = -(11y^2-48y+54)/2,  x = -4U^4/99 + 56U/33,    y = 122/33 - 4U^3/99
    ```

    On every one of these curves, every point with `y` in `ZZ` has `x = 0`.
    To see this, write `r = R/T` in lowest terms.  Then `x != 0` would make

    ```text
    V = b*(T*Dh*y + R*Eh),  Dh = 3R^8 - 24bR^4T^4 - 16b^2T^8,
                            Eh = R^8 + 24bR^4T^4 - 48b^2T^8
    ```

    a nonzero integer cube, because `V = (x*T^3*k^2/(y-r))^3`.  But `V` is
    never a cube mod 13 when `b = -2`, and `V = 3 or 6 (mod 9)` when `b = 3`.
* `a = 0`, `deg A = 4, 5`.  No `A` in `QQ[y]` gives a curve of genus 0 with
  one place at infinity.
* `a = -1`, `deg A` in `{0, 2, 4, 5}`.  Every `C_A` has positive genus.
* `deg A = 1, 3`, both values of `a`.  These degrees lead to polynomial
  components `x = X(y)` with `deg X = 1, 2`, that is, lines and the
  `(2,1,3)` ansatz.  None is defined over `QQ`.  This re-derives results 1
  and 2 of the first section by an independent elimination.

### Reduction to the checked statements

Put `P = y^4 - Q^2`.  Since `(2z+y^2)^2 = y^4 - 4(x^3+ax+b)`, projecting to
`(x,y)` identifies `C_A` with the plane curve `4(x^3+ax+b) = P(y)`, and
integer points go to integer points.

The involution `z -> -z-y^2` sends `C_A` to `C_{-A-y^2}`.  So for
`deg A = 2` we may assume the leading coefficient of `A` is not `-1`.  Then
`n = deg P` is `2 deg A` when `deg A >= 2`, is `3` when `deg A = 1`, and is at
most 2 when `A` is constant.

Both `x` and `y` are integral over the polynomial ring in the other variable,
so the places at infinity are the places above `y = oo`.  By Siegel's theorem,
infinitely many integer points require a component of genus 0 with at most two
places at infinity.

*Lemma A (`a = 0`).* Write the curve as `x^3 = F(y)` with `F = P/4 - b`.
* If `F` is not a cube in `QQbar[y]`, the curve is irreducible and
  `(x,y) -> y` is a cyclic triple cover.  Riemann-Hurwitz gives genus `B - 2`,
  where `B` counts the roots of `F` of multiplicity prime to 3, plus `oo` when
  `3 ∤ n`.  If `3 | n`, there are three places at infinity.
* So infinitely many integer points force one of two things.  Either there is a
  polynomial component (`F = X^3` with `X` in `QQ[y]`; if instead `F = c*X^3`
  with `c` not a rational cube, rational points need `X(y) = 0`).  Or
  `3 ∤ n` and `F` has exactly one root `s` of multiplicity prime to 3.
* That root is Galois-stable, hence rational, so `F = c(y-s)^m H(y)^3` with
  `H` in `QQ[y]` monic and `m = n (mod 3)`.

*Lemma B (`a = -1`).* Write the curve as `x^3 - x = g(y)` with `g = P/4 - b`.
* The critical values of `x^3 - x` are `±2/(3√3)`, each with one double and
  one simple preimage.  So for an irreducible curve, the triple cover
  `(x,y) -> y` ramifies only above `y = oo` (fully, if `3 ∤ n`) and above the
  roots of `g ∓ 2/(3√3)` of odd multiplicity (index 2).
* Riemann-Hurwitz gives `2g_C - 2 = -6 + 2[3 ∤ n] + O_+ + O_-`, where `O_±`
  counts the odd-multiplicity roots of `g ∓ 2/(3√3)`.
* Conjugation `√3 -> -√3` swaps these two polynomials, so `O_+ = O_-`.  Also
  `O_+ = n (mod 2)`.  For even `n` with `3 ∤ n`, genus 0 would need
  `O_+ = 1`, which contradicts parity, so the genus is positive.
* If `3 | n`, there are three places at infinity.
* A reducible curve has a component `x = X(y)`.  If `X` is not in `QQ[y]`, it
  meets its conjugate in finitely many points.  The residual conic
  `(2x+X)^2 + 3X^2 = 4` has bounded `X`.
* So only a component `x = X(y)` with `X` in `QQ[y]` and `3 deg X = n` can
  carry infinitely many integer points.

Applying the two lemmas degree by degree:

| `deg A` | `n` | `a = 0` | `a = -1` |
|---|---|---|---|
| 0 | 2, or `P = 0` | `B = 2` needs `beta^2 = -b`; `P = 0` needs `-b` a cube; both impossible | positive genus; `P = 0` needs a rational root of `N`: none |
| 1 | 3 | line `x = xi*y + eta`: none over `QQ` | same |
| 2 | 4 | `F = c(y-s)(y-r)^3`: the `C_b` analysis above | positive genus |
| 3 | 6 | `F = X^3`, `deg X = 2`: none over `QQ` | component `x = X(y)`, `deg X = 2`: none over `QQ` |
| 4 | 8 | `F = c(y-s)^2 H^3`, `deg H = 2`: none over `QQ` | positive genus |
| 5 | 10 | `F = c(y-s) H^3`, `deg H = 3`: none over `QQ` | positive genus |

How the "none over `QQ`" entries for `deg A = 4, 5` are checked:
* The shape `y^4 - 4b - Q^2 = -q^2 (y-s)^m H^3` is set up with `s` scaled to
  0 or 1 and `b` kept as an unknown.
* The top coefficients determine `Q`.  The remaining equations in `q^2` and
  the coefficients of `H` are eliminated with resultants.
* Every rational branch ends in "nonzero constant = 0", with one exception:
  `deg A = 4`, `s = 0` forces `H = y^2` and `b = -1/(16q^2)`, which is not one
  of the six values of `b`.  For `deg A = 4`, `s = 1` and for `deg A = 5`, no
  rational `b` at all occurs.

Literature inputs are used as stated and are not formalised:
* Siegel's theorem on integral points.
* The Riemann-Hurwitz formula.
* The 2-isogeny descent rank formula (Silverman-Tate, *Rational Points on
  Elliptic Curves*, III.6).
* Injectivity of reduction on torsion at odd primes of good reduction.

The scripts check the finite algebraic and arithmetic statements that the
argument reduces to.

### Reproduction

```bash
cd problems/small-diophantine
python3 analyze_z_poly_y.py                  # sympy only; ~3 s; 106 checks
gp -q crosscheck_z_poly_y.gp < /dev/null     # PARI/GP >= 2.15; < 1 s; 38 checks
```

`analyze_z_poly_y.py` checks the following:
* the `deg A = 2` classification modulo `k^2 = r^4 - 4b`;
* the map `C_b -> E_b`;
* the 2-isogeny descent for `b = -3`, by local insolubility of four quartics
  mod `3^2` or `2^4`;
* torsion via point counts mod 5 and 7;
* the explicit families, both as identities and with `Fraction` spot checks;
* the identity for `V` and all residue cases mod 13 and mod 9;
* the `deg A = 4, 5` eliminations;
* the line and `(2,1,3)` eliminations for all six pairs.

`crosscheck_z_poly_y.gp` is an independent re-check in PARI/GP:
* it rebuilds the `deg A = 4, 5` systems in a different normalisation
  (`Q = q*W` with `W` monic and `t = 1/q^2`) and repeats the eliminations;
* it recomputes the factorisation `y^4 - 4b - Q^2 = lam*(y-r)^3*(y-s)` and
  the residue obstructions from scratch;
* it confirms `rank E_{-3}(QQ) = 0` and the rank of `E_{-2}` and `E_3` with
  `ellrank`;
* it re-verifies both families.

The runtimes above were measured on an Apple M5 Max.

### What is not claimed

* No solution with `|x| > 10^50`, and no new solution of any size.  None of
  the six equations is claimed solved, and the status stays `partial`.
* Only curves on which `z` is a polynomial in `y` of degree at most 5 are
  covered.  The result says nothing about the following:
  * `deg A >= 6`.  The next cases are `deg A = 6` (components `x = X(y)` with
    `deg X = 4`, both values of `a`) and `deg A = 7, 8` for `a = 0`.
  * Curves on which `z` is not a function of `y` alone.
  * Solutions that lie on no curve with infinitely many integer points.
* The finiteness is ineffective (Siegel).  No bound on the integer points of
  a given `C_A` is claimed.
* The rational families for `b = -2, 3` are expected: the surfaces are
  unirational over `QQ`.  Only the integrality obstruction carries content.
* No novelty is claimed.  We did not check whether these exclusions appear in
  the literature, and Epoch's note on the two known families was not
  consulted for this section.
* Exploratory runs are not committed and not claimed: a divisor-based search
  over `|x| <= 3*10^5` for each equation, and a search for quadrics
  `z = gamma*y^2 + r10*x + r01*y + r00` through five or more of the small
  solutions.  Neither found a family.
