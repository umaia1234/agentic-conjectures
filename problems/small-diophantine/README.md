# Small Diophantine equations: independent low-degree attempt

## Outcome

No solution meeting Epoch's threshold was found.  In particular, this folder
does **not** claim that any of the six remaining equations has been solved.
It records exact negative results for three low-degree rational-curve ansatz
classes and a small exact spot-check of a Pell-factor ansatz.

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
