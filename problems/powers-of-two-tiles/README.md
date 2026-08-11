# Powers-of-two translational tiles of every odd cardinality

This note gives an unreviewed negative answer to the yes/no clause of Question
9 in Benjamini--Kozma--Tzalik, *The Number of Tiles of \(\mathbb Z^d\)*,
Electronic Journal of Combinatorics 33(3) (2026), P3.28. The question asks
whether the only translational tiles contained in
\(\{1,2,4,\ldots,2^n\}\) have cardinality one or two.

**Result.** There is such a tile of every positive odd cardinality. In
particular, the smallest-cardinality counterexample to the suggested
one-or-two restriction is

\[
A=\{1,4,16\},\qquad
B=\{0,1,2\}+9\mathbb Z.
\]

This settles that yes/no clause, but it does **not** determine the exact total
number of tiles requested in the first sentence of Question 9.

Primary source:

- <https://arxiv.org/abs/2303.07956v2>
- <https://arxiv.org/html/2303.07956v2>

## Periodic tiling criterion

A finite set \(A\subset\mathbb Z\) tiles \(\mathbb Z\) by translations if
there is a set \(B\subset\mathbb Z\) such that every integer has exactly one
representation \(a+b\), with \(a\in A\) and \(b\in B\). We write this as
\(A\mathbin{\dot+}B=\mathbb Z\).

If the sum map

\[
A\times C\longrightarrow\mathbb Z/M\mathbb Z,\qquad
(a,c)\longmapsto a+c\pmod M
\]

is bijective, then

\[
A\mathbin{\dot+}(C+M\mathbb Z)=\mathbb Z. \tag{1}
\]

Indeed, bijectivity gives the unique pair \((a,c)\) representing the residue
of any integer \(z\). There is then a unique \(k\in\mathbb Z\) with
\(z=a+c+kM\). Conversely, reducing two representations modulo \(M\) first
identifies \(a,c\), after which their integer quotients agree.

For the displayed three-element example,

\[
A\equiv\{1,4,7\}\pmod9.
\]

The three translates of \(C=\{0,1,2\}\) are the disjoint residue blocks
\(\{1,2,3\}\), \(\{4,5,6\}\), and \(\{7,8,0\}\). They cover
\(\mathbb Z/9\mathbb Z\), so (1) proves the tiling and its uniqueness.

## Tiles of every odd cardinality

Let \(t\geq3\) be odd, let

\[
r=\operatorname{ord}_t(2),\qquad q=2^r-1,
\]

and define

\[
A_t=\{2^{ri}:0\leq i<t\}. \tag{2}
\]

Since \(2^r\equiv1\pmod t\), we have \(t\mid q\). In particular,
\(q^2\) is divisible by \(tq\). For \(0\leq i<t\), the binomial theorem
therefore gives

\[
2^{ri}=(1+q)^i\equiv1+iq\pmod{tq}. \tag{3}
\]

Let \(C=\{0,1,\ldots,q-1\}\). By (3), the residues of \(A_t+C\) are

\[
1+iq+j,\qquad 0\leq i<t,\quad0\leq j<q.
\]

For fixed \(i\), these form the interval
\(\{iq+1,\ldots,(i+1)q\}\). The \(t\) intervals are consecutive and
disjoint, and together give \(1,\ldots,tq\), with the final value representing
zero modulo \(tq\). Thus the modular sum map is bijective, and (1) yields

\[
A_t\mathbin{\dot+}
\bigl(\{0,1,\ldots,q-1\}+tq\mathbb Z\bigr)=\mathbb Z. \tag{4}
\]

The exponents in (2) are distinct, so \(A_t\) has exactly \(t\) elements.
Together with the trivial singleton case, every positive odd cardinality
occurs.

## Shifting the exponents

Scaling preserves a translational tiling. More precisely, if
\(A\mathbin{\dot+}B=\mathbb Z\) and \(d\geq1\), then

\[
dA\mathbin{\dot+}
\bigl(dB+\{0,1,\ldots,d-1\}\bigr)=\mathbb Z. \tag{5}
\]

To prove this, uniquely write an arbitrary integer as \(z=dn+c\), where
\(0\leq c<d\), and then uniquely write \(n=a+b\). This produces
\(z=da+(db+c)\); reducing modulo \(d\) and then dividing by \(d\) proves
uniqueness.

Apply (5) to (4) with \(d=2^s\). For every \(s\geq0\),

\[
\begin{aligned}
A_{t,s}&=\{2^{s+ri}:0\leq i<t\},\\
B_{t,s}&=\{0,1,\ldots,2^sq-1\}+2^stq\mathbb Z
\end{aligned}
\]

satisfy \(A_{t,s}\mathbin{\dot+}B_{t,s}=\mathbb Z\). The largest exponent is
\(s+r(t-1)\); consequently, this tile lies inside
\(\{1,2,4,\ldots,2^n\}\) whenever \(n\geq s+r(t-1)\).

## Exact checker and reproduction

[`power_two_tile_counterexample.py`](power_two_tile_counterexample.py)
computes \(r,q\), checks the congruence (3), and exhaustively verifies that
every residue modulo the stated period has exactly one representation. From
the repository root:

```bash
python3 problems/powers-of-two-tiles/power_two_tile_counterexample.py 3
python3 problems/powers-of-two-tiles/power_two_tile_counterexample.py 5
python3 problems/powers-of-two-tiles/power_two_tile_counterexample.py 9
python3 problems/powers-of-two-tiles/power_two_tile_counterexample.py 9 --shift 2
```

The final 2026-08-11 check passed for cardinalities 3, 5, and 9, including a
shifted family. This result was developed separately from pre-existing work
elsewhere in this workspace. Targeted public searches through that date found
no earlier posted answer, but that is not a literature review or a priority
claim. The proof and checker have not been peer reviewed.
