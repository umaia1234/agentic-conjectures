**English** | [한국어](DETAILS.ko.md)

# Mathematical details for prize problem 2

Fix \(1<n_1<n_2<n_3\), and write

\[
 P=n_1n_2n_3,
 \qquad
 R=(r_0<r_1<\cdots<r_{A-1})
\]

for the increasing list of positive residues below \(P\) divisible by none
of the three moduli. Since every \(n_i>1\), the residue \(1\) belongs to
\(R\), so \(A>0\).

## Periodic decomposition

Each \(n_i\) divides \(P\). Therefore, for every \(q\) and every positive
\(r\),

\[
 n_i\mid Pq+r\quad\Longleftrightarrow\quad n_i\mid r.
\]

It follows that \(Pq+r_j\) is allowed for every \(q\) and \(j<A\).
Conversely, if \(y\) is allowed, division by \(P\) gives

\[
 y=P\left\lfloor\frac yP\right\rfloor+(y\bmod P).
\]

Its remainder cannot be zero: otherwise \(P\mid y\), hence
\(n_1\mid y\). The remainder is therefore a positive allowed member of
\([0,P)\), so it is a unique \(r_j\). Thus every allowed value has a unique
period-and-residue decomposition.

Within a period, the sorted residues are strictly increasing. Between
successive periods,

\[
 Pq+r_{A-1}<P(q+1)+r_0
\]

because \(r_{A-1}<P\) and \(r_0>0\). Hence the zero-based enumeration is

\[
 F_0(m)=P\left\lfloor\frac mA\right\rfloor+r_{m\bmod A}. \tag{2}
\]

The source's one-based formula is \(F(x)=F_0(x-1)\).

## Lean proof map

`residueFinset` filters `Finset.range P` by `Allowed`, `residueList` sorts
that finset, and `countPerPeriod` is its length. In `formula0`, `List.getD`
encodes the finite residue table. Its default value is unreachable because
`countPerPeriod_pos` and `Nat.mod_lt` prove that the selected index is in
range.

The formal proof establishes three properties of `formula0`:

1. `formula0_strictMono` proves strict increase, separately treating indices
   in the same period and in different periods.
2. `formula0_allowed` proves that every output is allowed by reducing each
   divisibility test to its residue.
3. `formula0_surjective_on_allowed` decomposes every allowed number into its
   period quotient and unique sorted-residue index.

Mathlib's characterization of `Nat.nth` from strict monotonicity, mapping,
and surjectivity then yields `exact_formula0`. Replacing \(m\) by \(x-1\)
gives `exact_formula`. Finally, rewriting with that identity makes
`Nat.dist` zero, and `proved` obtains
\(2\operatorname{dist}\leq n_3^2\).

## Specification and trust boundary

Equation (2) is an exact finite lookup formula for each fixed triple. Its
lookup table has \(A\) parameter-dependent entries. The Lean proposition
does not encode a grammar of admissible formulas, so it does not settle a
possible stronger reading in which the number of written cases must be
uniformly bounded independently of the moduli. This limitation concerns
faithfulness to an underspecified syntactic condition, not the verified
enumeration identity.

The proof is checked by Lean's kernel against mathlib. It uses no `sorry`,
added axiom, `native_decide`, numerical search, external solver, or
unverified certificate. `tSpace` is noncomputably presented with `Nat.nth`,
but the equal function `formula` is defined by finite filtering, sorting,
division, and lookup.
