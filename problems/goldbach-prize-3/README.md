**English** | [한국어](README.ko.md)

# Let's Prove Goldbach prize problem 3

The official [prize page](https://www.dimostriamogoldbach.it/en/prizes/)
listed problem 3 at **€200** with status **“No solutions received”** when
retrieved on 2026-08-12. For fixed integers
(1<n_1<n_2<\cdots<n_k), it defines

\[
S=\{y>0:n_i\nmid y\text{ for every }i,\quad n_1\mid y+1\}
\]

and says:

> “It is required to prove that this set can be expressed as”

\[
 S=\{f(x):g(x)\in
 \{n_2a_2+\cdots+n_ka_k:a_i\in I_i\}\}.
\]

Here (f,g:\mathbb N^\star\to\mathbb N) may use arithmetic, modulo,
rounding, and finitely many cases, while each (I_i) need only be a finite
subset of the positive integers.

## Result

The stated representation always exists. Put

\[
 M=\prod_{j=2}^k n_j,qquad
 C=\sum_{j=3}^k n_j,qquad
 \rho(q)=1+((q-1)\bmod M).
\]

Thus (1\leq\rho(q)\leq M). Choose

\[
\begin{aligned}
 I_2&=\{r\in\{1,\ldots,M\}:n_j\nmid n_1r-1
       \text{ for every }j=2,\ldots,k\},\\
 I_j&=\{1\}\quad(3\leq j\leq k),\\
 f(q)&=n_1q-1,\\
 g(q)&=n_2\rho(q)+C.
\end{aligned}
\]

The set (I_2) is finite and positive by construction; all later sets are
positive singletons. Their finite sumset is exactly

\[
  \{n_2r+C:r\in I_2\}.
\]

For every (q>0), (q\equiv\rho(q)\pmod M). Since every (n_j),
(j\geq2), divides (M),

\[
 n_j\mid n_1q-1\quad\Longleftrightarrow\quad
 n_j\mid n_1\rho(q)-1.
\]

Consequently (g(q)) belongs to the finite sumset exactly when (f(q))
avoids all (n_2,\ldots,n_k). Also (f(q)+1=n_1q), and (f(q)) is positive
and not divisible by (n_1). This proves the required equality in both
directions. The (k=2) case is included, with (C=0).

## Statement faithfulness and scope

The Lean list `ns` is exactly ([n_2,\ldots,n_k]). Its head supplies (n_2),
its tail sum is (C), and the product of the list is (M). The formal target
includes positivity, nondivisibility by (n_1) and every member of `ns`, and
divisibility of (y+1) by (n_1). The theorem assumes only the weaker facts
actually used—(n_1>1), a nonempty list, and every later modulus (>1)—so
the source's strict chain is a sufficient special case.

There is an important specification caveat. The advertised wording imposes
no bound on (|I_i|), no requirement that the bound be independent of the
parameters, and no separate formula-language restriction on membership in
the finite sets. This construction uses that freedom to store one complete
period in (I_2). If the sponsor intended a uniformly small set or a more
restrictive closed form, that condition is absent from the posted problem
and would define a stronger problem. The repository claims only the literal
statement above.

## Machine verification

The sorry-free module
[`GoldbachPrize3.lean`](../../AgenticConjectures/GoldbachPrize3.lean) proves:

- `residueSet_finite`: the chosen (I_2) is finite;
- `proved`: the exact two-sided set equality for all admissible parameters
  (through the reusable lemma `representation`).

```bash
lake env lean AgenticConjectures/GoldbachPrize3.lean
```

See [DETAILS.md](DETAILS.md) for the proof map and trust boundary.

## Research status

Targeted searches for the exact displayed representation and its defining
phrases found no public solution beyond the canonical prize page on
2026-08-12.

The construction has not been reviewed or accepted by the prize sponsor.
This repository therefore claims neither the prize nor novelty or priority.
No external submission has been made; that requires human approval.
