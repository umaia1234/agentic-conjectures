**English** | [한국어](DETAILS.ko.md)

# Theta arithmetic sum: identities, an upper bound and the computation

Throughout, $k$ is an odd prime and $n=(k-1)/2$. The objects are

\[
S'(h,k)=\sum_{j=1}^{k-1}(-1)^{j+1+\lfloor hj/k\rfloor},\qquad
S(k)=\sum_{h=1}^{k-1}S'(h,k).
\]

The paper writes $S(h,k)$ for $S'(h,k)$; the upstream Lean file uses `S'` to avoid
overloading. Sections 2–6 are exact identities; Section 7 is an unconditional upper bound;
Section 8 says precisely what the open conjectures need; Section 9 describes the computation.

## 1. Notation and statements

Let $((x))=x-\lfloor x\rfloor-\tfrac12$ for $x\notin\mathbb Z$ and $((x))=0$ for
$x\in\mathbb Z$. For $c\ge1$ and $\gcd(h,c)=1$ put

\[
s(h,c)=\sum_{i=1}^{c-1}\Bigl(\Bigl(\frac ic\Bigr)\Bigr)\Bigl(\Bigl(\frac{hi}c\Bigr)\Bigr),\qquad
s_3(h,c)=\sum_{i=1}^{c-1}(-1)^i\Bigl(\Bigl(\frac{hi}c\Bigr)\Bigr),\qquad
s_4(v,k)=\sum_{j=1}^{k-1}(-1)^{\lfloor vj/k\rfloor}.
\]

Here $s(h,c)$ is the classical Dedekind sum; $s$ and $s_3$ depend only on $h\bmod c$. The
paper's $S(h,k)$ (our $S'$), $s_3$ and $s_4$ are three of the six *Hardy sums* of Berndt
[Be78], which were also studied by Goldberg [Go81], Berndt and Goldberg [BG84] and
Sitaramachandrarao [Si87]; Zhang [Zh03], Dağlı [Da20] and others study their power and hybrid
mean values.
Finally

\[
H(k)=\sum_{\substack{1\le v\le k-2\\ v\text{ odd}}}\frac1v,\qquad
V(k)=\sum_{\substack{3\le v\le k-2\\ v\text{ odd}}}s_3(k\bmod v,\;v).
\]

$H(k)$ is the paper's $H(k)=\sum_{j\le k-1,\ j\text{ odd}}1/j$, since $k-1$ is even.

The upstream file states, for odd primes $k$ (numbering of arXiv v1):

- Conjecture 1.1: $S(k)>0$;
- Conjecture 4.1: $S(k)>k$ for $k>5$;
- Conjecture 4.2: $S(k)>2k$ for $k>233$;
- Conjecture 4.3: $S(k)>3k$ for $k>3119$;
- Conjecture 4.4: for every $n\in\mathbb N$, $S(k)>nk$ for all sufficiently large $k$.

Conjecture 3.3 first appears in arXiv v2 (2 Dec 2025); v3 (9 Jan 2026) has the same text, on
p. 4. It is not in the upstream file, which follows v1:

> “Let $C_1$ and $C_2$ be any fixed positive numbers. Let $\epsilon>0$ be fixed. Then, for all
> primes $k$ sufficiently large, $C_1k<S(k)<C_2k^{1+\epsilon}$.”

Since the constants are arbitrary, the conjecture is equivalent to two separate statements,
each with its own threshold:

- *first inequality:* for every $C_1>0$, $S(k)>C_1k$ for all sufficiently large primes $k$;
- *second inequality:* for every $C_2>0$ and $\varepsilon>0$, $S(k)<C_2k^{1+\varepsilon}$
  for all sufficiently large primes $k$.

The first is equivalent to Conjecture 4.4: take $C_1=n+1$ in one direction and
$n=\lceil C_1\rceil$ in the other. Section 7 proves the second. Lean states the conjecture and
both inequalities (`statement_3_3`, `statement_3_3_lower`, `statement_3_3_upper`) and proves
the two equivalences (`statement_3_3_iff`, `statement_3_3_lower_iff`), but neither
inequality.

## 2. Reflection: the Lean-checked reductions

**Lemma 2.1.** If $0<j<k$ and $k\nmid hj$, then
$\lfloor hj/k\rfloor+\lfloor h(k-j)/k\rfloor=h-1$.

*Proof.* The two quotients add up to the integer $h$, and neither is an integer. $\square$

For prime $k$ and $1\le h,j\le k-1$ we always have $k\nmid hj$. Pair $j$ with $k-j$; they
differ because $k$ is odd.

1. **$S'(h,k)=0$ for odd $h$.** The exponents of the two paired terms add up to
   $(j+1)+(k-j+1)+(h-1)=k+h+1$, which is odd, so the terms cancel. This is the prime case of
   the paper's Lemma 5.7 (v1), Proposition 7.5 (v3); for odd $k$ and $\gcd(h,k)=1$ it is
   also part of [Zh03, Lemma 5]. Lean: `S'_eq_zero_of_odd`.
2. **$S'(k-v,k)=s_4(v,k)$ for $0<v<k$.** Here
   $\lfloor (k-v)j/k\rfloor=j-1-\lfloor vj/k\rfloor$, so the exponent
   $2j-\lfloor vj/k\rfloor$ has the parity of $\lfloor vj/k\rfloor$. Lean: `S'_sub_eq_s4`.
3. **$s_4(v,k)=0$ for even $v$.** The paired exponents add up to $v-1$, which is odd. Lean:
   `s4_eq_zero_of_even`.
4. **Odd $v$.** The paired exponents add up to the even number $v-1$, so
   $s_4(v,k)=2\sum_{j=1}^{n}(-1)^{\lfloor vj/k\rfloor}$. Lean: `s4_eq_two_mul`.

Summing item 2 over $v=k-h$, and then using items 3 and 4:

\[
S(k)=\sum_{v=1}^{k-1}s_4(v,k)=\sum_{a=1}^{k-1}\sum_{b=1}^{k-1}(-1)^{\lfloor ab/k\rfloor}
=\sum_{\substack{v<k\\ v\text{ odd}}}s_4(v,k)
=2\sum_{\substack{v<k\\ v\text{ odd}}}\ \sum_{j=1}^{n}(-1)^{\lfloor vj/k\rfloor}.
\tag{2.1}
\]

In Lean these are `S_eq_sum_s4`, `S_eq_sum_sq`, `S_eq_sum_odd` and `S_eq_fastS`. The last form
costs about $k^2/4$ parity tests. The kernel evaluates it for every odd prime $k<300$ in
`small_primes`. Lean also proves `floor_eq`: the upstream $\mathbb Q$-floor
$\lfloor (hj:\mathbb Q)/k\rfloor_+$ equals the natural-number quotient `h * j / k`. All of
this is about the upstream definition itself.

## 3. Lattice form and the Dedekind-sum closed form (method A)

**Proposition 3.1 (lattice form).**

\[
S(k)=-2\sum_{s=1}^{n}\sum_{t=1}^{n}(-1)^{\lfloor 4st/k\rfloor}.
\]

*Proof.* For $A,B\subseteq\{1,\dots,k-1\}$ put
$Q(A,B)=\sum_{a\in A,\,b\in B}(-1)^{\lfloor ab/k\rfloor}$, and let $E$ and $O$ be the even
and the odd elements.

- Since $k$ is odd, $a\mapsto k-a$ maps $E$ onto $O$.
- By Lemma 2.1, $(-1)^{\lfloor (k-a)b/k\rfloor}=(-1)^{b-1}(-1)^{\lfloor ab/k\rfloor}$.
- Hence $Q(O,E)=-Q(E,E)$ and $Q(O,O)=Q(E,O)$.
- By symmetry $Q(E,O)=Q(O,E)$.

So (2.1) gives $S(k)=Q(E,E)+Q(E,O)+Q(O,E)+Q(O,O)=-2Q(E,E)$. Finally $E=\{2s:1\le s\le n\}$.
$\square$

Two sawtooth identities follow by checking one period. For $x\notin\mathbb Z$, and for
$1\le t\le k-1$:

\[
(-1)^{\lfloor x\rfloor}=2((x))-4((x/2)),\qquad
[\,t\le n\,]=\tfrac12+\Bigl(\Bigl(\frac{2t}k\Bigr)\Bigr)-2\Bigl(\Bigl(\frac tk\Bigr)\Bigr).
\tag{3.1}
\]

Take $c$ coprime to $k$, and multiply the second identity by $((ct/k))$. Sum over
$1\le t\le k-1$ and substitute $u\equiv 2t\pmod k$; note that $\sum_t((ct/k))=0$. With
$\bar2$ the inverse of $2$ modulo $k$, this gives

\[
\sum_{t=1}^{n}\Bigl(\Bigl(\frac{ct}k\Bigr)\Bigr)=s(c\bar2,k)-2s(c,k).
\tag{3.2}
\]

Now apply the first identity of (3.1) at $x=4mt/k$, which is not an integer for
$1\le m,t\le n$, and then (3.2) with $c=4m$ and $c=2m$:

\[
\sum_{t=1}^{n}(-1)^{\lfloor 4mt/k\rfloor}
=2\bigl(s(2m,k)-2s(4m,k)\bigr)-4\bigl(s(m,k)-2s(2m,k)\bigr)
=10s(2m,k)-4s(m,k)-4s(4m,k).
\]

**Proposition 3.2 (Dedekind form).** Summing over $m$ and using Proposition 3.1,

\[
S(k)=\sum_{m=1}^{n}\bigl(8s(m,k)-20s(2m,k)+8s(4m,k)\bigr).
\tag{D}
\]

*Prior art.* Sitaramachandrarao [Si87] expressed the Hardy sums through Dedekind sums. In
particular $S'(h,k)=8s(h,2k)+8s(2h,k)-20s(h,k)$ when $h+k$ is odd. For odd $k$ and $h=2m$,
$s(2m,2k)=s(m,k)$, so each term of (D) is $S'(2m,k)$; since the odd $h$ contribute
nothing (Section 2), (D) follows at once. The lattice derivation above does not use
[Si87], but (D) is not new in substance. We take the formula from its quotation in
[Da20, (3)] and did not consult [Si87] itself; `verify.py` checks it for every odd $k<150$.

Method A (`s_dedekind.cpp`) evaluates (D) with the classical continued-fraction formula for
Dedekind sums [Ba77, Hi77, Kn77]. Let $0<h<k$ with $\gcd(h,k)=1$. Let the Euclidean algorithm
on $(k,h)$ produce the quotients $q_1,\dots,q_r$, and let $hh'\equiv1\pmod k$ with $0<h'<k$.
Then

\[
12k\,s(h,k)=h+h'+k\Bigl(\sum_{i=1}^{r}(-1)^{i+1}q_i-2+(-1)^r\Bigr).
\tag{BHK}
\]

*Proof.* We did not consult [Ba77, Hi77, Kn77], so here is a proof from Dedekind's
reciprocity law [RG72], $12hk\bigl(s(h,k)+s(k,h)\bigr)=h^2+k^2+1-3hk$. Induct on $r$. If
$r=1$, then $h=h'=1$ and $q_1=k$, and (BHK) is the classical value
$12k\,s(1,k)=(k-1)(k-2)$. If $r\ge2$, let $c=k-q_1h$ be the next remainder, and let
$0<c^*<h$ with $cc^*\equiv1\pmod h$. The Euclidean algorithm on $(h,c)$ has the quotients
$q_2,\dots,q_r$, so by induction
$12h\,s(c,h)=c+c^*+h\bigl(\sum_{i=2}^{r}(-1)^iq_i-2-(-1)^r\bigr)$. Reciprocity, with
$s(k,h)=s(c,h)$ and $k(k-c)=q_1hk$, then gives

\[
12k\,s(h,k)=h+\frac{1-kc^*}h+k\Bigl(\sum_{i=1}^{r}(-1)^{i+1}q_i-1+(-1)^r\Bigr).
\]

Finally $h'=k+(1-kc^*)/h$. It is an integer because $kc^*\equiv cc^*\equiv1\pmod h$; it lies
in $(0,k)$ because $1\le h-c^*\le h-1$; and $hh'=kh+1-kc^*\equiv1\pmod k$. $\square$

One extended Euclidean run per Dedekind sum costs $O(\log k)$, so a prime costs
$O(k\log k)$. The total is accumulated in exact 128-bit integers, and the program checks that
it is divisible by $12k$. `verify.py` checks (BHK) against the definition for all coprime
$0<h<k\le500$, and (D) for every prime $k\le400$.

## 4. Reciprocity and the exact formula (method B)

**Proposition 4.1.** For odd $v\ge1$ and $\gcd(v,k)=1$,

\[
s_4(v,k)=\frac kv-1+2s_3(k\bmod v,\;v).
\tag{4.1}
\]

*Proof.* Group $j\in[1,k-1]$ by $q=\lfloor vj/k\rfloor\in[0,v-1]$. Put
$F(q)=\lfloor qk/v\rfloor$ for $0\le q\le v-1$ and $F(v)=k-1$. Since $qk/v\notin\mathbb Z$
for $0<q<v$, exactly $F(q+1)-F(q)$ indices $j$ have $\lfloor vj/k\rfloor=q$. Summation by
parts, with $v$ odd, gives

\[
s_4(v,k)=\sum_{q=0}^{v-1}(-1)^q\bigl(F(q+1)-F(q)\bigr)
=2\sum_{q=1}^{v-1}(-1)^{q-1}F(q)+k-1.
\]

Now substitute $F(q)=qk/v-((qk/v))-\tfrac12$. Use
$\sum_{q=1}^{v-1}(-1)^{q-1}q=-(v-1)/2$, $\sum_{q=1}^{v-1}(-1)^{q-1}=0$ and
$((qk/v))=((q(k\bmod v)/v))$. This gives
$s_4(v,k)=-k(v-1)/v+2s_3(k\bmod v,v)+k-1$. $\square$

In other words, $2s_3(k,v)-s_4(v,k)=1-k/v$ for odd $v$. Reciprocity laws of this kind for
the Hardy sums go back to Berndt [Be78] and Goldberg [Go81]; see also [Si87]. The proof
above is elementary.

**Lemma 4.2.** For odd $c$ and $\gcd(h,c)=1$, $s_3(h,c)=2s(h,c)-4s(2h,c)$.

*Proof.* The map $i\mapsto c-i$ sends odd $i$ to even $i$. It changes the sign of both
$(-1)^i$ and $((hi/c))$, so the odd and even parts of $s_3$ are equal. Hence
$s_3(h,c)=2\sum_{t=1}^{(c-1)/2}((2ht/c))$, and (3.2), with modulus $c$, finishes the proof.
$\square$

This is formula (1) of [Da20], where it is attributed to [Si87].

Put $c=k\bmod v$ and $T(c,v)=12v\,s(c,v)\in\mathbb Z$. Then (4.1) and Lemma 4.2 give
$12v\,s_4(v,k)=12k-12v+4T(c,v)-8T(2c\bmod v,v)$. Method B (`s_hardy.cpp`) computes $T$
exactly from Dedekind reciprocity [RG72]:

\[
c\,T(c,v)+v\,T(v\bmod c,\;c)=c^2+v^2+1-3cv,\qquad T(1,v)=(v-1)(v-2).
\tag{4.2}
\]

This also costs $O(k\log k)$ per prime. The program uses 64-bit integers with overflow checks
and an exactness check on every term.

**Theorem 4.3 (exact formula).** For every odd prime $k$,

\[
S(k)=k\,H(k)-\frac{k-1}2+2V(k).
\tag{4.3}
\]

*Proof.* By (2.1), $S(k)=\sum_{v\text{ odd},\,v\le k-2}s_4(v,k)$. Here $s_4(1,k)=k-1$, and
(4.1) applies for $3\le v\le k-2$. There are $n$ odd $v$ in total. $\square$

Since $H(k)=\tfrac12\ln k+\tfrac12(\ln2+\gamma)+O(1/k)$, with $\gamma$ Euler's constant,

\[
\frac{S(k)}k=\frac12\ln k+c_0+\frac{2V(k)}k+O\Bigl(\frac1k\Bigr),\qquad
c_0=\frac{\ln2+\gamma-1}2=0.1351\ldots
\tag{4.4}
\]

The main term $\tfrac12 k\ln k$ is thus explicit, and every conjecture is a statement about
$V(k)$ (Section 8).

Theorem 4.3 is the decomposition behind the paper's lower bound (Section 5), with each term
evaluated exactly by (4.1). We have not seen (4.3) stated in this form, but every ingredient
is classical; related relations for integer-valued analogues of Dedekind sums appear in
[BD82] and [Me97]. `verify.py` checks (4.1), Lemma 4.2 and (4.2) against the definitions on
ranges of coprime pairs, and (4.3) exactly, in rational arithmetic, for every prime
$k\le400$.

Lean checks (4.1) and (4.3) in general: they are `s4_eq_reciprocity` and `S_eq_exact`, with
$s_3$, $H$ and $V$ written as `s3`, `H` and `V`. In Lean, $H$ and $V$ sum over all odd $v<k$;
for odd $k$ this is the same range, and the extra term $v=1$ of `V` is $0$. Instead of
summation by parts, the Lean proof of (4.1) expands $(-1)^n=1+2\sum_{q=1}^{n}(-1)^q$ and
counts the $j\in[1,k-1]$ with $\lfloor vj/k\rfloor\ge q$; there are $k-1-\lfloor qk/v\rfloor$
of them.

## 5. The exact error term in the paper's lower bound

The paper's lower bound (Theorem 6.3 of v3, Theorem 6.4 of v1) has four steps:

1. It writes $S(k)=\tfrac{(k-1)^2}2-2\sum_{j\text{ odd}}r(j,k)$, with
   $r(j,k)=\sum_{h=1}^{k-1}\bigl(\lfloor hj/k\rfloor-2\lfloor hj/2k\rfloor\bigr)$.
2. It defines $\varepsilon_j(k)=r(j,k)/k-(j-1)/(2j)$.
3. It proves $\varepsilon_j(k)\le(j-1)/(2k)$.
4. It concludes $S(k)\ge-\tfrac{k-1}2+kH(k)-\tfrac{(k-1)(k+1)}4$.

The authors then write that "a proper upper bound for $\epsilon_j(k)$ is crucial".

**Proposition 5.1.** For odd $j$ with $1\le j\le k-2$,

\[
r(j,k)=\frac{k-1-s_4(j,k)}2=\frac{k(j-1)}{2j}-s_3(k\bmod j,\;j),
\qquad\text{so}\qquad
\varepsilon_j(k)=-\frac{s_3(k\bmod j,\;j)}k\quad\text{exactly.}
\]

*Proof.* $\lfloor hj/k\rfloor-2\lfloor hj/2k\rfloor$ is the parity of $\lfloor hj/k\rfloor$.
So $r(j,k)$ counts the $h$ with $\lfloor hj/k\rfloor$ odd, which is $(k-1-s_4(j,k))/2$. Now
apply (4.1). $\square$

The paper's bound $\varepsilon_j(k)\le(j-1)/(2k)$ is therefore the termwise bound
$s_3(c,j)\ge-(j-1)/2$. Summing the exact values over $j$ gives back (4.3).

This termwise bound is within a factor about $2$ of the truth on infinitely many terms. By
Section 6, $s_3(k\bmod j,j)=-(j-1)^2/(4j)$, that is $\varepsilon_j(k)=(j-1)^2/(4jk)$, whenever
$j\mid 2k-1$. So no better termwise bound is possible; an improvement has to come from
cancellation between different $j$. `verify.py` checks the identity for $r(j,k)$ for every
prime $k\le400$ and every odd $j\le k-2$.

## 6. Divisor terms

**Proposition 6.1.** Let $j\ge3$ be odd. If $j\mid 2k-1$, then
$s_3(k\bmod j,j)=-(j-1)^2/(4j)$; if $j\mid 2k+1$, then $s_3(k\bmod j,j)=+(j-1)^2/(4j)$.

*Proof.* If $j\mid 2k-1$, then $k\equiv\bar2\pmod j$.

- By Lemma 4.2 and $s(\bar h,j)=s(h,j)$, $s_3(\bar2,j)=2s(2,j)-4s(1,j)$.
- The classical values are $s(1,j)=\frac{(j-1)(j-2)}{12j}$ and, for odd $j$,
  $s(2,j)=\frac{(j-1)(j-5)}{24j}$ [RG72].
- Their combination is $-(j-1)^2/(4j)$.

If $j\mid 2k+1$, then $k\equiv-\bar2\pmod j$, and $s_3(-h,j)=-s_3(h,j)$. $\square$

Write $2k\mp1=jd$. A term with $j\mid 2k-1$ adds $-(j-1)^2/(2jk)\approx-1/d$ to $2V(k)/k$.
Over all divisors $j\ge3$ of $2k-1$, these terms therefore contribute about
$-(\sigma_{-1}(2k-1)-1)$ to $S(k)/k$. The divisors of $2k+1$ contribute about
$+(\sigma_{-1}(2k+1)-1)$.

These terms are unbounded along the primes. For odd $M$, Dirichlet's theorem gives infinitely
many primes $k\equiv(M+1)/2\pmod M$; for them $M\mid 2k-1$, so
$\sigma_{-1}(2k-1)\ge\sigma_{-1}(M)$, and $\sigma_{-1}$ is unbounded on the odd numbers. On the
other hand $\sigma_{-1}(m)\le\prod_{p\mid m}p/(p-1)=O(\log\log m)$ by Mertens' theorem, so
these terms are of order at most $\log\log k$, far below the main term $\tfrac12\ln k$. The
extremes of the data fit this picture:

- Over primes $10^3<k\le2\cdot10^6$, the smallest $E(k)=S(k)/k-\tfrac12\ln k$ is $-2.160$ at
  $k=750749$, where $2k-1=3^5\cdot37\cdot167$.
- The largest is $+2.363$ at $k=1735651$, where $2k+1=3\cdot11\cdot37\cdot2843$.

`verify.py` checks Proposition 6.1 for every prime $k\le400$ and prints these extremes.

## 7. An unconditional upper bound

**Theorem 7.1.** For every odd prime $k$,

\[
|S(k)|<6k(1+\ln k)^2+8k.
\]

In particular $S(k)=O(k\log^2k)$. The second inequality of Conjecture 3.3 therefore holds: for
every $C_2>0$ and $\varepsilon>0$, $6k(1+\ln k)^2+8k<C_2k^{1+\varepsilon}$ for all
sufficiently large $k$, so $S(k)<C_2k^{1+\varepsilon}$ for all sufficiently large primes $k$.
In Lean this is `statement_3_3_upper`, which is stated there but not proved.

The proof below is pen-and-paper and not machine-checked. One independent review (a separate
AI session) re-derived every step and found no gap. For every prime $k\le400$, `verify.py`
checks each claim of the proof:

- in Step 1, the residue claim and the inequality;
- in Step 2, both estimates, for every $h$;
- in Step 3, the continuant identity, the conditions on every quadruple, Facts 1–3 and each
  link of the displayed chain;
- both links of the conclusion.

Links that involve logarithms are checked in floating point, everything else exactly.
`verify.py` also checks the final bound on every row of the committed table. There it holds
with at least 40-fold slack (the largest ratio of $|S(k)|$ to the bound is $0.024$, at $k=7$),
so that check is only a sanity check.

*Step 1: $|S(k)|\le18\sum_{h=1}^{k-1}|s(h,k)|$.* Take $c\in\{1,2,4\}$, which is invertible
modulo $k$. The $2n$ residues $\pm cm$, $1\le m\le n$, are exactly $1,\dots,k-1$, and
$|s(-h,k)|=|s(h,k)|$. Hence $\sum_{m=1}^{n}|s(cm,k)|=\tfrac12\sum_h|s(h,k)|$ for each $c$, and
(D) gives $|S(k)|\le\tfrac{8+20+8}2\sum_h|s(h,k)|$.

*Step 2: $|s(h,k)|<(A(k/h)+5)/12$, where $A(k/h)=q_1+\dots+q_r$ is the sum of the partial
quotients.* In (BHK), $0<h+h'<2k$ and
$\bigl|\sum(-1)^{i+1}q_i-2+(-1)^r\bigr|\le A(k/h)+3$.

*Step 3: $\sum_{h=1}^{k-1}A(k/h)\le4k(1+\ln k)^2$.* Run the Euclidean algorithm on $(k,h)$:
$r_0=k$, $r_1=h$ and $r_{i-1}=q_ir_i+r_{i+1}$, ending with $r_m=1$ and $r_{m+1}=0$. With the
continuants $Q_{-1}=0$, $Q_0=1$ and $Q_i=q_iQ_{i-1}+Q_{i-2}$, induction on $i$ gives

\[
k=Q_{i-1}r_{i-1}+Q_{i-2}r_i\qquad(1\le i\le m).
\]

Map each step $(h,i)$ to the quadruple $(Q,Q',a,b)=(Q_{i-1},Q_{i-2},r_{i-1},r_i)$. Then
$Qa+Q'b=k$, $a>b\ge1$, $Q\ge1$, $0\le Q'\le Q$, and $q_i\le a/b\le k/(Qb)$. Three facts
bound the sum:

1. *At most two steps give the same quadruple.* $Q'=0$ only for $i=1$. Otherwise
   $Q/Q'=[q_{i-1};q_{i-2},\dots,q_1]$ with all entries $\ge1$. This determines
   $(q_1,\dots,q_{i-1})$ up to the two continued-fraction expansions of a rational. Running
   the algorithm backwards from $(a,b)$ then recovers $h=r_1$.
2. *Fixing $Q$ and $b$ leaves at most two quadruples.* $\gcd(Q,b)$ divides the prime $k$.
   It cannot equal $k$, since then $Q\ge k$ and $Qa\ge2k$. So $Q'$ is fixed modulo $Q$ by
   $Q'b\equiv k\pmod Q$, which leaves at most two values in $[0,Q]$, and
   $a=(k-Q'b)/Q$ is then fixed.
3. *Ranges.* $b<a\le k/Q$, so $b<k/Q$ and $Q<k$.

Therefore

\[
\sum_{h=1}^{k-1}A(k/h)\le2\sum_{(Q,Q',a,b)}\frac ab
\le4\sum_{Q=1}^{k-1}\ \sum_{1\le b<k/Q}\frac k{Qb}
\le4k\sum_{Q=1}^{k-1}\frac{1+\ln(k/Q)}Q\le4k(1+\ln k)^2.
\]

*Conclusion.* $|S(k)|\le18\sum_h|s(h,k)|<\tfrac32\sum_hA(k/h)+\tfrac{15}2(k-1)
<6k(1+\ln k)^2+8k$. $\square$

The exact average is $\sum_hA(k/h)=\tfrac6{\pi^2}k\ln^2k+O(k\log k(\log\log k)^2)$
[YK75]; for $k=999983$ the ratio $\sum_hA(k/h)/(k\ln^2k)$ is $0.719$. Steps 1 and 2 with
[YK75] therefore already give $S(k)=O(k\log^2k)$; Step 3 only makes the bound explicit for
every $k$. Theorem 7.1 is far from sharp. By (4.4) and the data, $S(k)$ is about
$\tfrac12k\ln k$; the extra logarithm is the price of the triangle inequality.

## 8. What the conjectures need

Conjectures 1.1 and 4.1–4.4 remain open, and so does the first inequality of Conjecture 3.3,
which is equivalent to Conjecture 4.4 (Section 1). By (4.3) and (4.4):

- **Conjecture 1.1** is equivalent to $V(k)>\tfrac12\bigl(\tfrac{k-1}2-kH(k)\bigr)$, a
  bound of order $-\tfrac14k\ln k$, for every odd prime $k$ (Lean: `statement_1_1_iff`).
- **Conjecture 4.4** is equivalent to $\tfrac12\ln k+2V(k)/k\to\infty$ along the primes.
  The bound $\liminf V(k)/(k\ln k)>-\tfrac14$ is sufficient.

So a lower bound $V(k)\ge-(\tfrac14-\delta)k\ln k$ for all large $k$ would settle
Conjecture 4.4. It would also settle Conjectures 1.1 and 4.1–4.3 beyond an explicit point,
and the computation could then cover the finite range.

The tools above do not reach such a bound:

- **Termwise bounds.** These must allow $s_3=-(j-1)^2/(4j)$ at the divisors of $2k-1$
  (Section 6).
- **Averaging partial quotients.** As in Section 7, this gives only $|V(k)|=O(k\log^2k)$,
  one logarithm too many.
- **Dirichlet characters.** Proposition 8.1 below writes $S(k)$ exactly as a weighted sum
  over the odd characters modulo $k$. We know of no result that bounds it from below.

**Proposition 8.1 (character form).** For every prime $k\ge5$,

\[
S(k)=\frac{4k}{(k-1)\pi^2}\sum_{\chi(-1)=-1}|L(1,\chi)|^2\,|2\bar\chi(2)-1|^2\,
\bigl(2\bar\chi(2)-1\bigr)\,B_{1,\bar\chi},
\qquad B_{1,\bar\chi}=\frac1k\sum_{a=1}^{k-1}a\,\bar\chi(a),
\]

where $\chi$ runs over the odd Dirichlet characters modulo $k$.

*Proof.* Let $\chi$ be odd. The partial-fraction expansion of the cotangent gives
$\sum_a\chi(a)\cot(\pi a/k)=(2k/\pi)L(1,\chi)$. With the cotangent formula for $s(a,k)$
[RG72] this gives $\sum_a\chi(a)s(a,k)=(k/\pi^2)|L(1,\chi)|^2$, the evaluation behind
Walum's identity [Wa82]; even characters give $0$, since $s(-a,k)=-s(a,k)$. By (3.1),
$\sum_{m\le n}\bar\chi(m)=(\chi(2)-2)B_{1,\bar\chi}$. Expand $s(cm,k)$ in characters, insert
both evaluations into (D), and use $(8-20x+8x^2)(\bar x-2)=4(2x-1)|2x-1|^2$ for
$x=\bar\chi(2)$. $\square$

Proposition 8.1 is a direct consequence of [Zh03, Lemma 5], which expands each $S'(h,k)$
with $k$ odd and $\gcd(h,k)=1$ over the odd characters. For prime $k$ and even $h$ it reads
$S'(h,k)=-\frac{16k}{(k-1)\pi^2}\sum_{\chi(-1)=-1}\chi(h)|L(1,\chi\chi_2^0)|^2$, with
$\chi_2^0$ the principal character modulo $2$. Sum it over the even $h$, and use
$|L(1,\chi\chi_2^0)|=\tfrac12|2-\chi(2)|\,|L(1,\chi)|$ and $|2-\chi(2)|=|2\chi(2)-1|$; after
replacing $\chi$ by $\bar\chi$ this is Proposition 8.1.

Here $B_{1,\bar\chi}=\tfrac i\pi\,\tau(\bar\chi)L(1,\chi)$ with the Gauss sum
$\tau(\bar\chi)=\sum_a\bar\chi(a)e^{2\pi ia/k}$, so $|B_{1,\bar\chi}|=\sqrt k\,|L(1,\chi)|/\pi$.
Conjecture 1.1 is therefore the positivity of a hybrid mean value of $L(1,\chi)$ and Gauss
sums. `verify.py` checks Proposition 8.1, the expansion quoted from [Zh03, Lemma 5] and the
value of $|B_{1,\bar\chi}|$ in floating point for every prime $5\le k\le100$, with
$L(1,\chi)$ computed independently from the digamma function.

*Heuristic, not a proof.* Section 6 suggests that
$E(k)=S(k)/k-\tfrac12\ln k=c_0+2V(k)/k$ fluctuates on the scale $\log\log k$. The data agree:

- over primes $10^3<k\le2\cdot10^6$, $E(k)$ stays within $[-2.2,2.4]$;
- the decade means of $E(k)$ are about $0.24$;
- least squares over $k>10^3$ gives $S(k)/k\approx0.5005\ln k+0.2325$.

If $|V(k)|=o(k\log k)$, Conjectures 4.4 and 3.3 follow.

## 9. Computation

Three programs compute $S(k)$ exactly:

| Program | Method | Cost per $k$ | Arithmetic |
|---|---|---|---|
| `s_dedekind.cpp` (A) | (D) with (BHK) | $O(k\log k)$ | `__int128`, divisibility check |
| `s_hardy.cpp` (B) | (2.1), (4.1), (4.2) | $O(k\log k)$ | `int64_t` with overflow and exactness checks |
| `s_literal.cpp` (C) | the definition, no identities | $O(k^2)$ | `int64_t` |

Methods A and B use different decompositions of $S(k)$ and different evaluations of Dedekind
sums. Both rest on the classical theory of Dedekind sums, whose identities `verify.py` checks
against the definitions. Method C uses no identity at all.

Runs on an Apple M5 Max, one thread per job; the logs are in `logs/`. The times are CPU
(user) times from `/usr/bin/time -p`. Some jobs were paused during Lean builds to stay within
two threads, and several `real` values printed by `time` disagree with the start and end
timestamps in the logs, so no wall-clock times are given.

| Run | Range | CPU time |
|---|---|---|
| A | odd primes $3\le k\le10^6$ | 2055 s |
| B | odd primes $3\le k\le10^6$ | 1882 s |
| A, B (committed sources, clang++ -O3) | odd primes $\le2\cdot10^5$ | 78 s, 71 s; identical to the first runs |
| A | odd primes in $(10^6,1.5\cdot10^6]$ and $(1.5\cdot10^6,2\cdot10^6]$ | 2406 s, 3347 s |
| B | the same two ranges | 2211 s, 3055 s |
| C | odd primes $\le30000$ | 446 s |
| C | all $1\le k\le10000$ | 162 s |
| C | $k=10395,17017,19019$ | < 1 s |

Results:

- A and B agree on every odd prime $k\le2\cdot10^6$. C agrees with A on every odd prime
  $k\le30000$.
- For $k\le10^4$, C reproduces the paper's 151 negative values, all at composite $k$, and the
  composite values the paper quotes.
- No odd prime $k\le2\cdot10^6$ violates Conjecture 1.1, 4.1, 4.2 or 4.3.
- The minimum of $S(k)/k$ over primes $k>5$ is $14/11$, at $k=11$.
- The largest prime with $S(k)\le3k$ is $3119$, as in the paper. The largest with
  $S(k)\le4k$ is $58013$, and the largest with $S(k)\le5k$ is $869399$. $S(k)\le6k$ still
  occurs at $k=1999619$, near the end of the range.
- The paper's lists of the 17 primes below $10^4$ with $S(k)<2k$ and of the 87 with
  $S(k)\le3k$ are reproduced exactly.

The paper (v3, Section 3) says that for primes $k\le50000$ there are 8 pairs violating
$S(k)>4k$. In the table, those 8 are exactly the primes in $(30000,50000]$ with
$S(k)\le4k$. There are 79 such primes in $(10^4,5\cdot10^4]$ and 508 odd primes up to
$5\cdot10^4$. The paper's sentence presumably refers to the range above 30000.

Data files (one `k S(k)` pair per line):

- `data/S_odd_primes.txt`: every odd prime $k\le2\cdot10^6$, from methods A and B.
- `data/S_all_k_le_10000.txt`: every $1\le k\le10000$, from method C.

`verify.py` (CI mode, about 15 s; it needs `g++` and Python 3 with `mpmath`, which comes with
`sympy`, as in CI) does three things:

1. It checks every identity of Sections 2–8 on small ranges, and each claim in the proof of
   Theorem 7.1 for every prime $k\le400$. The checks are exact, except for Proposition 8.1
   and the links of Section 7 that involve logarithms, which are checked in floating point.
2. It compiles the three programs and compares A and B with the table for every odd prime
   $\le50000$, and C for every prime $\le2500$, every $k\le1500$ and the paper's composite
   values.
3. It audits both tables in full.

`verify.py --full` reruns everything over the whole table, which takes several hours.

## 10. References

- [BBMXZ] B. C. Berndt, R. N. Bhat, J. L. Meyer, L. Xie, A. Zaharescu, *An arithmetic sum
  associated with the classical theta function*, arXiv:2501.03234 (v1–v3); Results Math. 81,
  no. 1, doi:10.1007/s00025-025-02584-2 (not checked; numbering here follows arXiv).
- [Ba77] P. Barkan, Sur les sommes de Dedekind et les fractions continues finies, C. R. Acad.
  Sci. Paris Sér. A 284 (1977), 923–926.
- [Be78] B. C. Berndt, Analytic Eisenstein series, theta-functions, and series relations in the
  spirit of Ramanujan, J. Reine Angew. Math. 304 (1978), 332–365.
- [BD82] B. C. Berndt, U. Dieter, Sums involving the greatest integer function and
  Riemann–Stieltjes integration, J. Reine Angew. Math. 337 (1982), 208–220.
- [BG84] B. C. Berndt, L. A. Goldberg, Analytic properties of arithmetic sums arising in the
  theory of the classical theta-functions, SIAM J. Math. Anal. 15 (1984), 143–150.
- [Da20] M. C. Dağlı, New relations concerning a mean value of some Hardy sums and Ramanujan
  sum, Süleyman Demirel Univ. J. Sci. (Fac. Arts Sci.) 15 (2020), 148–157,
  doi:10.29233/sdufeffd.702928.
- [Go81] L. A. Goldberg, *Transformations of theta-functions and analogues of Dedekind sums*,
  Ph.D. thesis, University of Illinois at Urbana-Champaign, 1981.
- [Hi77] D. Hickerson, Continued fractions and density results for Dedekind sums, J. Reine
  Angew. Math. 290 (1977), 113–116.
- [Kn77] D. E. Knuth, Notes on generalized Dedekind sums, Acta Arith. 33 (1977), 297–325.
- [Me97] J. L. Meyer, Properties of certain integer-valued analogues of Dedekind sums, Acta
  Arith. 82 (1997), 229–242.
- [RG72] H. Rademacher, E. Grosswald, *Dedekind Sums*, Carus Math. Monographs 16, MAA, 1972.
- [Si87] R. Sitaramachandrarao, Dedekind and Hardy sums, Acta Arith. 48 (1987), 325–340.
- [Wa82] H. Walum, An exact formula for an average of $L$-series, Illinois J. Math. 26 (1982),
  1–3.
- [YK75] A. C. Yao, D. E. Knuth, Analysis of the subtractive algorithm for greatest common
  divisors, Proc. Nat. Acad. Sci. USA 72 (1975), 4720–4722.
- [Zh03] W. Zhang, On a hybrid mean value of certain Hardy sums and Ramanujan sum, Osaka J.
  Math. 40 (2003), 365–373.
