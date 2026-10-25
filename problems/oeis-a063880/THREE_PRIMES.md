**English** | [한국어](THREE_PRIMES.ko.md)

# A063880: powerful cores with three primes

## Result

**Theorem.** Let \(p,q,r\) be distinct primes and \(a,b,c\ge2\). Then
\(n=p^aq^br^c\) does not satisfy \(\sigma(n)=2\sigma^*(n)\).

With the two-prime theorem of [PROOF.md](PROOF.md) and its reduction to
the powerful core \(C(n)\), this gives: **every solution with
\(\omega(C(n))\le3\) has \(C(n)=108\)**, i.e. \(n=108s\) with \(s\)
squarefree and coprime to \(108\). In this subfamily every term is
\(108\pmod{216}\) and \(108\) is the only primitive term. Everything
here is kernel-checked in Lean (section 9). Cores with four or more
distinct primes are not treated, so the OEIS conjecture stays open.

## 1. Notation and the case split

For a prime \(p\) and an exponent \(e\ge2\) write

\[
u_p=1+p^e,\qquad t_p=p+p^2+\dots+p^{e-1},\qquad
\sigma_p=\sigma(p^e)=u_p+t_p .
\]

Then \((p-1)t_p=p^e-p\), so \(u_p=(p+1)+(p-1)t_p\) and
\(\sigma_p=(p+1)+p\,t_p\). Since \(\sigma\) and \(\sigma^*\) are
multiplicative with \(\sigma^*(p^e)=1+p^e\), the equation for
\(n=p^aq^br^c\) is

\[
R(p,a)\,R(q,b)\,R(r,c)=2,\qquad R(p,e):=\frac{\sigma(p^e)}{1+p^e}.
\]

We use three elementary facts about the local ratio:

- (R1) \(R(p,e)\) is increasing in \(e\);
- (R2) \(R(p,e)<p/(p-1)\), so \(m\,\sigma(p^e)<(m+1)(1+p^e)\) whenever
  \(m+1\le p\);
- (R3) \(\sigma(p^e)>1+p^e\) for \(e\ge2\), and \(\sigma(p^e)\equiv1\pmod p\).

Sort the primes as \(p<q<r\). There are three cases:

- **Case B**: \(p\ge3\) (no factor \(2\)), section 2;
- **Case \(\{2,3,r\}\)**: \(p=2\), \(q=3\), \(r\ge5\), section 3;
- **Case A**: \(p=2\), \(5\le q<r\), sections 4–7.

## 2. Case B: three odd primes

By (R2):

1. \(p\ge5\): each ratio is \(<5/4\), and \(125/64<2\).
2. \(p=3\), \(q\ge7\): then \(r\ge11\), and
   \(\tfrac32\cdot\tfrac76\cdot\tfrac{11}{10}=\tfrac{231}{120}<2\).
3. \(p=3\), \(q=5\), \(r\ge17\):
   \(\tfrac32\cdot\tfrac54\cdot\tfrac{17}{16}=\tfrac{255}{128}<2\).
4. \(p=3\), \(q=5\), \(r\in\{7,11,13\}\): three finite boxes (section 7).

## 3. Case \(\{2,3,r\}\)

Here \(R(2,2)=7/5\), \(R(2,3)=15/9\), \(R(3,2)=13/10\),
\(R(3,3)=40/28\) and \(R(3,4)=121/82\). By (R1) and (R3):

- \(a\ge3\): the product is \(>\tfrac{15}{9}\cdot\tfrac{13}{10}=\tfrac{13}{6}>2\).
- \(a=2\), \(b\ge4\): the product is \(>\tfrac75\cdot\tfrac{121}{82}=\tfrac{847}{410}>2\).
- \(a=2\), \(b=3\): \(\tfrac75\cdot\tfrac{40}{28}=2\), so \(R(r,c)=1\),
  which contradicts (R3).
- \(a=2\), \(b=2\): \(91\,\sigma(r^c)=100\,(1+r^c)\). Modulo \(r\) both
  \(\sigma(r^c)\) and \(1+r^c\) are \(1\), so \(r\mid9\). This is
  impossible for \(r\ge5\).

## 4. Case A: the integer equation and the window for \(q\)

Let \(n=2^aq^br^c\) with \(a,b,c\ge2\) and primes \(5\le q<r\), so
\(r\ge q+2\). Put \(K=\sigma(2^a)=2^{a+1}-1\). It is odd and \(K\ge7\),
and \(2(1+2^a)=K+3\). The equation is

\[
K\,\sigma_q\sigma_r=(K+3)\,u_qu_r. \tag{A}
\]

For \(p\in\{q,r\}\) put \(\delta_p=3p-3-K\) (an odd integer) and
\(W_p=3u_p-Kt_p=3(p+1)+\delta_pt_p\).

**4.1.** (A) is equivalent to

\[
W_qW_r=K(K+3)\,t_qt_r. \tag{A'}
\]

To see this, substitute \(\sigma=u+t\). Then (A) reads
\(3u_qu_r=K(t_qu_r+u_qt_r+t_qt_r)\). Now expand
\((3u_q-Kt_q)(3u_r-Kt_r)\).

**4.2. Positivity.** \(W_q>0\) and \(W_r>0\). By (A') they have the same
sign. If both were negative, then \(Kt_qu_r>3u_qu_r\), which
contradicts the form of (A) in 4.1.

**4.3. The window for \(q\).**

- (a) \(K\le3q\).
- (b) If \(b\ge3\), then \(\delta_q\ge1\), i.e. \(K\le3q-4\), and
  hence \(K(K+3)<9q^2\).
- (c) \(3q\le2K+4\).

For (a): if \(\delta_q<0\), then \(t_q\ge q\) gives
\(0<W_q\le3+3q^2-Kq\), so \(K\le3q\). For (b): \(t_q\ge q(q+1)\) gives
\(0<W_q\le(q+1)(3+\delta_qq)\), so \(\delta_q>-3/q\). Hence
\(\delta_q\ge0\), and \(\delta_q\ge1\) because \(\delta_q\) is odd. For
(c): if \(\delta_q\le0\), then \(3q\le K+3\). Otherwise
\(\delta_r\ge\delta_q+6>0\), and \(W_p>\delta_pt_p\) in (A') gives
\(\delta_q(\delta_q+6)\le\delta_q\delta_r<K(K+3)\). So \(\delta_q<K\),
i.e. \(3q<2K+3\).

So \(K/3\le q\le(2K+4)/3\): for each \(a\), only finitely many \(q\)
are possible.

**4.4. Search reduction** (used only by the scripts of section 8). From
(A) and \(\sigma_r=u_r+t_r\) we get \(u_rW_q=K\sigma_qt_r\), so

\[
\mu_r:=\frac{u_r}{t_r}=\frac{K\sigma_q}{W_q}.
\]

Because \(u_r/t_r=r-1+(r+1)/t_r\), this value equals \(r+1/r\) for
\(c=2\). For \(c\ge3\) it lies in \((r-1,\,r-1+1/r]\) and decreases in
\(c\). The intervals \((r-1,\,r+1/r]\) for different odd primes \(r\)
are disjoint, so \((a,q,b)\) determines at most one candidate
\((r,c)\). Moreover,
\(\mu_r=K\bigl((q+1)+qt_q\bigr)/\bigl(3(q+1)+\delta_qt_q\bigr)\)
increases strictly with \(t_q\) (the cross term is
\((q+1)(K+3)>0\)). Note that \(\delta_q\ne0\) because \(\delta_q\) is
odd.

- If \(\delta_q<0\), only the finitely many \(b\) with \(W_q>0\) matter.
- If \(\delta_q>0\), \(\mu_r\) increases to \(\mu_\infty=Kq/\delta_q\).
  Once it exceeds the largest value \(u_r/t_r\) below \(\mu_\infty\),
  no larger \(b\) can give a solution.

## 5. Case A: 2-adic constraints

Let \(p\) be an odd prime.

- If \(e\) is even, \(\sigma(p^e)\) is odd and \(1+p^e\equiv2\pmod8\).
- If \(e=2m+1\), then \(\sigma(p^e)=(1+p)(1+p^2+\dots+p^{2m})\), and
  \(1+p^e=(1+p)(1-p+\dots+p^{2m})\) whose second factor is odd. For
  \(y\equiv1\pmod4\), \(v_2(1+y+\dots+y^{m})=v_2(m+1)\): halve the
  number of terms and induct.

Define \(\varepsilon(e):=v_2\sigma(p^e)-v_2(1+p^e)\). Then
\(\varepsilon(e)=-1\) for even \(e\) and \(\varepsilon(2m+1)=v_2(m+1)\);
neither value depends on \(p\). Since \(K\) and \(1+2^a\) are odd, the
original equation \(\sigma(2^a)\sigma_q\sigma_r=2(1+2^a)u_qu_r\) gives
\(\varepsilon(b)+\varepsilon(c)=1\). Hence:

- if \(c\) is even, then \(\varepsilon(b)=2\), so \(b\equiv7\pmod{16}\),
  in particular \(b\ge7\);
- if \(c=3\) (\(\varepsilon=1\)), then \(b\equiv1\pmod4\), so \(b=5\) or
  \(b\ge9\);
- if \(c=5\) (\(\varepsilon=0\)), then \(b\equiv3\pmod8\), so \(b=3\) or
  \(b\ge11\).

## 6. Case A: size bounds and the split on \(c\)

Put
\(\Omega=K(K+3)-\delta_q\delta_r\),
\(H=K(K+3)t_r-\delta_qW_r\) and \(G=K(K+3)t_q-\delta_rW_q\). From (A')
and \(W_p=3(p+1)+\delta_pt_p\):

\[
\Omega\,t_qt_r=3(q+1)W_r+3(r+1)\delta_qt_q=3(r+1)W_q+3(q+1)\delta_rt_r,
\tag{I}
\]

\[
Ht_q=3(q+1)W_r,\quad Gt_r=3(r+1)W_q,\quad HG=9(q+1)(r+1)K(K+3),\quad
\Omega t_r=H+3(r+1)\delta_q. \tag{II}
\]

These have three consequences:

- \(\Omega\) is odd, because \(K(K+3)\) is even and
  \(\delta_q\delta_r\) is odd. Also \(\Omega\ge1\): by (I) when
  \(\delta_q\ge0\) or \(\delta_r\ge0\); and if both are negative, then
  \(0<-\delta_p<K\), so \(\delta_q\delta_r<K^2\).
- \(H\) and \(G\) are positive integers (by (II) and 4.2). Hence
  \(t_q\le3(q+1)W_r\), and
  \(t_r\le\Omega t_r\le HG+3(r+1)\delta_q\), that is,
  \[
  t_r\le9(q+1)(r+1)K(K+3)+3(r+1)\delta_q. \tag{M}
  \]
- Since \(W_q>\delta_qt_q\), (A') gives
  \(\delta_qW_r<K(K+3)\,t_r\). \(\quad\)(D)

Now split on \(c\), using section 5 for \(b\).

**\(c\ge7\).** Here \(t_r\ge r^6\). In (M) use \(q+1\le r-1\),
\(K\le3q\le3r-6\) and \(\delta_q<3r\). This gives
\(r^6<81r^4+9r(r+1)\), so \(r\le9\). Then \(r=7\), \(q=5\), and
\(K\le15\), so \(a\in\{2,3\}\). These cases are boxes (section 7).

**\(c\in\{4,6\}\).** Here \(b\ge7\), so \(t_q\ge q^6\ge\frac{2700}{26}(q+1)q^2\).
By (I) and \(\Omega\ge1\),
\(t_qt_r\le3(q+1)W_r+3(r+1)\delta_qt_q\). By (D) and 4.3(b),
\(W_r\le\delta_qW_r<9q^2t_r\), so
\(3(q+1)W_r<27(q+1)q^2t_r\le0.26\,t_qt_r\). Hence

\[
74\,t_r<300(r+1)\delta_q<900\,r(r+1). \tag{C}
\]

With \(t_r\ge r+r^2+r^3\) this gives \(r\le12\), so \(r\in\{7,11\}\).
The window \(K+4\le3q\le2K+4\) then leaves
\((a,q,r)\in\{(2,5,7),(2,5,11),(3,7,11)\}\). These are boxes.

**\(c=5\).** If \(b\ge11\), then (C) with \(t_r\ge r^4\) is
impossible. If \(b=3\), then \(t_q=q(q+1)\), and the second form of (I)
becomes \((q+1)t_r\,M=3(r+1)W_q\) with \(M=q\Omega-3\delta_r\). Here
\(M\) is even and positive, and \(W_q=(q+1)(3+\delta_qq)\). So
\(2t_r\le3(r+1)(3+\delta_qq)<9r^2(r+1)\), which contradicts
\(t_r=r+r^2+r^3+r^4\).

**\(c=2\).** Here \(b\ge7\) and \(t_r=r\). The first form of (I) gives
\(J\,t_qr=3(q+1)W_r+3\delta_qt_q\) with \(J=\Omega-3\delta_q\) even and
positive. So \(2t_qr\le3(q+1)W_r+3\delta_qt_q\). As in the case
\(c\in\{4,6\}\), \(3(q+1)W_r<0.26\,t_qr\), so
\(r<\frac{50}{29}\delta_q\). Combining \(t_q\le3(q+1)W_r\) with (D) gives
\(\delta_qt_q<3(q+1)K(K+3)\,r<\frac{150}{29}(q+1)K(K+3)\,\delta_q\).
Hence \(t_q<47(q+1)q^2\), which contradicts \(t_q\ge q^6\).

**\(c=3\).** Here \(t_r=r(r+1)\) and \(W_r=(r+1)(3+r\delta_r)\). The
first form of (I) becomes \(L\,t_q=3(q+1)(3+r\delta_r)\) with
\(L=r\Omega-3\delta_q\) even and positive, so

\[
2t_q\le3(q+1)(3+r\delta_r). \tag{L}
\]

- \(b\ge9\). Since \(\Omega\ge1\) and \(\delta_q\ge1\),
  \(\delta_r<K(K+3)<9q^2\). Also
  \(3r=\delta_r+3+K<(K+2)^2\le(3q-2)^2\), so \(r<3q^2\). Then (L) gives
  \(2t_q<3(q+1)(3+27q^4)\), which contradicts \(t_q\ge q^8\).
- \(b=5\). Here \(t_q=(q+1)P\) with \(P=q^3+q\), and
  \(W_q=(q+1)(3+\delta_qP)\). So (A') reduces to the quadratic

  \[
  (3+\delta_qP)(3+r\delta_r)=K(K+3)\,P\,r. \tag{Q}
  \]

  Write \(A=3+\delta_qP\), \(E=3+r\delta_r\) and \(M=K(K+3)\). Then
  (L) reads \(LP=3E\), so \(2P\le3E\). Also \(\Omega\ge1\) in (I)
  gives \(Pr\le3E+3\delta_qP\). Multiply both by \(A\) and use
  \(AE=MPr\): this gives \(2A\le3Mr\) and \(rA\le3Mr+3\delta_qA\).

  Suppose \(2P\ge15M\). Then \(A-3M>0\). Combining
  \(r(A-3M)\le3\delta_qA\) with \(2A\le3Mr\) gives
  \(2(A-3M)\le9M\delta_q\). Hence
  \(2\delta_qP<9M\delta_q+6M\le15M\delta_q\), i.e. \(2P<15M\), a
  contradiction. Therefore

  \[
  2(q^3+q)<15\,K(K+3).
  \]

  With \(K\le3q-4\) this forces \(q\le67\), and then \(a\le6\).
  Together with the window, 16 pairs \((a,q)\) with odd \(q\) remain
  (section 7).

## 7. Finite checks

**Boxes.** In each box the three primes are fixed and the exponents
run over intervals, some of them unbounded. Using (R1) and the limits
\(p/(p-1)\), the exponent ranges are split until, in every piece, the
lower bounds already give a product \(>2\) or the upper bounds give a
product \(<2\). There are eight boxes:

| Primes | Exponents | Origin |
|---|---|---|
| \(3,5,7\) | \(a,b,c\ge2\) | Case B |
| \(3,5,11\) | \(a,b,c\ge2\) | Case B |
| \(3,5,13\) | \(a,b,c\ge2\) | Case B |
| \(2,5,7\) | \(a=2\), \(b\ge2\), \(c\ge7\) | Case A, \(c\ge7\) |
| \(2,5,7\) | \(a=3\), \(b,c\ge2\) | Case A, \(c\ge7\) |
| \(2,5,7\) | \(a=2\), \(b\ge7\), \(c\ge4\) | Case A, \(c\in\{4,6\}\) |
| \(2,5,11\) | \(a=2\), \(b,c\ge2\) | Case A, \(c\in\{4,6\}\) |
| \(2,7,11\) | \(a=3\), \(b,c\ge2\) | Case A, \(c\in\{4,6\}\) |

**The quadratic (Q).** For fixed \((a,q)\), (Q) reads
\(3Ar^2-Br+3A=0\) with \(B=A(K+3)+MP\). Its roots have product \(1\),
so a root \(r>1\) satisfies \(r=B/(3A)-1/r\). If \(3A\nmid B\), the
only possible integer root is \(r_0=\lfloor B/(3A)\rfloor\). The 16
pairs allowed by \(K+4\le3q\le2K+4\) and \(2(q^3+q)<15K(K+3)\) (\(q\)
odd, prime or not) are listed below. In all of them \(3A\nmid B\), and
\(r_0\) is not a root of (Q) (for \(q=11\), also \(r_0<q+2\)):

| \(a\) | \(K\) | \(q\) values | \(r_0\) |
|---|---|---|---|
| 2 | 7 | 5 | 7 |
| 3 | 15 | 7, 9, 11 | 35, 15, 11 |
| 4 | 31 | 13, 15, 17, 19 | 81, 43, 31, 26 |
| 5 | 63 | 23, 25, 27, 29, 31 | 483, 175, 114, 87, 73 |
| 6 | 127 | 45, 47, 49 | 1143, 543, 367 |

## 8. Computational cross-check

Two independent exact searches, both standard-library Python, cover
Case A for every \(a\) from \(2\) to `AMAX` and all \(q,b,r,c\). They
rely on the reduction of 4.4, and the first also on the window of 4.3.
They do not use sections 5–7. Both recover planted solutions of
synthetic equations before searching.

- [`three_prime_search.py`](three_prime_search.py) uses exact
  `fractions.Fraction` arithmetic. It also re-checks Case B and Case
  \(\{2,3,r\}\) with nested monotone bounds.
- [`three_prime_search_int.py`](three_prime_search_int.py) uses
  integers only, reads off \(r\) differently, and scans the wider window
  \(\max(3,\lfloor K/3\rfloor-6)\le q\le K+6\).

Neither finds a solution for \(2\le a\le28\). The searches are a
consistency check of the Lean-proved statement in that range, not
part of the proof. Measured wall-clock times on the development
machine:

| Command (in this folder) | Time |
|---|---|
| `python3 three_prime_search.py --amax 22` | 4.0 s |
| `python3 three_prime_search_int.py --amax 22` | 8.3 s |
| `python3 three_prime_search.py --amax 28` | 5 min 06 s (machine under load) |
| `python3 three_prime_search_int.py --amax 28` | 16 min 08 s (machine under load) |

## 9. Lean formalization

All of the above is in
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean),
section *Three-prime cores*. The main declarations:

| Declaration | Content |
|---|---|
| `not_a_three_prime_pow` | the theorem above, for the upstream predicate `A` |
| `three_prime_sorted`, `caseB`, `case23`, `caseA` | the case split (section 1) and the three cases |
| `two_adic_rel`, `caseA_two_adic` | section 5 |
| `caseA_pos`, `caseA_K_le`, `caseA_K_le'`, `caseA_range` | 4.2, 4.3 |
| `caseA_Om`, `caseA_H`, `caseA_dWr`, `caseA_KK` | section 6: (I), \(\Omega\ge1\) odd, \(t_q\le3(q+1)W_r\), (D), \(K(K+3)<9q^2\) |
| `caseA_c7`, `caseA_c46`, `caseA_c2`, `caseA_c5b`, `caseA_c3a`, `caseA_c3b` | the cases \(c\ge7\), (C), \(c=2\), \(c=5\), \(c=3\) |
| `quad_root`, `caseA_c3b_finite` | the table of section 7 |
| `box_3_5_7`, `box_3_5_11`, `box_3_5_13`, `box_2_5_7_c7`, `box_2_5_7_a3`, `box_2_5_7_b7`, `box_2_5_11`, `box_2_7_11` | the eight boxes |
| `eq_108_of_powerful_of_card_le_three` | a powerful solution with at most three prime factors is \(108\) |
| `exists_eq_108_mul_of_card_le_three` | `A n` and at most three primes \(p\) with \(p^2\mid n\) ⇒ `n = 108 * s`, `s` squarefree and coprime to \(108\) |
| `mod_216_of_card_le_three`, `eq_108_of_isPrimitiveTerm_of_card_le_three` | the two corollaries for \(\omega(C(n))\le3\) |

Presentational differences from the text: in Lean, \(t_p\) is
\(\sigma(p^e)-1-p^e\), characterized by \((p-1)t_p=p^e-p\) (`t_key`),
and Case A is argued over \(\mathbb Z\); the boxes and the table are
checked with `norm_num`, `interval_cases` and `omega` (no `decide` or
`native_decide`); and the squarefree-part induction of
`exists_eq_108_mul_of_card_le_two` is restated for an arbitrary bound
\(k\) (`exists_eq_108_mul_of_card_le`), leaving the existing theorem
unchanged.

## 10. What is not claimed

- Cores with four or more distinct primes are not treated. Both
  conjectures of the OEIS entry (unique primitive term, all terms
  \(108\pmod{216}\)) remain open.
- The OEIS search for primitive terms up to \(10^{18}\) was not rerun.
- We do not assert novelty.
