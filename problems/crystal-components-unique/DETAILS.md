**English** | [한국어](DETAILS.ko.md)

# Uniqueness of crystal components: mathematical details

This file gives the arguments behind [README.md](README.md). Each step names the Lean declaration
in [`AgenticConjectures/CrystalComponentsUnique.lean`](../../AgenticConjectures/CrystalComponentsUnique.lean)
that proves it. Section 8 is computer-assisted: Lean checks the reduction and the final case
analysis, but the list of integral points of an elliptic curve is computed in Sage/PARI and enters
as a hypothesis. Section 10 contains remarks that are neither formalized nor part of the claim.

Throughout, a **crystal** (`IsCrystalWithComponents n a b`) means: n is odd, a, b > 1, n = ab, and
2(a + 1)(b + 1) divides (a + b)² + (ab + 1)². We write

D = (a + 1)(b + 1),  s = a + b,  u = (a + 1)/2,  v = (b + 1)/2.

## 1. Divisibility (Proposition 1 of the paper)

Since n + 1 = ab + 1 = D − s and D − 2s = (a − 1)(b − 1),

(n + 1)² = s² + D(D − 2s) = s² + D(a − 1)(b − 1).  (1.1)

Hence s² + (n + 1)² = 2s² + D(a − 1)(b − 1). If a is odd, then (a − 1)(b − 1) = 2 · ((a − 1)/2)(b − 1),
so s² + (n + 1)² = 2(s² + D · ((a − 1)/2)(b − 1)), and 2D divides it iff D ∣ s²
(`dvd_biharmonic_iff`, hypothesis: a odd). By (1.1), (n + 1)² ≡ s² (mod D), so D ∣ s² iff
D ∣ (n + 1)² (`dvd_sq_add_iff_dvd_mul_add_one_sq`, no hypothesis).

For a crystal, a and b are odd because n = ab is odd (`IsCrystalWithComponents.odd_left`,
`.odd_right`). This gives `isCrystal_iff_dvd_sq_add` and `isCrystal_iff_dvd_succ_sq`. In the
paper's notation these are the equivalences B ∈ ℕ ⟺ Q ∈ ℕ ⟺ F ∈ ℕ of Proposition 1, where
Q = s²/D and F = (n + 1)²/D. The open Formal Conjectures PR #7051 proves the same equivalences, and
also the one for the paper's fourth quantity P = s(n + 1)/D. It leaves the recurrence
characterization of Section 3 of the paper as a TODO.

## 2. The (u, v) form and the invariant k

For a crystal, a, b ≥ 3, so u, v ≥ 2. Since a + 1 = 2u and b + 1 = 2v, D = 4uv and s = 2(u + v − 1).
So D ∣ s² iff uv ∣ (u + v − 1)² (`isCrystal_iff_uv_dvd`).

**Splitting.** uv ∣ (u + v − 1)² ⟺ u ∣ (v − 1)² and v ∣ (u − 1)² (proved over ℤ in the private
lemma `int_uv`; `isCrystal_iff_uv`).

- (⇒) (u + v − 1)² ≡ (v − 1)² (mod u) and (u + v − 1)² ≡ (u − 1)² (mod v).
- (⇐) Let g = gcd(u, v). Then g ∣ (v − 1)² = v(v − 2) + 1 and g ∣ v, so g = 1. Coprime u and v
  both divide (u + v − 1)², hence so does uv.

In particular gcd(a + 1, b + 1) = 2 for every crystal.

**The invariant.** Put k = s²/D = (u + v − 1)²/(uv), the paper's Q(a, b). Lean defines
`crystalK a b` with truncating ℕ division; for a crystal the division is exact
(`IsCrystalWithComponents.sq_add_eq`). Since D = n + 1 + s,

s² = k(n + 1 + s)  (`IsCrystalWithComponents.sq_add_eq_mul`).  (2.1)

**k ≥ 3** (`IsCrystalWithComponents.three_le_crystalK`): (u + v − 1)² − 2uv = (u − 1)² + (v − 1)² − 1 ≥ 1
for u, v ≥ 2, so kuv > 2uv.

## 3. The reduction: n and k determine the crystal

Fix n and k ≥ 1. By (2.1), s is a positive root of z² − kz − k(n + 1). The product of the two roots is
−k(n + 1) < 0, so exactly one root is positive, and s is determined. Then a and b are the two roots
of z² − sz + n. Hence two crystal factorizations of the same n with the same k are equal as
unordered pairs (`eq_of_crystalK_eq`).

Consequently the conjecture is equivalent to: *any two crystal factorizations of the same n have
the same k* (`statement_iff_crystalK_eq`). The other direction holds because equal unordered pairs
have equal k (`crystalK_comm`).

## 4. Vieta descent (Theorem 4 of the paper)

For an integer w, let u₀ = 0, u₁ = 1, u_{m+2} = (w − 2)u_{m+1} − u_m + 2 (`seqU w`). Write
Q_w(x, y) = (x + y − 1)² − wxy. For fixed y,

Q_w(x, y) = x² − ((w − 2)y + 2)x + (y − 1)²,

a monic quadratic in x. If x is a root, the other root is x′ = (w − 2)y + 2 − x, and xx′ = (y − 1)².

**Invariant** (`seqU_invariant`): Q_w(u_{m+1}, u_m) = 0 for all m. Base: Q_w(1, 0) = 0. Step: if
Q_w(u_{m+1}, u_m) = 0, then u_m is a root of Q_w(·, u_{m+1}), and so is its partner
(w − 2)u_{m+1} + 2 − u_m = u_{m+2}.

**Theorem 4** (`sq_eq_mul_iff_seqU`): for any integer w and positive integers x, y,
Q_w(x, y) = 0 iff (x, y) = (u_{m+2}, u_{m+1}) or (x, y) = (u_{m+1}, u_{m+2}) for some m ≥ 0.

- (⇐) The invariant and the symmetry of Q_w.
- (⇒) Strong induction on x + y (private lemma `seqU_descent`). By symmetry assume x ≥ y.
  - If y = 1, then x² = wx, so x = w and (x, y) = (u₂, u₁).
  - If y ≥ 2, then the partner x′ = (w − 2)y + 2 − x = (y − 1)²/x of x is an integer with
    0 < x′ < y²/x ≤ y. So (x′, y) is a positive solution with a smaller sum, and by induction it is
    a consecutive pair. If (y, x′) = (u_{m+2}, u_{m+1}), then x = (w − 2)y + 2 − x′ = u_{m+3}. If
    (y, x′) = (u_{m+1}, u_{m+2}), then x = (w − 2)u_{m+1} + 2 − u_{m+2} = u_m; here m ≥ 1 because
    x > 0 = u₀, so (x, y) = (u_m, u_{m+1}) is again consecutive.

The paper states Theorem 4 as (x, y) = (u_n(w), u_{n−1}(w)) with n ≥ 1, citing its reference [1]
(Abrate, Barbero, Cerruti and Murru, *Polynomial sequences on quadratic curves*, Integers, 2015).
That form fixes the order of the pair, and its index range includes the non-positive pair
(u₁, u₀) = (1, 0). The Lean statement allows both orders and starts at the pair (u₁, u₂) = (1, w).

## 5. The classification (Theorem 5 of the paper)

For a crystal with k = `crystalK a b`, (u, v) is a positive solution of Q_k = 0 (Section 2), so
{u, v} = {u_{m+1}, u_{m+2}} for the sequence `seqU k` (`IsCrystalWithComponents.exists_seqU`).
Conversely, if 2 ≤ u_{m+1}, 2 ≤ u_{m+2} for some integer w and {a + 1, b + 1} = {2u_{m+1}, 2u_{m+2}},
then a and b are odd and at least 3, and uv divides (u + v − 1)² = wuv, so n = ab is a crystal
(`isCrystal_iff_seqU`).

**Chains.** For k ≥ 3 put w_j = u_{j+1}: w₀ = 1, w₁ = k, w₂ = (k − 1)², w₃ = k(k − 2)², and
w_{j+1} = (k − 2)w_j − w_{j−1} + 2. The **j-th crystal of k** (j ≥ 1) is
{a, b} = {2w_j − 1, 2w_{j+1} − 1}, and n_j(k) denotes its product.

- For k ≥ 4 the chain is strictly increasing: w_{j+1} − w_j = (k − 3)w_j − w_{j−1} + 2 ≥ w_j − w_{j−1} + 2,
  so by induction w_{j+1} − w_j ≥ 2. Hence n_j(k) is strictly increasing in j, and different j give
  different crystals.
- For k = 3 the chain is 1, 3, 4, 3, 1, 3, 4, … with period 4. The pairs with both entries at least 2
  are (3, 4) and (4, 3), so k = 3 gives the single crystal {5, 7}
  (`IsCrystalWithComponents.eq_five_seven_of_crystalK_eq_three`).

Since a crystal determines k, it lies on exactly one chain, at exactly one position j (for k ≥ 4).

## 6. Closed form through a Lucas sequence

Let L₀ = 0, L₁ = 1, L_{i+2} = cL_{i+1} − L_i (`lucas c`). The quadratic form x² − cxy + y² is invariant
under (x, y) ↦ (cx − y, x), which gives

L_{i+1}² − cL_iL_{i+1} + L_i² = 1  (`lucas_cassini`),  (6.1)

and for c ≥ 2, 0 ≤ L_i < L_{i+1} (`lucas_nonneg_lt`). With c = k − 2, induction on i using the two
recurrences and (6.1) gives

u_{2i} = kL_i²,  u_{2i+1} = (L_i + L_{i+1})²  (`seqU_lucas`).

For p, r ≥ 0, (p + r)² − kpr = p² − (k − 2)pr + r², so (6.1) says (p + r)² = kpr + 1 for consecutive
terms. The j-th crystal of k is therefore

{a + 1, b + 1} = {2kp², 2(p + r)²}, where (p, r) = (L_i, L_{i+1}) if j = 2i − 1 and (p, r) = (L_{i+1}, L_i) if j = 2i.

`isCrystal_iff_kpr` states the classification in this form: n = ab is a crystal iff
{a + 1, b + 1} = {2kp², 2(p + r)²} for some k and some p, r ≥ 1 with (p + r)² = kpr + 1, and then
k = `crystalK a b` (`crystalK_eq_of_kpr`). Such p, r force k ≥ 3, because for k ≤ 2,
(p + r)² − kpr − 1 ≥ p² + r² − 1 > 0.

**The pronic form.** Put m = p(p + r). Then u + v − 1 = kp² + kpr = km and uv = km², so
s = 2km, D = 4km² and

n + 1 = D − s = 2km(2m − 1).  (6.2)

With q = 2m − 1 this reads n + 1 = kq(q + 1) and a + b = k(q + 1). Conversely these two equations
give D = n + 1 + s = k(q + 1)² and s² = kD, so `isCrystal_iff_pronic` characterizes crystals by them.

## 7. Cases proved in Lean

**7.1 Same k.** Section 3 (`eq_of_crystalK_eq`).

**7.2 k = 3.** The only crystal with k = 3 is {5, 7} (Section 5). The only factorization of 35 with
both factors greater than 1 is 5 · 7 (`IsCrystalWithComponents.eq_five_seven_of_eq_35`). So if one
of two crystals of the same n has k = 3, then n = 35 and both are {5, 7}
(`eq_of_crystalK_eq_three`).

**7.3 The family k = 4** (`IsCrystalWithComponents.crystalK_eq_four_iff`). For c = 2, L_i = i, so
{u, v} = {(2i)², (2i + 1)²} or {(2i + 2)², (2i + 1)²}: the j-th crystal of k = 4 is
{u, v} = {t², (t + 1)²} with t = j + 1 ≥ 2. Then n = f₄(t) = (2t² − 1)(2(t + 1)² − 1), and
f₄(t) + 1 = 4X(X − 1) with X = t(t + 1).

**7.4 The family j = 1.** If a + 1 = 2k, then b + 1 = 2(k − 1)² (`IsCrystalWithComponents.j1`):
with u = k, the equation (k + v − 1)² = k²v forces v to be a square c², and then
c² − kc + (k − 1) = (c − 1)(c − k + 1) = 0, where c = 1 is excluded by v ≥ 2. So the crystal is
{2k − 1, 2(k − 1)² − 1} with

n = f₁(k) = (2k − 1)(2(k − 1)² − 1),  f₁(k) + 1 = 2k(k − 1)(2k − 3).

f₁ is strictly increasing for k ≥ 2, so two such crystals of the same n have the same k and
coincide by 7.1 (`eq_of_j1`). These are the j = 1 crystals: {5, 7} for k = 3, {7, 17} for k = 4
(the t = 2 member of 7.3), and the class F1 below for k ≥ 5.

## 8. k = 4 against j = 1 (computer-assisted; Lean given the integral points)

**Claim.** If t ≥ 2 and K ≥ 3 are integers with f₄(t) = f₁(K), then (t, K) = (2, 4), where
n = 119 = 7 · 17 is the single crystal of 7.3 and 7.4 with k = 4. Hence no crystal of the k = 4
family shares n with a crystal of the j = 1 family of a different k.

**Reduction to an elliptic curve.** By 7.3 and 7.4, f₄(t) = f₁(K) iff 2X(X − 1) = K(K − 1)(2K − 3),
that is,

(2X − 1)² = 4K³ − 10K² + 6K + 1,  X = t(t + 1).

Multiplying by 16 and putting x = 4K, y = 4(2X − 1) gives an integral point of

E: y² = x³ − 10x² + 24x + 16

with 4 ∣ x and y ≡ 4 (mod 8). E has conductor 2432 = 2⁷ · 19 and trivial torsion.
[`ec_k4_j1.py`](ec_k4_j1.py) carries out the following steps and asserts each outcome; its output is
[`logs/ec_k4_j1.log`](logs/ec_k4_j1.log).

1. **Rank.** PARI `ellrank` returns [r, R, s, L] = [2, 2, 0, [(0, 4), (4, 4)]]. The lower and upper
   bounds for the rank agree, so rank E(ℚ) = 2, and P₁ = (0, 4), P₂ = (4, 4) are independent.
2. **Generators.** Let ν be the index of ⟨P₁, P₂⟩ in E(ℚ) ≅ ℤ². Then Reg(P₁, P₂) = ν² Reg(E(ℚ)).
   Let λ be a lower bound for the canonical height ĥ of every point of infinite order. Hermite's
   inequality for the rank-2 lattice (E(ℚ), ĥ) gives λ ≤ γ₂ Reg(E(ℚ))^{1/2} with γ₂² = 4/3, so
   ν ≤ (Reg(P₁, P₂) · 4/3)^{1/2} / λ.
   Sage's `E.height_function().min(0.0001, 5)` (the method of Cremona–Siksek and Thongjunthug,
   which establishes the bound rigorously) gives λ = 0.0953418…, and Reg(P₁, P₂) = 0.2418772…, so
   ν ≤ 5.956, that is ν ≤ 5. PARI `ellsaturation([P₁, P₂], 100)` returns generators of a subgroup
   that contains ⟨P₁, P₂⟩ and whose index in E(ℚ) has no prime factor up to 100. It returns
   [(4, 4), (0, −4)] = [P₂, −P₁], with the same regulator, so ν itself has no prime factor up to 100.
   With ν ≤ 5 this gives ν = 1: P₁ and P₂ generate E(ℚ). The bound λ and the regulators use the same
   normalization; for example ĥ(P₂) = 0.374… ≥ λ.
3. **Integral points.** Sage's `E.integral_points(mw_base=[P₂, −P₁])` (elliptic logarithms, a
   Baker-type bound and lattice reduction) returns, up to sign of y:
   (0, 4), (3, 5), (4, 4), (6, 4), (10, 16), (16, 44), (19, 61), (84, 724), (1200, 41396).
4. **Back to (K, X, t).** The points with 4 ∣ x and y/4 odd give K = x/4 and X = (y/4 + 1)/2:

| Point | K | X | 4X + 1 | t with X = t(t + 1) |
| --- | ---: | ---: | ---: | --- |
| (0, ±4) | 0 | 1, 0 | 5, 1 | none; t = 0 |
| (4, ±4) | 1 | 1, 0 | 5, 1 | none; t = 0 |
| (16, ±44) | 4 | 6, −5 | 25, −19 | t = 2; none |
| (84, ±724) | 21 | 91, −90 | 365, −359 | none |
| (1200, ±41396) | 300 | 5175, −5174 | 20701, −20695 | none |

X = t(t + 1) for an integer t iff 4X + 1 is a perfect square. The only solution with t ≥ 2 and
K ≥ 3 is (t, K) = (2, 4). As a sanity check that is not part of the argument, the script also
searches 0 ≤ K ≤ 10⁶ directly for square values of 4K³ − 10K² + 6K + 1 and finds exactly
K ∈ {0, 1, 4, 21, 300}.

**In Lean.** `eq_of_crystalK_eq_four_of_j1` proves the claim, in the form "a crystal with k = 4
and a j = 1 crystal of the same n coincide", from the hypothesis `EllipticCurveIntegralPoints`:
every integral point of E has x ∈ {0, 3, 4, 6, 10, 16, 19, 84, 1200}, the x-coordinates of step 3.
The reduction to E and step 4 are checked by Lean. For K = 21 and K = 300 the proof factors
(2X − 1)² − 181² and (2X − 1)² − 10349² and bounds t; for K = 4 the two crystals have the same k
and coincide by 7.1. Steps 1–3, which establish the hypothesis, are not checked by Lean.

**Trust.** The hypothesis relies on PARI 2.17.4 (`ellrank`, `ellsaturation`) and Sage (passagemath
10.8.13: the height bound and `integral_points`). None of that is formally verified.

## 9. The searches: algorithms and completeness

**Classes.** Every crystal lies in exactly one class (Section 5):

| Class | Definition | n |
| --- | --- | --- |
| F3 | k = 3 | 35 |
| F4 | k = 4 | f₄(t), t ≥ 2 |
| F1 | k ≥ 5, j = 1 | f₁(k) |
| S | k ≥ 5, j ≥ 2 | n_j(k) |

f₁ (k ≥ 2) and f₄ (t ≥ 1) are strictly increasing, so F1 against F1 and F4 against F4 cannot
collide (also `eq_of_j1` and `eq_of_crystalK_eq`), and F3 against anything is `eq_of_crystalK_eq_three`.
The searches test S against S, F1, F4 and F3, and F4 against F1 and F3. The last is redundant
given Section 8 and serves as a check.

**Size of S.** The j = 2 member of k is {u, v} = {(k − 1)², k(k − 2)²}, so
n₂(k) = (2(k − 1)² − 1)(2k(k − 2)² − 1) ≈ 4k⁵, and in general n_j(k) ≈ 4k^{2j+1}. Hence only
k ≲ (X/4)^{1/5} contribute to S up to X, and S has 33,811,278 members up to 2¹²⁷ − 1, against about
3.5 · 10¹² members of F1.

**Completeness of the enumeration of S.** Both [`crystal_search.c`](crystal_search.c) (A) and
[`crystal_exact.py`](crystal_exact.py) (B) loop over k = 5, 6, … and, for each k, over j = 2, 3, ….

1. For fixed k ≥ 5, n_j(k) is strictly increasing in j (Section 5), so the members up to X are
   j = 2, …, J(k), and stopping at the first member above X loses nothing.
2. n₂(k) is strictly increasing in k, so once n₂(k) > X no larger k has a member of S up to X. Both
   programs stop at the first k with no member of S up to X.
3. A generates the chain from the Lucas pairs (Section 6, with j = 2i − 1 for (L_i, L_{i+1}) and
   j = 2i for (L_{i+1}, L_i)) and checks (p + r)² = kpr + 1 for every member it lists. B generates it
   from the recurrence w_{j+1} = (k − 2)w_j − w_{j−1} + 2, checks (a + b)² = k(a + 1)(b + 1) for every
   member, and checks the original definition for the first two members of each k. Both check that
   n increases along each chain.

**Collision tests.**

- S against S: sort the members of S and compare neighbours.
- S against F1 and F4: for each member n, find the largest K ≥ 3 with f₁(K) ≤ n and test f₁(K) = n
  with K ≥ 5; likewise for f₄ with t ≥ 2. The search starts from an estimate (floating point in A,
  an integer root in B) and steps to the exact answer by comparing exact values of f₁ or f₄, so the
  estimate only affects the number of steps.
- S against F3: n = 35.
- F4 against F1 and F3: every t ≥ 2 with f₄(t) ≤ X (A), or up to the bound `--f4-limit` (B).

The class sizes of F1 and F4 come from inverting f₁ and f₄ at X.

**Overflow.** A uses 128-bit integers, and every product and sum saturates: on overflow it returns
2¹²⁸ − 1. Since X ≤ 2¹²⁷ − 1, a saturated value is larger than X, so it is never listed and never
equals a listed value. The subtraction in 2x − 1 is applied only to even values, which cannot equal
the odd value 2¹²⁸ − 1, so a saturated value stays saturated. B uses Python's exact integers.

**Independence.** A and B share no code. They differ in how they generate the chains (Lucas pairs
against the (u, v) recurrence), how they invert f₁ and f₄ (floating point against integer roots)
and in their arithmetic (saturating 128-bit against exact). Both rely on the Lean classification
for completeness.

**Direct check.** [`direct_check.py`](direct_check.py) does not use the classification. By
`isCrystal_iff_uv`, a crystal with a ≤ b has u ≤ v and v ∣ (u − 1)², and (2u − 1)² ≤ ab ≤ X. For
every such u it lists the divisors v ≥ u of (u − 1)² with (2u − 1)(2v − 1) ≤ X, from the
factorization of u − 1 by a smallest-prime-factor sieve, and tests the original definition. Partial
products above the bound are pruned; this is sound because every partial product of a divisor
below the bound is itself below the bound. It then computes k and the chain index j by the descent
(x, y) ↦ ((x − 1)²/y, x) for x ≤ y, which ends at the pair (1, k). It finds the same 7,266 crystals up
to 10¹² and 32,094 up to 10¹⁴ as A and B, with the same class sizes and the same checksum of S. If
the classification missed a crystal, the direct check would find more crystals than A and B.

**Checksum.** All three programs print the sum of the members of S modulo 2⁶⁴.

## 10. Remarks on the open case (not formalized, not claimed)

What remains open is a crystal of class S sharing its n with a crystal of a different k. The
following remarks explain what a proof would have to overcome.

**10.1 m ≥ k − 1.** In the notation of Section 6, expanding with kpr = (p + r)² − 1 gives

pr(m + 1 − k) = (p² − 1)(pr + r² − 1).

So m ≥ k − 1, with equality iff p = 1, which for k ≥ 4 is the j = 1 crystal. By (6.2), n + 1 = 2km(2m − 1)
increases with k and with m. If a crystal with (k, m) shares n with the j = 1 crystal of k′ ≠ k,
whose m is k′ − 1, then k > k′ would give m ≥ k − 1 ≥ k′ > k′ − 1 and a larger n. So k < k′, and then
m > k′ − 1: the other crystal has the smaller k and the larger m.

**10.2 A parametrization by factorizations of m(m − 1).** Put X = u − m and Y = v − m. Then
X = p(p² + pr − 1)/r ≥ 1, Y = r(p + r) ≥ 1, XY = m(m − 1), X + Y = (k − 2)m + 1, and

n + 1 = 2(2m − 1)(2m − 1 + X + Y).

Conversely, for m ≥ 2 and positive X, Y with XY = m(m − 1) and X + Y ≡ 1 (mod m), the pair
(u, v) = (m + X, m + Y) is a crystal pair with k = 2 + (X + Y − 1)/m: then uv = m(2m − 1 + X + Y) = km²
and u + v − 1 = km. The j = 1 crystals are exactly those with {X, Y} = {1, m(m − 1)}. So crystals
correspond to the factorizations of the pronic number m(m − 1) into two factors whose sum is
1 mod m, and the conjecture says that (2m − 1)(2m − 1 + X + Y) determines m.

**10.3 No local obstruction.** At k = 0 the chain is 1, 0, 1, 0, …, so n_j(0) = −1 for every j. Also
f₁(1) = f₁(0) = −1 and f₄(0) = f₄(−1) = −1. So every equation n_j(k) = n_{j′}(k′) or n_j(k) = f₄(t)
between two families has an integer solution, hence solutions modulo every integer and over ℝ, and
no congruence or sign argument can exclude a collision between two families. For the same reason
n mod M never determines k mod M′ for M′ ≥ 2: the F1 crystals with K ≡ 0 and K ≡ 1 (mod MM′) all have
n ≡ −1 (mod M). A scan of the 144,251 crystals below 10¹⁶ confirmed this for
M ∈ {2, 3, 4, 5, 7, 8, 9, 16, 24, 32, 48, 64, 72, 96, 128, 144} and M′ ∈ {2, 3, 4, 5, 7, 8, 9, 16}.

**10.4 Genus.** The collision equations are curves of genus greater than 1 already for the smallest
pairs of families. The Riemann–Hurwitz formula (computed with sympy) gives:

- F1 against the j = 2 members, k(k − 1)(2k − 3) = k′(k′ − 1)(k′ − 2)(2k′² − 6k′ + 3): genus 4;
- F4 against the j = 2 members, 2X(X − 1) = k′(k′ − 1)(k′ − 2)(2k′² − 6k′ + 3) with X = t(t + 1): genus 6;
- F4 against F1 in the variables (K, t): genus 3. Its quotient by t ↦ −1 − t is the curve E of
  Section 8.

Each such curve has finitely many integral points (Siegel), but S consists of infinitely many
families (one for each j ≥ 2), so a proof needs an argument that is uniform in j.

**10.5 A heuristic.** In a naive random model, an odd n near a member of S lies in F1 with
probability about 2/f₁′(K) ≈ (1/6)(n/4)^{−2/3}, where f₁(K) ≈ n, and in F4 with probability about
2/f₄′(t) ≈ (1/8)(n/4)^{−3/4}. Summed over the members of S, this predicts about 0.006 collisions with
F1 and 0.002 with F4 in total, almost all from the smallest members: the ten smallest, all below
4 · 10⁵, contribute 0.005 and 0.002. Above 2¹²⁷ − 1 it predicts about 2 · 10⁻¹⁹, almost all from
the j = 2 members with k > 3.36 · 10⁷: about Σ_{k>k₀} (1/6)k^{−10/3} ≈ (1/14)k₀^{−7/3}. The model
ignores arithmetic correlations (for instance, every member of F1 is 3 mod 4, while members of S
need not be), so it suggests only that a counterexample, if one exists, is unlikely to be large. It
is not evidence of the kind a proof needs.
