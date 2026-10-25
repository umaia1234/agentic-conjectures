import Mathlib

/-!
# OEIS A063880 — `σ(n) = 2 σ*(n)`: solutions whose powerful core has at most three primes

A063880 lists the `n` with `σ(n) = 2 σ*(n)`, where `σ*` is the sum of unitary
divisors (`d ∣ n` with `gcd(d, n/d) = 1`). The OEIS entry conjectures that every
term is `108 (mod 216)` and that `108` is the only *primitive* term (no proper
divisor is a term); both are open and are recorded here as `Prop`s
(`statement_mod_216`, `statement_unique_primitive`), never proved.

This module formalizes the *partial* theorem of
`problems/oeis-a063880/PROOF.md`: writing `C(n) = ∏_{e_p ≥ 2} p^{e_p}` for the
powerful core of `n`, every solution with `ω(C(n)) ≤ 2` has `C(n) = 108`
(`exists_eq_108_mul_of_card_le_two`); hence, in that subfamily, every term is
`108 (mod 216)` (`mod_216_of_card_le_two`) and `108` is the only primitive term
(`eq_108_of_isPrimitiveTerm_of_card_le_two`). Conversely, `108 s` is a term of
that subfamily for every squarefree `s` coprime to `108` (`a_108_mul`,
`primeFactors_filter_sq_dvd_108_mul`), so the classification is an equivalence.
`problems/oeis-a063880/THREE_PRIMES.md` extends this to `ω(C(n)) ≤ 3`: no powerful
number with exactly three prime factors is a term (`not_a_three_prime_pow`), so every
solution with `ω(C(n)) ≤ 3` has `C(n) = 108` (`exists_eq_108_mul_of_card_le_three`), and
both corollaries hold in that larger subfamily (`mod_216_of_card_le_three`,
`eq_108_of_isPrimitiveTerm_of_card_le_three`). Cores with four or more primes are not
treated.
It also proves the two upstream `textbook` lemmas `powerful_of_isPrimitiveTerm`
and `a_of_primitive_mul_squarefree` (both `sorry`-backed upstream); the upstream
`exists_primitive_of_a` is not formalized here.

## Correspondence with the upstream snapshot

* `unitaryDivisors`, `usigma`, `A`, `IsPrimitiveTerm` are the upstream
  declarations of `problems/oeis-a063880/upstream/63880.lean`
  (`OeisA63880.unitaryDivisors / usigma / A / IsPrimitiveTerm`), copied term for
  term: `A n := 0 < n ∧ σ 1 n = 2 * usigma n` with `σ 1 = ArithmeticFunction.sigma 1`.
* `IsPrimitive` is `Set.IsPrimitive` and `Powerful` is `Nat.Powerful = Nat.Full 2`
  from the upstream companion files (`FormalConjecturesForMathlib/NumberTheory/
  Primitive.lean`, `…/Data/Nat/Full.lean` at the pinned commit), which are not
  in mathlib; `Nat.Full 2 n` is unfolded to `∀ p ∈ n.primeFactors, p ^ 2 ∣ n`.
* All equations are additive in `ℕ`; no truncated subtraction occurs in any
  statement.
* The hypothesis `ω(C(n)) ≤ k` (`k = 2, 3`) is encoded as
  `(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ k` — the primes `p` with
  `p² ∣ n` are exactly the primes of the powerful core — and the conclusion
  `C(n) = 108` as `∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s`
  (equivalent: `C(108 s) = 108` for such `s`, and if `C(n) = 108` then `n / 108`
  is squarefree and coprime to `108`).

## Proof outline (as in `PROOF.md`)

* `usigma_mul`, `usigma_prime_pow`, `usigma_eq_sigma_of_squarefree`: `σ*` is
  multiplicative with `σ*(p^e) = 1 + p^e` (`e ≥ 1`), and agrees with `σ` on squarefree
  numbers. Hence `a_mul_iff`: for `s` squarefree and coprime to `m`,
  `A (m * s) ↔ A m` (reduction (4) of `PROOF.md`).
* `sigma_prime_pow_lt`: `σ(p^e) < 2 (1 + p^e)`, so a prime power is never a
  solution; `sigma_mul_sigma_lt_of_odd`: for distinct odd primes,
  `σ(p^a) σ(q^b) < 2 (1 + p^a)(1 + q^b)` (local ratios `< 3/2 · 5/4 < 2`).
* `eq_of_two_pow_mul_prime_pow`: `σ(2^a) σ(q^b) = 2 (1 + 2^a)(1 + q^b)` with `q`
  odd and `a, b ≥ 2` forces `q ∣ 3`, i.e. `q = 3`; then
  `(2^{a+1} - 7)(3^b - 3) = 24` (equation (9) of `PROOF.md` times 3), whence
  `a = 2, b = 3`.
* `eq_108_of_powerful`: a powerful solution with at most two prime factors is
  `108` (split on `0, 1, 2` prime factors).
* `exists_eq_108_mul_of_card_le_two`: strong induction on `n`; an exponent-1
  prime is peeled off with `a_mul_iff`, and if there is none, `n` is powerful.
  (This replaces `PROOF.md`'s explicit core `C(n)`; the theorem proved is the same.)
* `not_a_three_prime_pow` (`THREE_PRIMES.md`): after sorting `p < q < r`, `caseB` (no
  factor `2`), `case23` (`{2, 3, r}`) and `caseA` (`2 < 5 ≤ q < r`); see the section
  *Three-prime cores* below. With `eq_108_of_powerful_of_card_le_three` and
  `exists_eq_108_mul_of_card_le` (the same induction for any bound `k` under which every
  powerful solution is `108`) this gives `exists_eq_108_mul_of_card_le_three`.
-/

namespace AgenticConjectures.OeisA063880

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- Upstream `OeisA63880.unitaryDivisors`: divisors `d` of `n` with `gcd(d, n/d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- Upstream `OeisA63880.usigma`: the sum of unitary divisors `σ*(n)`. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- Upstream `OeisA63880.A`: membership in A063880, `0 < n ∧ σ(n) = 2 σ*(n)`. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- Upstream `Set.IsPrimitive` (FormalConjecturesForMathlib/NumberTheory/Primitive.lean). -/
def IsPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

/-- Upstream `OeisA63880.IsPrimitiveTerm`. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := IsPrimitive {n | A n} n

/-- Upstream `Nat.Powerful` (`Nat.Full 2`, FormalConjecturesForMathlib/Data/Nat/Full.lean),
unfolded: every prime factor `p` of `n` has `p ^ 2 ∣ n`. -/
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

/-- Open (upstream `mod_216_of_a`): every member of A063880 is `108 (mod 216)`. -/
def statement_mod_216 : Prop := ∀ n, A n → n % 216 = 108

/-- Open (upstream `unique_primitive_108`): `108` is the only primitive term. -/
def statement_unique_primitive : Prop := ∀ n, IsPrimitiveTerm n → n = 108

/-! ### `usigma` basics -/

/-- `σ*(0) = 0` (no divisors). -/
theorem usigma_zero : usigma 0 = 0 := by
  simp [usigma, unitaryDivisors]

/-- `σ*(1) = 1`. -/
theorem usigma_one : usigma 1 = 1 := by
  decide

/-- `1` is a unitary divisor of every `n > 0`. -/
theorem one_mem_unitaryDivisors {n : ℕ} (hn : 0 < n) : 1 ∈ unitaryDivisors n := by
  simp [unitaryDivisors, Nat.mem_divisors, hn.ne']

/-- `σ*(n) > 0` for `n > 0`. -/
theorem usigma_pos {n : ℕ} (hn : 0 < n) : 0 < usigma n := by
  have h1 := one_mem_unitaryDivisors hn
  have h := Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) h1
  simp only [usigma]
  exact lt_of_lt_of_le Nat.one_pos h

/-- The unitary divisors of a prime power `p^e` are exactly `1` and `p^e`. -/
theorem unitaryDivisors_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    unitaryDivisors (p ^ e) = {1, p ^ e} := by
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hcop⟩
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [Nat.pow_div hk hp.pos] at hcop
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · left; simp
    · rcases Nat.lt_or_ge k e with hke | hke
      · exfalso
        rw [Nat.coprime_pow_left_iff hk0, Nat.coprime_pow_right_iff (by omega)] at hcop
        exact hp.one_lt.ne' ((Nat.coprime_self p).1 hcop)
      · right
        have : k = e := le_antisymm hk hke
        rw [this]
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.ne_zero⟩, Nat.coprime_one_left _⟩
    · refine ⟨⟨dvd_rfl, pow_ne_zero _ hp.ne_zero⟩, ?_⟩
      rw [Nat.div_self (pow_pos hp.pos e)]
      exact Nat.coprime_one_right _

/-- `σ*(p^e) = 1 + p^e` for a prime `p` and `e ≥ 1`. -/
theorem usigma_prime_pow {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    usigma (p ^ e) = 1 + p ^ e := by
  unfold usigma
  rw [unitaryDivisors_prime_pow hp e]
  have h1 : (1 : ℕ) ≠ p ^ e := by
    intro h
    have := Nat.one_lt_pow he.ne' hp.one_lt
    omega
  rw [Finset.sum_pair h1]

/-- Unitary divisors are divisors. -/
theorem unitaryDivisors_subset_divisors (n : ℕ) : unitaryDivisors n ⊆ n.divisors :=
  Finset.filter_subset _ _

/-- For coprime `m, n`, the unitary divisors of `m * n` are the products `d₁ * d₂` of
unitary divisors `d₁ ∣ m`, `d₂ ∣ n`. -/
theorem unitaryDivisors_mul {m n : ℕ} (h : m.Coprime n) :
    unitaryDivisors (m * n) =
      (unitaryDivisors m ×ˢ unitaryDivisors n).image (fun p : ℕ × ℕ => p.1 * p.2) := by
  unfold unitaryDivisors
  rw [Nat.divisors_mul, ← Finset.image_mul_product, Finset.filter_image, ← Finset.filter_product]
  congr 1
  apply Finset.filter_congr
  rintro ⟨d₁, d₂⟩ hd
  simp only [Finset.mem_product, Nat.mem_divisors] at hd
  obtain ⟨⟨hd₁, -⟩, ⟨hd₂, -⟩⟩ := hd
  simp only
  rw [Nat.mul_div_mul_comm hd₁ hd₂]
  have h1 : d₁.Coprime (n / d₂) :=
    (h.coprime_dvd_left hd₁).coprime_dvd_right (Nat.div_dvd_of_dvd hd₂)
  have h2 : d₂.Coprime (m / d₁) :=
    ((h.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁)).coprime_dvd_right hd₂).symm
  rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  tauto

/-- `σ*` is multiplicative: `σ*(m n) = σ*(m) σ*(n)` for coprime `m, n`. -/
theorem usigma_mul {m n : ℕ} (h : m.Coprime n) : usigma (m * n) = usigma m * usigma n := by
  unfold usigma
  rw [unitaryDivisors_mul h, Finset.sum_image, Finset.sum_product, ← Finset.sum_mul_sum]
  intro x hx y hy hxy
  apply h.mul_injOn_divisors _ _ hxy
  · simp only [Finset.mem_coe, Finset.mem_product] at hx ⊢
    exact ⟨unitaryDivisors_subset_divisors m hx.1, unitaryDivisors_subset_divisors n hx.2⟩
  · simp only [Finset.mem_coe, Finset.mem_product] at hy ⊢
    exact ⟨unitaryDivisors_subset_divisors m hy.1, unitaryDivisors_subset_divisors n hy.2⟩

/-- On squarefree numbers every divisor is unitary, so `σ* = σ`. -/
theorem usigma_eq_sigma_of_squarefree {s : ℕ} (hs : Squarefree s) : usigma s = σ 1 s := by
  induction s using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    obtain ⟨-, rfl⟩ := (Nat.squarefree_pow_iff hp.ne_one hn.ne').1 hs
    rw [usigma_prime_pow hp hn, ArithmeticFunction.sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
  | zero => exact absurd hs not_squarefree_zero
  | one => rw [usigma_one]; simp
  | coprime a b _ _ hab iha ihb =>
    rw [Nat.squarefree_mul hab] at hs
    rw [usigma_mul hab, iha hs.1, ihb hs.2,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab]

/-! ### Reduction to the powerful core -/

/-- Reduction (4) of `PROOF.md`: attaching a squarefree factor `s` coprime to `m` does not
change membership in A063880, `A (m * s) ↔ A m`. -/
theorem a_mul_iff {m s : ℕ} (hs : Squarefree s) (h : m.Coprime s) : A (m * s) ↔ A m := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  have hσs : 0 < σ 1 s := ArithmeticFunction.sigma_pos 1 s hs.ne_zero
  have key : σ 1 (m * s) = σ 1 m * σ 1 s :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h
  have key2 : usigma (m * s) = usigma m * σ 1 s := by
    rw [usigma_mul h, usigma_eq_sigma_of_squarefree hs]
  unfold A
  rw [key, key2, Nat.mul_pos_iff_of_pos_right hs0, ← mul_assoc]
  constructor
  · rintro ⟨hm, heq⟩
    exact ⟨hm, Nat.eq_of_mul_eq_mul_right hσs heq⟩
  · rintro ⟨hm, heq⟩
    exact ⟨hm, by rw [heq]⟩

/-- Upstream `textbook` lemma `a_of_primitive_mul_squarefree` (sorry-backed upstream): a
primitive term times a coprime squarefree number is a term. -/
theorem a_of_primitive_mul_squarefree (m s : ℕ) (hm : IsPrimitiveTerm m)
    (hs : Squarefree s) (hcoprime : m.Coprime s) : A (m * s) :=
  (a_mul_iff hs hcoprime).2 hm.1

/-- Upstream `textbook` lemma `powerful_of_isPrimitiveTerm` (sorry-backed upstream): every
primitive term is powerful. -/
theorem powerful_of_isPrimitiveTerm {n : ℕ} (h : IsPrimitiveTerm n) : Powerful n := by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp h.1.1
  by_contra hsq
  obtain ⟨m, rfl⟩ := hp_dvd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
  have hpm : ¬ p ∣ m := by
    intro hpm
    apply hsq
    rw [pow_two]
    exact Nat.mul_dvd_mul_left p hpm
  have hcop : m.Coprime p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp_prime).2 hpm)
  have hAm : A m := by
    have : A (m * p) := by rw [mul_comm]; exact h.1
    exact (a_mul_iff hp_prime.prime.squarefree hcop).1 this
  have hmem : m ∈ (p * m).properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨Dvd.intro_left p rfl, ?_⟩
    have := hp_prime.two_le
    have := Nat.pos_of_ne_zero hm0
    nlinarith
  exact Set.disjoint_left.mp h.2 (by exact_mod_cast hmem) hAm

/-! ### The local-ratio inequalities and the two-prime Diophantine equation -/

/-- Key identity in `ℤ`: `(p - 1) * σ 1 (p ^ e) = p ^ e * p - 1`. -/
theorem sigma_prime_pow_key {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p : ℤ) - 1) * (σ 1 (p ^ e) : ℤ) = (p : ℤ) ^ e * p - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have G := geom_sum_mul (p : ℤ) (e + 1)
  push_cast
  rw [pow_succ] at G
  linear_combination G

/-- Local ratio of one prime power: `σ(p^e) < 2 (1 + p^e)`, so a prime power is never a
solution. -/
theorem sigma_prime_pow_lt {p : ℕ} (hp : p.Prime) (e : ℕ) :
    σ 1 (p ^ e) < 2 * (1 + p ^ e) := by
  have key := sigma_prime_pow_key hp e
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hX : (1 : ℤ) ≤ (p : ℤ) ^ e := one_le_pow₀ (by linarith)
  have hS : (0 : ℤ) ≤ (σ 1 (p ^ e) : ℤ) := by positivity
  have h : (σ 1 (p ^ e) : ℤ) < 2 * (1 + (p : ℤ) ^ e) := by
    by_contra hcon
    have hcon' : 2 * (1 + (p : ℤ) ^ e) ≤ (σ 1 (p ^ e) : ℤ) := not_lt.mp hcon
    have h1 : 0 ≤ ((p : ℤ) - 1) * ((σ 1 (p ^ e) : ℤ) - 2 * (1 + (p : ℤ) ^ e)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ ((p : ℤ) - 2) * (p : ℤ) ^ e := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, key]
  exact_mod_cast h

/-- For an odd prime `p ≥ 3`: `2 σ(p^a) < 3 (1 + p^a)`. -/
theorem two_mul_sigma_prime_pow_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (a : ℕ) :
    2 * σ 1 (p ^ a) < 3 * (1 + p ^ a) := by
  have key := sigma_prime_pow_key hp a
  have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hX : (1 : ℤ) ≤ (p : ℤ) ^ a := one_le_pow₀ (by linarith)
  have hS : (0 : ℤ) ≤ (σ 1 (p ^ a) : ℤ) := by positivity
  have h : 2 * (σ 1 (p ^ a) : ℤ) < 3 * (1 + (p : ℤ) ^ a) := by
    by_contra hcon
    have hcon' : 3 * (1 + (p : ℤ) ^ a) ≤ 2 * (σ 1 (p ^ a) : ℤ) := not_lt.mp hcon
    have h1 : 0 ≤ ((p : ℤ) - 1) * (2 * (σ 1 (p ^ a) : ℤ) - 3 * (1 + (p : ℤ) ^ a)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ ((p : ℤ) - 3) * (p : ℤ) ^ a := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, key]
  exact_mod_cast h

/-- For a prime `q ≥ 5`: `4 σ(q^b) < 5 (1 + q^b)`. -/
theorem four_mul_sigma_prime_pow_lt {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (b : ℕ) :
    4 * σ 1 (q ^ b) < 5 * (1 + q ^ b) := by
  have key := sigma_prime_pow_key hq b
  have hq5' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have hY : (1 : ℤ) ≤ (q : ℤ) ^ b := one_le_pow₀ (by linarith)
  have hS : (0 : ℤ) ≤ (σ 1 (q ^ b) : ℤ) := by positivity
  have h : 4 * (σ 1 (q ^ b) : ℤ) < 5 * (1 + (q : ℤ) ^ b) := by
    by_contra hcon
    have hcon' : 5 * (1 + (q : ℤ) ^ b) ≤ 4 * (σ 1 (q ^ b) : ℤ) := not_lt.mp hcon
    have h1 : 0 ≤ ((q : ℤ) - 1) * (4 * (σ 1 (q ^ b) : ℤ) - 5 * (1 + (q : ℤ) ^ b)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ ((q : ℤ) - 5) * (q : ℤ) ^ b := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, key]
  exact_mod_cast h

/-- Product bound: from `2 S < 3 X` and `4 T < 5 Y` (in `ℕ`) derive `S * T < 2 * (X * Y)`. -/
theorem mul_lt_two_mul_of_bounds {S T X Y : ℕ} (h1 : 2 * S < 3 * X) (h2 : 4 * T < 5 * Y) :
    S * T < 2 * (X * Y) := by
  have h3 : 2 * S * (4 * T) < 3 * X * (5 * Y) :=
    mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)
  have h4 : 8 * (S * T) < 8 * (2 * (X * Y)) := by
    have hXY : 0 ≤ X * Y := Nat.zero_le _
    nlinarith [h3, hXY]
  exact Nat.lt_of_mul_lt_mul_left h4

/-- Two distinct odd primes: `σ(p^a) σ(q^b) < 2 (1 + p^a)(1 + q^b)` (local ratios
`< 3/2 · 5/4 < 2`), so `p^a q^b` is never a solution. -/
theorem sigma_mul_sigma_lt_of_odd {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    σ 1 (p ^ a) * σ 1 (q ^ b) < 2 * ((1 + p ^ a) * (1 + q ^ b)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have hq4 : q ≠ 4 := by rintro rfl; norm_num at hq
  rcases (show 5 ≤ p ∨ 5 ≤ q by omega) with h5 | h5
  · have h1 := four_mul_sigma_prime_pow_lt hp h5 a
    have h2 := two_mul_sigma_prime_pow_lt hq hq3 b
    have h3 := mul_lt_two_mul_of_bounds h2 h1
    rw [mul_comm (σ 1 (q ^ b)), mul_comm (1 + q ^ b)] at h3
    exact h3
  · have h1 := two_mul_sigma_prime_pow_lt hp hp3 a
    have h2 := four_mul_sigma_prime_pow_lt hq h5 b
    exact mul_lt_two_mul_of_bounds h1 h2

/-- The two-prime Diophantine equation (7)–(9) of `PROOF.md`: if `q` is an odd prime,
`a, b ≥ 2` and `σ(2^a) σ(q^b) = 2 (1 + 2^a)(1 + q^b)`, then `q = 3`, `a = 2`, `b = 3`. -/
theorem eq_of_two_pow_mul_prime_pow {q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : σ 1 (2 ^ a) * σ 1 (q ^ b) = 2 * ((1 + 2 ^ a) * (1 + q ^ b))) :
    q = 3 ∧ a = 2 ∧ b = 3 := by
  -- Move the hypothesis to `ℤ`.
  have hZ : ((σ 1 (2 ^ a) : ℕ) : ℤ) * ((σ 1 (q ^ b) : ℕ) : ℤ)
      = 2 * ((1 + (2 : ℤ) ^ a) * (1 + (q : ℤ) ^ b)) := by
    exact_mod_cast h
  -- `σ(2^a) = 2·2^a - 1`.
  have h2 : ((σ 1 (2 ^ a) : ℕ) : ℤ) = 2 * (2 : ℤ) ^ a - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    have hg := geom_sum_mul (2 : ℤ) (a + 1)
    push_cast
    rw [pow_succ] at hg
    linarith
  -- `(q - 1)·σ(q^b) = q·q^b - 1`.
  have hqS : ((q : ℤ) - 1) * ((σ 1 (q ^ b) : ℕ) : ℤ) = (q : ℤ) * (q : ℤ) ^ b - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
    have hg := geom_sum_mul (q : ℤ) (b + 1)
    push_cast
    rw [pow_succ] at hg
    linarith
  -- Name the three quantities.
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (2 : ℤ) ^ a := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = (q : ℤ) ^ b := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = ((σ 1 (q ^ b) : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hS] at hZ
  rw [← hy, ← hS] at hqS
  rw [← hx] at h2
  rw [h2] at hZ
  -- Now `hZ : (2x - 1) S = 2 ((1 + x)(1 + y))`, `hqS : (q - 1) S = q y - 1`.
  have key : (3 : ℤ) = q * (3 * y + 2 * x + 2) - 2 * y * (x + 1) := by
    linear_combination (q - 1) * hZ - (2 * x - 1) * hqS
  have hqy : (q : ℤ) ∣ y := by
    rw [hy]; exact dvd_pow_self _ (by omega)
  have hdvd : (q : ℤ) ∣ 3 := by
    rw [key]
    exact dvd_sub (dvd_mul_right _ _) (Dvd.dvd.mul_right (Dvd.dvd.mul_left hqy _) _)
  have hq3 : q = 3 := by
    have h3 : q ∣ 3 := by exact_mod_cast hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3
  subst hq3
  push_cast at hqS hy
  -- `(2x - 7)(y - 3) = 24`.
  have key2 : (2 * x - 7) * (y - 3) = 24 := by
    linear_combination 2 * hZ - (2 * x - 1) * hqS
  have hy9 : (9 : ℤ) ≤ y := by
    rw [hy]
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have ha2 : a = 2 := by
    by_contra hne
    have ha3 : 3 ≤ a := by omega
    have hx8 : (8 : ℤ) ≤ x := by
      rw [hx]
      calc (8 : ℤ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha3
    have h1 : (9 : ℤ) ≤ 2 * x - 7 := by linarith
    have h2 : (6 : ℤ) ≤ y - 3 := by linarith
    have hm := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  subst ha2
  have hx4 : x = 4 := by rw [hx]; norm_num
  subst hx4
  have hy27 : (3 : ℤ) ^ b = 3 ^ 3 := by rw [← hy]; linarith
  have hb3 : (3 : ℕ) ^ b = 3 ^ 3 := by exact_mod_cast hy27
  have hb3' : b = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hb3
  exact ⟨rfl, rfl, hb3'⟩

/-! ### Classification -/

/-- Helper: `A` fails for a nontrivial prime power. -/
theorem not_a_prime_pow {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) : ¬ A (p ^ e) := by
  rintro ⟨-, hσ⟩
  rw [usigma_prime_pow hp he] at hσ
  have := sigma_prime_pow_lt hp e
  rw [hσ] at this
  exact lt_irrefl _ this

/-- Helper: the two-prime powerful case forces `p ^ a * q ^ b = 108`. -/
theorem eq_108_of_a_two_prime_pow {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (h : A (p ^ a * q ^ b)) : p ^ a * q ^ b = 108 := by
  obtain ⟨-, hσ⟩ := h
  have hcop : (p ^ a).Coprime (q ^ b) := ((Nat.coprime_primes hp hq).2 hpq).pow a b
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, usigma_mul hcop,
    usigma_prime_pow hp (by omega), usigma_prime_pow hq (by omega)] at hσ
  rcases eq_or_ne p 2 with rfl | hp2
  · have hq2 : q ≠ 2 := fun h => hpq h.symm
    obtain ⟨rfl, rfl, rfl⟩ := eq_of_two_pow_mul_prime_pow hq hq2 ha hb hσ
    norm_num
  · rcases eq_or_ne q 2 with rfl | hq2
    · have hσ' : σ 1 (2 ^ b) * σ 1 (p ^ a) = 2 * ((1 + 2 ^ b) * (1 + p ^ a)) := by
        rw [mul_comm (σ 1 (p ^ a)), mul_comm (1 + p ^ a)] at hσ
        exact hσ
      obtain ⟨rfl, rfl, rfl⟩ := eq_of_two_pow_mul_prime_pow hp hp2 hb ha hσ'
      norm_num
    · have hlt := sigma_mul_sigma_lt_of_odd (a := a) (b := b) hp hq hp2 hq2 hpq
      rw [hσ] at hlt
      exact absurd hlt (lt_irrefl _)

/-- A powerful solution with at most two distinct prime factors is `108`. -/
theorem eq_108_of_powerful {n : ℕ} (h : A n) (hpow : Powerful n)
    (hcard : n.primeFactors.card ≤ 2) : n = 108 := by
  have hn : n ≠ 0 := h.1.ne'
  have hfact := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at hfact
  rcases Nat.lt_or_ge n.primeFactors.card 2 with hlt | hge
  · rcases Nat.lt_or_ge n.primeFactors.card 1 with hlt1 | hge1
    · -- no prime factors: `n = 1`
      have h0 : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [Nat.primeFactors_eq_empty] at h0
      rcases h0 with rfl | rfl
      · exact absurd rfl hn
      · exfalso
        obtain ⟨-, hσ⟩ := h
        rw [usigma_one] at hσ
        simp at hσ
    · -- exactly one prime factor: `n = p ^ e`
      have h1 : n.primeFactors.card = 1 := by omega
      obtain ⟨p, hs⟩ := Finset.card_eq_one.mp h1
      have hpmem : p ∈ n.primeFactors := by rw [hs]; simp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
      rw [hs, Finset.prod_singleton] at hfact
      have he : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hpdvd
      rw [← hfact] at h
      exact absurd h (not_a_prime_pow hp he)
  · -- exactly two prime factors: `n = p ^ a * q ^ b`
    have h2 : n.primeFactors.card = 2 := le_antisymm hcard hge
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h2
    have hpmem : p ∈ n.primeFactors := by rw [hs]; simp
    have hqmem : q ∈ n.primeFactors := by rw [hs]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    rw [hs, Finset.prod_pair hpq] at hfact
    have ha : 2 ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).mp (hpow p hpmem)
    have hb : 2 ≤ n.factorization q := (hq.pow_dvd_iff_le_factorization hn).mp (hpow q hqmem)
    rw [← hfact] at h
    rw [← hfact]
    exact eq_108_of_a_two_prime_pow hp hq hpq ha hb h

/-- **Main theorem** (`PROOF.md`): if `n ∈ A063880` and at most two primes `p` satisfy
`p² ∣ n` (i.e. `ω(C(n)) ≤ 2`), then `n = 108 s` with `s` squarefree and coprime to `108`
(i.e. the powerful core of `n` is `108`). -/
theorem exists_eq_108_mul_of_card_le_two {n : ℕ} (h : A n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2) :
    ∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn : 0 < n := h.1
    by_cases hex : ∃ p ∈ n.primeFactors, ¬ p ^ 2 ∣ n
    · obtain ⟨p, hpmem, hp2⟩ := hex
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
      obtain ⟨m, rfl⟩ := hpn
      have hpm : ¬ p ∣ m := fun hpm => hp2 (by rw [pow_two]; exact mul_dvd_mul_left p hpm)
      have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hn)
      have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
      have hsqp : Squarefree p := hp.squarefree
      have hAm : A m := by
        rw [mul_comm] at h
        exact (a_mul_iff hsqp hcop).1 h
      have hlt : m < p * m := by
        have := hp.two_le
        nlinarith
      have hsub : (m.primeFactors.filter fun q => q ^ 2 ∣ m) ⊆
          ((p * m).primeFactors.filter fun q => q ^ 2 ∣ p * m) := by
        intro q hq
        rw [Finset.mem_filter] at hq ⊢
        refine ⟨?_, Dvd.dvd.mul_left hq.2 p⟩
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1.1, Dvd.dvd.mul_left hq.1.2.1 p, by positivity⟩
      have hcard : (m.primeFactors.filter fun q => q ^ 2 ∣ m).card ≤ 2 :=
        le_trans (Finset.card_le_card hsub) hω
      obtain ⟨s, hs, hcs, rfl⟩ := ih m hlt hAm hcard
      refine ⟨s * p, ?_, ?_, by ring⟩
      · have hsp : Nat.Coprime s p :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpm (h.mul_left 108))).symm
        exact (Nat.squarefree_mul hsp).2 ⟨hs, hsqp⟩
      · have h108p : Nat.Coprime 108 p :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpm (h.mul_right s))).symm
        exact Nat.Coprime.mul_right hcs h108p
    · have hex' : ∀ p ∈ n.primeFactors, p ^ 2 ∣ n :=
        fun p hp => not_not.mp (fun h => hex ⟨p, hp, h⟩)
      have hpow : Powerful n := hex'
      have hfilt : (n.primeFactors.filter fun p => p ^ 2 ∣ n) = n.primeFactors :=
        Finset.filter_true_of_mem hex'
      rw [hfilt] at hω
      refine ⟨1, squarefree_one, Nat.coprime_one_right 108, ?_⟩
      rw [eq_108_of_powerful h hpow hω]

/-- Sanity check (upstream test theorem `a_108`): `108 ∈ A063880`. -/
theorem a_108 : A 108 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- Conversely, `108 s ∈ A063880` for every squarefree `s` coprime to `108`. -/
theorem a_108_mul {s : ℕ} (hs : Squarefree s) (h : Nat.Coprime 108 s) : A (108 * s) :=
  (a_mul_iff hs h).2 a_108

/-- Conversely, `108 s` (with `s` squarefree and coprime to `108`) lies in the subfamily:
the primes `p` with `p² ∣ 108 s` are exactly `2` and `3`, so `ω(C(108 s)) = 2`. -/
theorem primeFactors_filter_sq_dvd_108_mul {s : ℕ} (hs : Squarefree s) (h : Nat.Coprime 108 s) :
    ((108 * s).primeFactors.filter fun p => p ^ 2 ∣ 108 * s) = {2, 3} := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h
  have hne : 108 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp, -, -⟩, hp2⟩
    by_cases h108 : p ∣ 108
    · have h' : p ∣ 2 ^ 2 * 3 ^ 3 := by
        rw [show (2 : ℕ) ^ 2 * 3 ^ 3 = 108 by norm_num]; exact h108
      rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      · right
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
    · exfalso
      have hcop : Nat.Coprime (p ^ 2) 108 :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h108)
      have hp2s : p ^ 2 ∣ s := hcop.dvd_of_dvd_mul_left hp2
      exact (Nat.squarefree_iff_prime_squarefree.1 hs) p hp (by rwa [← pow_two])
  · rintro (rfl | rfl)
    · exact ⟨⟨Nat.prime_two, Dvd.dvd.mul_right (by norm_num) s, hne⟩,
        Dvd.dvd.mul_right (by norm_num) s⟩
    · exact ⟨⟨Nat.prime_three, Dvd.dvd.mul_right (by norm_num) s, hne⟩,
        Dvd.dvd.mul_right (by norm_num) s⟩

/-- In the subfamily `ω(C(n)) ≤ 2`, every term is `108 (mod 216)`
(the upstream conjecture `mod_216_of_a` restricted to that subfamily). -/
theorem mod_216_of_card_le_two {n : ℕ} (h : A n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2) : n % 216 = 108 := by
  obtain ⟨s, hs, hcs, rfl⟩ := exists_eq_108_mul_of_card_le_two h hω
  have h2 : Nat.Coprime 2 s := Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 108) hcs
  have hodd : ¬ 2 ∣ s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 h2
  omega

/-- In the subfamily `ω(C(n)) ≤ 2`, the only primitive term is `108`
(the upstream conjecture `unique_primitive_108` restricted to that subfamily). -/
theorem eq_108_of_isPrimitiveTerm_of_card_le_two {n : ℕ} (h : IsPrimitiveTerm n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2) : n = 108 := by
  have hA : A n := h.1
  obtain ⟨s, hs, hcs, rfl⟩ := exists_eq_108_mul_of_card_le_two hA hω
  by_cases hs1 : s = 1
  · subst hs1; rfl
  · exfalso
    have hs0 : s ≠ 0 := by rintro rfl; simp [A] at hA
    have hs2 : 2 ≤ s := by omega
    have hmem : 108 ∈ (108 * s).properDivisors :=
      Nat.mem_properDivisors.2 ⟨dvd_mul_right 108 s, by omega⟩
    exact Set.disjoint_left.mp h.2 hmem a_108

/-- Sanity check (upstream test theorem `isPrimitiveTerm_108`): `108` is a primitive term. -/
theorem isPrimitiveTerm_108 : IsPrimitiveTerm 108 := by
  refine ⟨a_108, ?_⟩
  rw [Set.disjoint_left]
  intro d hd hAd
  have hd' : d ∈ (108 : ℕ).properDivisors := hd
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.1 hd'
  have hAd' : A d := hAd
  have hcard : (d.primeFactors.filter fun p => p ^ 2 ∣ d).card ≤ 2 := by
    calc _ ≤ d.primeFactors.card := Finset.card_filter_le _ _
      _ ≤ (108 : ℕ).primeFactors.card :=
          Finset.card_le_card (Nat.primeFactors_mono hdvd (by norm_num))
      _ = 2 := by
          simp only [Nat.primeFactors, Nat.primeFactorsList_ofNat]
          decide
  obtain ⟨s, hs, hcs, rfl⟩ := exists_eq_108_mul_of_card_le_two hAd' hcard
  have : s ≠ 0 := by rintro rfl; simp [A] at hAd'
  omega

/-! ## Three-prime cores (`THREE_PRIMES.md`)

`not_a_three_prime_pow`: no powerful `p^a q^b r^c` (distinct primes, exponents `≥ 2`) is a
term. With `p < q < r` there are three cases: all primes odd (`caseB`: local-ratio bounds and
three finite boxes), `{p, q} = {2, 3}` (`case23`: ratio bounds and a congruence), and
`p = 2 < 5 ≤ q` (`caseA`: the integer equation `W_q W_r = K(K+3) t_q t_r`, 2-adic
valuations, size bounds, five finite boxes and a finite quadratic check). The induction of
`exists_eq_108_mul_of_card_le_two`, run with the bound `3`, then gives
`exists_eq_108_mul_of_card_le_three`.

### Local-ratio toolkit -/

/-- Monotonicity of the local ratio `σ(p^e) / (1 + p^e)` in the exponent. -/
theorem sigma_prime_pow_mono {p : ℕ} (hp : p.Prime) {e e' : ℕ} (h : e ≤ e') :
    σ 1 (p ^ e) * (1 + p ^ e') ≤ σ 1 (p ^ e') * (1 + p ^ e) := by
  have k1 := sigma_prime_pow_key hp e
  have k2 := sigma_prime_pow_key hp e'
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hxy : (p : ℤ) ^ e ≤ (p : ℤ) ^ e' := pow_le_pow_right₀ (by linarith) h
  have hD : ((p : ℤ) - 1) * ((σ 1 (p ^ e) : ℤ) * (1 + (p : ℤ) ^ e')
      - (σ 1 (p ^ e') : ℤ) * (1 + (p : ℤ) ^ e)) = ((p : ℤ) + 1) * ((p : ℤ) ^ e - (p : ℤ) ^ e') := by
    linear_combination (1 + (p : ℤ) ^ e') * k1 - (1 + (p : ℤ) ^ e) * k2
  have h' : (σ 1 (p ^ e) : ℤ) * (1 + (p : ℤ) ^ e') ≤ (σ 1 (p ^ e') : ℤ) * (1 + (p : ℤ) ^ e) := by
    by_contra hc
    push Not at hc
    have h1 : 0 < ((p : ℤ) - 1) * ((σ 1 (p ^ e) : ℤ) * (1 + (p : ℤ) ^ e')
        - (σ 1 (p ^ e') : ℤ) * (1 + (p : ℤ) ^ e)) := mul_pos (by linarith) (by linarith)
    have h2 : ((p : ℤ) + 1) * ((p : ℤ) ^ e - (p : ℤ) ^ e') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  exact_mod_cast h'

/-- Lower bound `σ(p^e)/(1+p^e) ≥ σ(p^e₀)/(1+p^e₀)` for `e ≥ e₀`, as `N * u ≤ D * s`. -/
theorem sigma_ge_of_le {p e₀ e : ℕ} (hp : p.Prime) (h : e₀ ≤ e) :
    σ 1 (p ^ e₀) * (1 + p ^ e) ≤ (1 + p ^ e₀) * σ 1 (p ^ e) := by
  have := sigma_prime_pow_mono hp h
  linarith [mul_comm (σ 1 (p ^ e)) (1 + p ^ e₀)]

/-- Upper bound `σ(p^e)/(1+p^e) ≤ σ(p^e₁)/(1+p^e₁)` for `e ≤ e₁`, as `D * s ≤ N * u`. -/
theorem sigma_le_of_le {p e e₁ : ℕ} (hp : p.Prime) (h : e ≤ e₁) :
    (1 + p ^ e₁) * σ 1 (p ^ e) ≤ σ 1 (p ^ e₁) * (1 + p ^ e) := by
  have := sigma_prime_pow_mono hp h
  linarith [mul_comm (σ 1 (p ^ e)) (1 + p ^ e₁)]

/-- The limit bound `σ(p^e)/(1+p^e) < p/(p-1)`, in the form `(p-1) σ(p^e) ≤ p (1+p^e)`. -/
theorem sigma_le_limit {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p - 1) * σ 1 (p ^ e) ≤ p * (1 + p ^ e) := by
  have key := sigma_prime_pow_key hp e
  have h1 : 1 ≤ p := hp.one_le
  have hX : (0 : ℤ) ≤ (p : ℤ) ^ e := by positivity
  have h' : (((p - 1) * σ 1 (p ^ e) : ℕ) : ℤ) ≤ ((p * (1 + p ^ e) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    nlinarith [key]
  exact_mod_cast h'

/-- `m σ(p^e) < (m+1)(1+p^e)` whenever `p ≥ m + 1`. -/
theorem mul_sigma_lt_of_le {p m : ℕ} (hp : p.Prime) (hm : m + 1 ≤ p) (e : ℕ) :
    m * σ 1 (p ^ e) < (m + 1) * (1 + p ^ e) := by
  have key := sigma_prime_pow_key hp e
  have hm' : ((m : ℤ) + 1) ≤ p := by exact_mod_cast hm
  have hX : (1 : ℤ) ≤ (p : ℤ) ^ e := one_le_pow₀ (by linarith)
  have hS : (0 : ℤ) ≤ (σ 1 (p ^ e) : ℤ) := by positivity
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have h : (m : ℤ) * (σ 1 (p ^ e) : ℤ) < ((m : ℤ) + 1) * (1 + (p : ℤ) ^ e) := by
    by_contra hc
    push Not at hc
    have h1 : 0 ≤ ((p : ℤ) - 1) *
        ((m : ℤ) * (σ 1 (p ^ e) : ℤ) - ((m : ℤ) + 1) * (1 + (p : ℤ) ^ e)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ ((p : ℤ) - (m : ℤ) - 1) * (p : ℤ) ^ e := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, key]
  exact_mod_cast h

/-- `1 + p^e ≤ σ(p^e)` for `e ≥ 1` (with factors `1`, in the shape used by `prod3_gt`). -/
theorem one_add_pow_le_sigma {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    1 * (1 + p ^ e) ≤ 1 * σ 1 (p ^ e) := by
  rw [one_mul, one_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ i ∈ Finset.range d, p ^ (i + 1) := Nat.zero_le _
  omega

/-- Product of three ratio upper bounds. -/
theorem prod3_lt {s1 s2 s3 u1 u2 u3 N1 N2 N3 D1 D2 D3 : ℕ}
    (h1 : D1 * s1 ≤ N1 * u1) (h2 : D2 * s2 ≤ N2 * u2) (h3 : D3 * s3 ≤ N3 * u3)
    (hu : 0 < u1 * u2 * u3) (hN : N1 * N2 * N3 < 2 * (D1 * D2 * D3)) :
    s1 * s2 * s3 < 2 * (u1 * u2 * u3) := by
  have h123 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have e1 : D1 * s1 * (D2 * s2) * (D3 * s3) = (D1 * D2 * D3) * (s1 * s2 * s3) := by ring
  have e2 : N1 * u1 * (N2 * u2) * (N3 * u3) = (N1 * N2 * N3) * (u1 * u2 * u3) := by ring
  rw [e1, e2] at h123
  have h4 : (N1 * N2 * N3) * (u1 * u2 * u3) < (2 * (D1 * D2 * D3)) * (u1 * u2 * u3) :=
    Nat.mul_lt_mul_of_pos_right hN hu
  have h5 : (D1 * D2 * D3) * (s1 * s2 * s3) < (D1 * D2 * D3) * (2 * (u1 * u2 * u3)) := by
    calc _ ≤ _ := h123
      _ < _ := h4
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_left h5

/-- Product of three ratio lower bounds. -/
theorem prod3_gt {s1 s2 s3 u1 u2 u3 N1 N2 N3 D1 D2 D3 : ℕ}
    (h1 : N1 * u1 ≤ D1 * s1) (h2 : N2 * u2 ≤ D2 * s2) (h3 : N3 * u3 ≤ D3 * s3)
    (hu : 0 < u1 * u2 * u3) (hN : 2 * (D1 * D2 * D3) < N1 * N2 * N3) :
    2 * (u1 * u2 * u3) < s1 * s2 * s3 := by
  have h123 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have e1 : D1 * s1 * (D2 * s2) * (D3 * s3) = (D1 * D2 * D3) * (s1 * s2 * s3) := by ring
  have e2 : N1 * u1 * (N2 * u2) * (N3 * u3) = (N1 * N2 * N3) * (u1 * u2 * u3) := by ring
  rw [e1, e2] at h123
  have h4 : (2 * (D1 * D2 * D3)) * (u1 * u2 * u3) < (N1 * N2 * N3) * (u1 * u2 * u3) :=
    Nat.mul_lt_mul_of_pos_right hN hu
  have h5 : (D1 * D2 * D3) * (2 * (u1 * u2 * u3)) < (D1 * D2 * D3) * (s1 * s2 * s3) := by
    calc _ = (2 * (D1 * D2 * D3)) * (u1 * u2 * u3) := by ring
      _ < _ := h4
      _ ≤ _ := h123
  exact Nat.lt_of_mul_lt_mul_left h5

example : σ 1 (3 ^ 4) = 121 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  simp [Finset.sum_range_succ]

/-! ### Finite boxes

Each box fixes the three primes (and possibly bounds on the exponents) and splits the
exponent ranges until, in every leaf, the bounds `sigma_ge_of_le`, `sigma_le_of_le`,
`sigma_le_limit` on the three local ratios put their product strictly above or below `2`. -/

/-- No solution `3^a 5^b 7^c`, `a, b, c ≥ 2`, by nested monotone ratio bounds (4 leaves). -/
theorem box_3_5_7 {a b c : ℕ} (_ha₀ : 2 ≤ a) (hb₀ : 2 ≤ b) (hc₀ : 2 ≤ c)
    (h : σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (7 ^ c) =
      2 * ((1 + 3 ^ a) * (1 + 5 ^ b) * (1 + 7 ^ c))) : False := by
  have hp7 : Nat.Prime 7 := by norm_num
  rcases Nat.lt_or_ge a 3 with hs1 | hs1
  · have b1 := sigma_le_of_le (e₁ := 2) Nat.prime_three (show a ≤ 2 by omega)
    have b2 := sigma_le_limit Nat.prime_five b
    have b3 := sigma_le_limit hp7 c
    refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  · rcases Nat.lt_or_ge a 4 with hs2 | hs2
    · rcases Nat.lt_or_ge b 3 with hs3 | hs3
      · have b1 := sigma_le_of_le (e₁ := 3) Nat.prime_three (show a ≤ 3 by omega)
        have b2 := sigma_le_of_le (e₁ := 2) Nat.prime_five (show b ≤ 2 by omega)
        have b3 := sigma_le_limit hp7 c
        refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
        rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_three]
        rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
        norm_num [Finset.sum_range_succ]
      · have b1 := sigma_ge_of_le (e₀ := 3) Nat.prime_three (show 3 ≤ a by omega)
        have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
        have b3 := sigma_ge_of_le (e₀ := 2) hp7 (show 2 ≤ c by omega)
        refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
        rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_three]
        rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
        rw [sigma_one_apply_prime_pow (i := 2) hp7]
        norm_num [Finset.sum_range_succ]
    · have b1 := sigma_ge_of_le (e₀ := 4) Nat.prime_three (show 4 ≤ a by omega)
      have b2 := sigma_ge_of_le (e₀ := 2) Nat.prime_five (show 2 ≤ b by omega)
      have b3 := sigma_ge_of_le (e₀ := 2) hp7 (show 2 ≤ c by omega)
      refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
      rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
      rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
      rw [sigma_one_apply_prime_pow (i := 2) hp7]
      norm_num [Finset.sum_range_succ]

/-- No solution `3^a 5^b 11^c`, `a, b, c ≥ 2`, by nested monotone ratio bounds (7 leaves). -/
theorem box_3_5_11 {a b c : ℕ} (_ha₀ : 2 ≤ a) (_hb₀ : 2 ≤ b) (hc₀ : 2 ≤ c)
    (h : σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (11 ^ c) =
      2 * ((1 + 3 ^ a) * (1 + 5 ^ b) * (1 + 11 ^ c))) : False := by
  have hp11 : Nat.Prime 11 := by norm_num
  rcases Nat.lt_or_ge a 3 with hs1 | hs1
  · have b1 := sigma_le_of_le (e₁ := 2) Nat.prime_three (show a ≤ 2 by omega)
    have b2 := sigma_le_limit Nat.prime_five b
    have b3 := sigma_le_limit hp11 c
    refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  · rcases Nat.lt_or_ge a 4 with hs2 | hs2
    · have b1 := sigma_le_of_le (e₁ := 3) Nat.prime_three (show a ≤ 3 by omega)
      have b2 := sigma_le_limit Nat.prime_five b
      have b3 := sigma_le_limit hp11 c
      refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
      rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_three]
      norm_num [Finset.sum_range_succ]
    · rcases Nat.lt_or_ge b 3 with hs3 | hs3
      · have b1 := sigma_le_limit Nat.prime_three a
        have b2 := sigma_le_of_le (e₁ := 2) Nat.prime_five (show b ≤ 2 by omega)
        have b3 := sigma_le_limit hp11 c
        refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
        rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
        norm_num [Finset.sum_range_succ]
      · rcases Nat.lt_or_ge a 5 with hs4 | hs4
        · rcases Nat.lt_or_ge b 4 with hs5 | hs5
          · rcases Nat.lt_or_ge c 3 with hs6 | hs6
            · have b1 := sigma_le_of_le (e₁ := 4) Nat.prime_three (show a ≤ 4 by omega)
              have b2 := sigma_le_of_le (e₁ := 3) Nat.prime_five (show b ≤ 3 by omega)
              have b3 := sigma_le_of_le (e₁ := 2) hp11 (show c ≤ 2 by omega)
              refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
              rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
              rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
              rw [sigma_one_apply_prime_pow (i := 2) hp11]
              norm_num [Finset.sum_range_succ]
            · have b1 := sigma_ge_of_le (e₀ := 4) Nat.prime_three (show 4 ≤ a by omega)
              have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
              have b3 := sigma_ge_of_le (e₀ := 3) hp11 (show 3 ≤ c by omega)
              refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
              rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
              rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
              rw [sigma_one_apply_prime_pow (i := 3) hp11]
              norm_num [Finset.sum_range_succ]
          · have b1 := sigma_ge_of_le (e₀ := 4) Nat.prime_three (show 4 ≤ a by omega)
            have b2 := sigma_ge_of_le (e₀ := 4) Nat.prime_five (show 4 ≤ b by omega)
            have b3 := sigma_ge_of_le (e₀ := 2) hp11 (show 2 ≤ c by omega)
            refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
            rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
            rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_five]
            rw [sigma_one_apply_prime_pow (i := 2) hp11]
            norm_num [Finset.sum_range_succ]
        · have b1 := sigma_ge_of_le (e₀ := 5) Nat.prime_three (show 5 ≤ a by omega)
          have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
          have b3 := sigma_ge_of_le (e₀ := 2) hp11 (show 2 ≤ c by omega)
          refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
          rw [sigma_one_apply_prime_pow (i := 5) Nat.prime_three]
          rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
          rw [sigma_one_apply_prime_pow (i := 2) hp11]
          norm_num [Finset.sum_range_succ]

/-- No solution `3^a 5^b 13^c`, `a, b, c ≥ 2`, by nested monotone ratio bounds (9 leaves). -/
theorem box_3_5_13 {a b c : ℕ} (_ha₀ : 2 ≤ a) (_hb₀ : 2 ≤ b) (hc₀ : 2 ≤ c)
    (h : σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (13 ^ c) =
      2 * ((1 + 3 ^ a) * (1 + 5 ^ b) * (1 + 13 ^ c))) : False := by
  have hp13 : Nat.Prime 13 := by norm_num
  rcases Nat.lt_or_ge a 3 with hs1 | hs1
  · have b1 := sigma_le_of_le (e₁ := 2) Nat.prime_three (show a ≤ 2 by omega)
    have b2 := sigma_le_limit Nat.prime_five b
    have b3 := sigma_le_limit hp13 c
    refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  · rcases Nat.lt_or_ge a 4 with hs2 | hs2
    · have b1 := sigma_le_of_le (e₁ := 3) Nat.prime_three (show a ≤ 3 by omega)
      have b2 := sigma_le_limit Nat.prime_five b
      have b3 := sigma_le_limit hp13 c
      refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
      rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_three]
      norm_num [Finset.sum_range_succ]
    · rcases Nat.lt_or_ge b 3 with hs3 | hs3
      · have b1 := sigma_le_limit Nat.prime_three a
        have b2 := sigma_le_of_le (e₁ := 2) Nat.prime_five (show b ≤ 2 by omega)
        have b3 := sigma_le_limit hp13 c
        refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
        rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
        norm_num [Finset.sum_range_succ]
      · rcases Nat.lt_or_ge a 5 with hs4 | hs4
        · have b1 := sigma_le_of_le (e₁ := 4) Nat.prime_three (show a ≤ 4 by omega)
          have b2 := sigma_le_limit Nat.prime_five b
          have b3 := sigma_le_limit hp13 c
          refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
          rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
          norm_num [Finset.sum_range_succ]
        · rcases Nat.lt_or_ge b 4 with hs5 | hs5
          · rcases Nat.lt_or_ge c 3 with hs6 | hs6
            · have b1 := sigma_le_limit Nat.prime_three a
              have b2 := sigma_le_of_le (e₁ := 3) Nat.prime_five (show b ≤ 3 by omega)
              have b3 := sigma_le_of_le (e₁ := 2) hp13 (show c ≤ 2 by omega)
              refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
              rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
              rw [sigma_one_apply_prime_pow (i := 2) hp13]
              norm_num [Finset.sum_range_succ]
            · rcases Nat.lt_or_ge a 6 with hs7 | hs7
              · rcases Nat.lt_or_ge c 4 with hs8 | hs8
                · have b1 := sigma_le_of_le (e₁ := 5) Nat.prime_three (show a ≤ 5 by omega)
                  have b2 := sigma_le_of_le (e₁ := 3) Nat.prime_five (show b ≤ 3 by omega)
                  have b3 := sigma_le_of_le (e₁ := 3) hp13 (show c ≤ 3 by omega)
                  refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
                  rw [sigma_one_apply_prime_pow (i := 5) Nat.prime_three]
                  rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
                  rw [sigma_one_apply_prime_pow (i := 3) hp13]
                  norm_num [Finset.sum_range_succ]
                · have b1 := sigma_ge_of_le (e₀ := 5) Nat.prime_three (show 5 ≤ a by omega)
                  have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
                  have b3 := sigma_ge_of_le (e₀ := 4) hp13 (show 4 ≤ c by omega)
                  refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
                  rw [sigma_one_apply_prime_pow (i := 5) Nat.prime_three]
                  rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
                  rw [sigma_one_apply_prime_pow (i := 4) hp13]
                  norm_num [Finset.sum_range_succ]
              · have b1 := sigma_ge_of_le (e₀ := 6) Nat.prime_three (show 6 ≤ a by omega)
                have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
                have b3 := sigma_ge_of_le (e₀ := 3) hp13 (show 3 ≤ c by omega)
                refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
                rw [sigma_one_apply_prime_pow (i := 6) Nat.prime_three]
                rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
                rw [sigma_one_apply_prime_pow (i := 3) hp13]
                norm_num [Finset.sum_range_succ]
          · have b1 := sigma_ge_of_le (e₀ := 5) Nat.prime_three (show 5 ≤ a by omega)
            have b2 := sigma_ge_of_le (e₀ := 4) Nat.prime_five (show 4 ≤ b by omega)
            have b3 := sigma_ge_of_le (e₀ := 2) hp13 (show 2 ≤ c by omega)
            refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
            rw [sigma_one_apply_prime_pow (i := 5) Nat.prime_three]
            rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_five]
            rw [sigma_one_apply_prime_pow (i := 2) hp13]
            norm_num [Finset.sum_range_succ]


/-- No solution `2^2 5^b 7^c`, `b ≥ 2`, `c ≥ 7`, by nested monotone ratio bounds (2 leaves). -/
theorem box_2_5_7_c7 {a b c : ℕ} (ha₀ : 2 ≤ a) (ha₁ : a ≤ 2) (_hb₀ : 2 ≤ b) (hc₀ : 7 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (5 ^ b) * σ 1 (7 ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 5 ^ b) * (1 + 7 ^ c))) : False := by
  have hp7 : Nat.Prime 7 := by norm_num
  rcases Nat.lt_or_ge b 3 with hs1 | hs1
  · have b1 := sigma_le_of_le (e₁ := 2) Nat.prime_two (show a ≤ 2 by omega)
    have b2 := sigma_le_of_le (e₁ := 2) Nat.prime_five (show b ≤ 2 by omega)
    have b3 := sigma_le_limit hp7 c
    refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_two]
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
    norm_num [Finset.sum_range_succ]
  · have b1 := sigma_ge_of_le (e₀ := 2) Nat.prime_two (show 2 ≤ a by omega)
    have b2 := sigma_ge_of_le (e₀ := 3) Nat.prime_five (show 3 ≤ b by omega)
    have b3 := sigma_ge_of_le (e₀ := 7) hp7 (show 7 ≤ c by omega)
    refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_two]
    rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_five]
    rw [sigma_one_apply_prime_pow (i := 7) hp7]
    norm_num [Finset.sum_range_succ]

/-- No solution `2^3 5^b 7^c`, `b, c ≥ 2`, by monotone ratio bounds (1 leaf). -/
theorem box_2_5_7_a3 {a b c : ℕ} (ha₀ : 3 ≤ a) (_ha₁ : a ≤ 3) (hb₀ : 2 ≤ b) (hc₀ : 2 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (5 ^ b) * σ 1 (7 ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 5 ^ b) * (1 + 7 ^ c))) : False := by
  have hp7 : Nat.Prime 7 := by norm_num
  have b1 := sigma_ge_of_le (e₀ := 3) Nat.prime_two (show 3 ≤ a by omega)
  have b2 := sigma_ge_of_le (e₀ := 2) Nat.prime_five (show 2 ≤ b by omega)
  have b3 := sigma_ge_of_le (e₀ := 2) hp7 (show 2 ≤ c by omega)
  refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
  rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_two]
  rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_five]
  rw [sigma_one_apply_prime_pow (i := 2) hp7]
  norm_num [Finset.sum_range_succ]

/-- No solution `2^2 5^b 7^c`, `b ≥ 7`, `c ≥ 4`, by monotone ratio bounds (1 leaf). -/
theorem box_2_5_7_b7 {a b c : ℕ} (ha₀ : 2 ≤ a) (_ha₁ : a ≤ 2) (hb₀ : 7 ≤ b) (hc₀ : 4 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (5 ^ b) * σ 1 (7 ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 5 ^ b) * (1 + 7 ^ c))) : False := by
  have hp7 : Nat.Prime 7 := by norm_num
  have b1 := sigma_ge_of_le (e₀ := 2) Nat.prime_two (show 2 ≤ a by omega)
  have b2 := sigma_ge_of_le (e₀ := 7) Nat.prime_five (show 7 ≤ b by omega)
  have b3 := sigma_ge_of_le (e₀ := 4) hp7 (show 4 ≤ c by omega)
  refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
  rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_two]
  rw [sigma_one_apply_prime_pow (i := 7) Nat.prime_five]
  rw [sigma_one_apply_prime_pow (i := 4) hp7]
  norm_num [Finset.sum_range_succ]

/-- No solution `2^2 5^b 11^c`, `b, c ≥ 2`, by monotone ratio bounds (1 leaf). -/
theorem box_2_5_11 {a b c : ℕ} (_ha₀ : 2 ≤ a) (ha₁ : a ≤ 2) (_hb₀ : 2 ≤ b) (_hc₀ : 2 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (5 ^ b) * σ 1 (11 ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 5 ^ b) * (1 + 11 ^ c))) : False := by
  have hp11 : Nat.Prime 11 := by norm_num
  have b1 := sigma_le_of_le (e₁ := 2) Nat.prime_two (show a ≤ 2 by omega)
  have b2 := sigma_le_limit Nat.prime_five b
  have b3 := sigma_le_limit hp11 c
  refine absurd h (prod3_lt b1 b2 b3 (by positivity) ?_).ne
  rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_two]
  norm_num [Finset.sum_range_succ]

/-- No solution `2^3 7^b 11^c`, `b, c ≥ 2`, by monotone ratio bounds (1 leaf). -/
theorem box_2_7_11 {a b c : ℕ} (ha₀ : 3 ≤ a) (_ha₁ : a ≤ 3) (hb₀ : 2 ≤ b) (hc₀ : 2 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (7 ^ b) * σ 1 (11 ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 7 ^ b) * (1 + 11 ^ c))) : False := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have b1 := sigma_ge_of_le (e₀ := 3) Nat.prime_two (show 3 ≤ a by omega)
  have b2 := sigma_ge_of_le (e₀ := 2) hp7 (show 2 ≤ b by omega)
  have b3 := sigma_ge_of_le (e₀ := 2) hp11 (show 2 ≤ c by omega)
  refine absurd h (prod3_gt b1 b2 b3 (by positivity) ?_).ne'
  rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_two]
  rw [sigma_one_apply_prime_pow (i := 2) hp7]
  rw [sigma_one_apply_prime_pow (i := 2) hp11]
  norm_num [Finset.sum_range_succ]


/-! ### 2-adic valuations (Case A) -/

/-- Pairing the terms of a geometric sum: `∑_{i<2m} x^i = (1 + x) ∑_{j<m} (x^2)^j`. -/
theorem geom_sum_pair (x m : ℕ) :
    ∑ i ∈ range (2 * m), x ^ i = (1 + x) * ∑ j ∈ range m, (x ^ 2) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- A geometric sum with odd ratio has the parity of its number of terms. -/
theorem geom_sum_mod_two {x : ℕ} (hx : x % 2 = 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hx, one_pow]
    omega

/-- `padicValNat 2 (2 * t) = 1` for odd `t`. -/
theorem padicValNat_two_mul_odd {t : ℕ} (ht : t % 2 = 1) : padicValNat 2 (2 * t) = 1 := by
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]

/-- `v₂(∑_{j<m} y^j) = v₂(m)` for `y ≡ 1 (mod 4)`. -/
theorem padicValNat_geom_sum {y : ℕ} (hy : y % 4 = 1) (m : ℕ) :
    padicValNat 2 (∑ j ∈ range m, y ^ j) = padicValNat 2 m := by
  induction m using Nat.strong_induction_on generalizing y with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨m', rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m' with rfl | hpos
      · simp
      · have hy2 : (y ^ 2) % 4 = 1 := by rw [Nat.pow_mod, hy]
        have hS : ∑ j ∈ range m', (y ^ 2) ^ j ≠ 0 := by
          have := Finset.single_le_sum (f := fun j => (y ^ 2) ^ j) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.2 hpos)
          simp at this
          omega
        rw [geom_sum_pair, padicValNat.mul (by omega) hS, ih m' (by omega) hy2,
          padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
        have h1y : 1 + y = 2 * ((1 + y) / 2) := by omega
        rw [h1y, padicValNat_two_mul_odd (by omega)]
    · have hodd := geom_sum_mod_two (x := y) (by omega) (2 * m' + 1)
      rw [padicValNat.eq_zero_of_not_dvd (by omega), padicValNat.eq_zero_of_not_dvd (by omega)]

/-- For odd exponents, `σ(p^(2m+1)) = (1 + p) ∑_{j ≤ m} (p^2)^j`. -/
theorem sigma_prime_pow_odd {p : ℕ} (hp : p.Prime) (m : ℕ) :
    σ 1 (p ^ (2 * m + 1)) = (1 + p) * ∑ j ∈ range (m + 1), (p ^ 2) ^ j := by
  rw [sigma_one_apply_prime_pow hp, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, geom_sum_pair]

/-- For odd exponents, `1 + p^(2m+1) = (1 + p)(1 + p(p-1) ∑_{j<m} (p^2)^j)`. -/
theorem one_add_pow_odd {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    1 + p ^ (2 * m + 1) = (1 + p) * (1 + p * (p - 1) * ∑ j ∈ range m, (p ^ 2) ^ j) := by
  have hg := geom_sum_mul ((p : ℤ) ^ 2) m
  have h' : ((1 + p ^ (2 * m + 1) : ℕ) : ℤ)
      = (((1 + p) * (1 + p * (p - 1) * ∑ j ∈ range m, (p ^ 2) ^ j) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hp]
    rw [pow_succ, pow_mul]
    linear_combination (-(p : ℤ)) * hg
  exact_mod_cast h'

/-- `v₂(σ(p^e)) = 0` for odd `p` and even `e`. -/
theorem padicValNat_sigma_even {p e : ℕ} (hp : p.Prime) (hpo : p % 2 = 1) (he : e % 2 = 0) :
    padicValNat 2 (σ 1 (p ^ e)) = 0 := by
  rw [sigma_one_apply_prime_pow hp]
  have := geom_sum_mod_two hpo (e + 1)
  exact padicValNat.eq_zero_of_not_dvd (by omega)

/-- `v₂(1 + p^e) = 1` for odd `p` and even `e`. -/
theorem padicValNat_one_add_pow_even {p e : ℕ} (hpo : p % 2 = 1) (he : e % 2 = 0) :
    padicValNat 2 (1 + p ^ e) = 1 := by
  have h4 : p ^ e % 4 = 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, e = 2 * n := ⟨e / 2, by omega⟩
    have hp2 : p ^ 2 % 4 = 1 := by
      have : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    rw [pow_mul, Nat.pow_mod, hp2, one_pow]
    norm_num
  rw [show 1 + p ^ e = 2 * ((1 + p ^ e) / 2) by omega, padicValNat_two_mul_odd (by omega)]

/-- `v₂(σ(p^(2m+1))) = v₂(1 + p) + v₂(m + 1)` for odd `p`. -/
theorem padicValNat_sigma_odd {p : ℕ} (hp : p.Prime) (hpo : p % 2 = 1) (m : ℕ) :
    padicValNat 2 (σ 1 (p ^ (2 * m + 1))) = padicValNat 2 (1 + p) + padicValNat 2 (m + 1) := by
  have hp2 : (p ^ 2) % 4 = 1 := by
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have hS : ∑ j ∈ range (m + 1), (p ^ 2) ^ j ≠ 0 := by
    rw [Finset.sum_range_succ']; simp
  rw [sigma_prime_pow_odd hp, padicValNat.mul (by omega) hS, padicValNat_geom_sum hp2]

/-- `v₂(1 + p^(2m+1)) = v₂(1 + p)` for odd `p`. -/
theorem padicValNat_one_add_pow_odd {p : ℕ} (hpo : p % 2 = 1) (m : ℕ) :
    padicValNat 2 (1 + p ^ (2 * m + 1)) = padicValNat 2 (1 + p) := by
  have hev : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
  rw [one_add_pow_odd (by omega), padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (n := 1 + p * (p - 1) * _) ?_, add_zero]
  intro h2
  have : 2 ∣ p * (p - 1) * ∑ j ∈ range m, (p ^ 2) ^ j := Dvd.dvd.mul_right hev _
  omega

/-- `σ(2^a) + 1 = 2^(a+1)`. -/
theorem sigma_two_pow_add_one (a : ℕ) : σ 1 (2 ^ a) + 1 = 2 * 2 ^ a := by
  have k := sigma_prime_pow_key Nat.prime_two a
  push_cast at k
  have : ((σ 1 (2 ^ a) + 1 : ℕ) : ℤ) = ((2 * 2 ^ a : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this

/-- `2^k ∣ n` and `2^(k+1) ∤ n` when `v₂(n) = k`, `n ≠ 0`. -/
theorem dvd_of_padicValNat_two {n k : ℕ} (hn : n ≠ 0) (h : padicValNat 2 n = k) :
    2 ^ k ∣ n ∧ ¬ 2 ^ (k + 1) ∣ n := by
  subst h
  exact ⟨pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd hn⟩

/-- The 2-adic valuations of `σ(p^e)` and `1 + p^e` for an odd prime `p`. -/
theorem v2_cases {p e : ℕ} (hp : p.Prime) (hpo : p % 2 = 1) :
    (e % 2 = 0 ∧ padicValNat 2 (σ 1 (p ^ e)) = 0 ∧ padicValNat 2 (1 + p ^ e) = 1) ∨
    (∃ m, e = 2 * m + 1 ∧
      padicValNat 2 (σ 1 (p ^ e)) = padicValNat 2 (1 + p) + padicValNat 2 (m + 1) ∧
      padicValNat 2 (1 + p ^ e) = padicValNat 2 (1 + p)) := by
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · left
    exact ⟨by omega, padicValNat_sigma_even hp hpo (by omega),
      padicValNat_one_add_pow_even hpo (by omega)⟩
  · right
    exact ⟨m, rfl, padicValNat_sigma_odd hp hpo m, padicValNat_one_add_pow_odd hpo m⟩

/-- Comparing 2-adic valuations in `σ(2^a) σ(q^b) σ(r^c) = 2 (1+2^a)(1+q^b)(1+r^c)`. -/
theorem two_adic_rel {a b c q r : ℕ} (ha : 1 ≤ a) (hq : q.Prime) (hr : r.Prime)
    (h : σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c))) :
    padicValNat 2 (σ 1 (q ^ b)) + padicValNat 2 (σ 1 (r ^ c)) =
      1 + padicValNat 2 (1 + q ^ b) + padicValNat 2 (1 + r ^ c) := by
  have h2 := sigma_two_pow_add_one a
  have hs2 : padicValNat 2 (σ 1 (2 ^ a)) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hu2 : padicValNat 2 (1 + 2 ^ a) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [pow_succ]
    omega
  have s2 : σ 1 (2 ^ a) ≠ 0 := by omega
  have sq : σ 1 (q ^ b) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have sr : σ 1 (r ^ c) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hr.ne_zero)).ne'
  have u2 : 1 + 2 ^ a ≠ 0 := by omega
  have uq : 1 + q ^ b ≠ 0 := by omega
  have ur : 1 + r ^ c ≠ 0 := by omega
  have e1 : padicValNat 2 (σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c)) =
      padicValNat 2 (σ 1 (2 ^ a)) + padicValNat 2 (σ 1 (q ^ b)) + padicValNat 2 (σ 1 (r ^ c)) := by
    rw [padicValNat.mul (mul_ne_zero s2 sq) sr, padicValNat.mul s2 sq]
  have e2 : padicValNat 2 (2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c))) =
      1 + (padicValNat 2 (1 + 2 ^ a) + padicValNat 2 (1 + q ^ b) + padicValNat 2 (1 + r ^ c)) := by
    rw [padicValNat.mul (by norm_num) (mul_ne_zero (mul_ne_zero u2 uq) ur),
      padicValNat.mul (mul_ne_zero u2 uq) ur, padicValNat.mul u2 uq,
      padicValNat.self (by norm_num)]
  have hv := congrArg (padicValNat 2) h
  rw [e1, e2] at hv
  omega

/-- The exponent constraints forced by `two_adic_rel`. -/
theorem caseA_two_adic {b c q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqo : q % 2 = 1)
    (hro : r % 2 = 1) (hb : 2 ≤ b)
    (hv : padicValNat 2 (σ 1 (q ^ b)) + padicValNat 2 (σ 1 (r ^ c)) =
      1 + padicValNat 2 (1 + q ^ b) + padicValNat 2 (1 + r ^ c)) :
    (c % 2 = 0 → 7 ≤ b) ∧ (c = 3 → b = 5 ∨ 9 ≤ b) ∧ (c = 5 → b = 3 ∨ 11 ≤ b) := by
  have h22 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have h23 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rcases v2_cases (e := b) hq hqo with ⟨hbe, hb1, hb2⟩ | ⟨m, rfl, hb1, hb2⟩ <;>
    rcases v2_cases (e := c) hr hro with ⟨hce, hc1, hc2⟩ | ⟨n, rfl, hc1, hc2⟩ <;>
    rw [hb1, hc1, hb2, hc2] at hv
  · omega
  · refine ⟨fun h => by omega, fun h => ?_, fun h => ?_⟩
    · obtain rfl : n = 1 := by omega
      have : padicValNat 2 (1 + 1) = 1 := h22
      omega
    · obtain rfl : n = 2 := by omega
      have : padicValNat 2 (2 + 1) = 0 := h23
      omega
  · have hm : padicValNat 2 (m + 1) = 2 := by omega
    obtain ⟨h4, -⟩ := dvd_of_padicValNat_two (by omega) hm
    norm_num at h4
    refine ⟨fun _ => by omega, fun h => by omega, fun h => by omega⟩
  · refine ⟨fun h => by omega, fun h => ?_, fun h => ?_⟩
    · obtain rfl : n = 1 := by omega
      have : padicValNat 2 (1 + 1) = 1 := h22
      have hm : padicValNat 2 (m + 1) = 0 := by omega
      obtain ⟨-, h2⟩ := dvd_of_padicValNat_two (by omega) hm
      norm_num at h2
      omega
    · obtain rfl : n = 2 := by omega
      have : padicValNat 2 (2 + 1) = 0 := h23
      have hm : padicValNat 2 (m + 1) = 1 := by omega
      obtain ⟨h2, h4⟩ := dvd_of_padicValNat_two (by omega) hm
      norm_num at h2 h4
      omega

/-! ### Case A in integer form

Throughout, `K = 2^(a+1) - 1`, `5 ≤ q < r` are odd primes, `t_q = q + ⋯ + q^(b-1)`,
`t_r = r + ⋯ + r^(c-1)`, `δ_p = 3p - 3 - K`, `W_p = 3(p+1) + δ_p t_p`, and the equation is
`W_q W_r = K(K+3) t_q t_r`. -/

section CaseA

variable {K q r tq tr Wq Wr : ℤ}

/-- Both `W_q` and `W_r` are positive. -/
theorem caseA_pos (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ≤ tq) (htr : r ≤ tr)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * tr) (heq : Wq * Wr = K * (K + 3) * tq * tr) :
    0 < Wq ∧ 0 < Wr := by
  have htq0 : 0 < tq := by linarith
  have htr0 : 0 < tr := by linarith
  have hP : 0 < Wq * Wr := by rw [heq]; positivity
  have h1 : -(K * tq) < Wq := by
    have : 0 ≤ (q - 1) * tq := mul_nonneg (by linarith) htq0.le
    rw [hWq]; nlinarith
  have h2 : -(K * tr) < Wr := by
    have : 0 ≤ (r - 1) * tr := mul_nonneg (by linarith) htr0.le
    rw [hWr]; nlinarith
  have hKK : K * tq * (K * tr) ≤ K * (K + 3) * tq * tr := by
    have : 0 ≤ 3 * K * (tq * tr) := by positivity
    nlinarith
  rcases lt_or_ge 0 Wq with hq0 | hq0
  · exact ⟨hq0, pos_of_mul_pos_right hP hq0.le⟩
  · exfalso
    have hr0 : Wr < 0 := by
      by_contra hc
      push Not at hc
      have : Wq * Wr ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq0 hc
      linarith
    have h3 : (-Wq) * (-Wr) < (K * tq) * (K * tr) :=
      mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
    have : (-Wq) * (-Wr) = Wq * Wr := by ring
    linarith

/-- `K ≤ 3q`. -/
theorem caseA_K_le (hq : 5 ≤ q) (htq : q ≤ tq) (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hW : 0 < Wq) : K ≤ 3 * q := by
  by_contra hc
  push Not at hc
  have : (3 * q - 3 - K + 4) * tq ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  nlinarith

/-- If `b ≥ 3` (`t_q ≥ q + q²`) then `δ_q ≥ 1`, i.e. `K ≤ 3q - 4`. -/
theorem caseA_K_le' (hq : 5 ≤ q) (htq : q + q ^ 2 ≤ tq) (hKo : K % 2 = 1) (hqo : q % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq) (hW : 0 < Wq) : K ≤ 3 * q - 4 := by
  have h0 : K ≤ 3 * q - 3 := by
    by_contra hc
    push Not at hc
    have : (3 * q - 3 - K + 1) * tq ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
    nlinarith
  omega

/-- The range of `q`: `3q ≤ 2K + 4` (from `W_q/t_q < W_r/t_r` and their product `K(K+3)`). -/
theorem caseA_range (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ≤ tq) (htr : r ≤ tr)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * tr) (heq : Wq * Wr = K * (K + 3) * tq * tr)
    (hW : 0 < Wq) : 3 * q ≤ 2 * K + 4 := by
  have htq0 : 0 < tq := by linarith
  have htr0 : 0 < tr := by linarith
  have hXY : Wq * tr < Wr * tq := by
    rw [hWq, hWr]
    have h1 : 0 ≤ (r - q - 2) * tq * tr := by
      have := mul_nonneg (show (0 : ℤ) ≤ r - q - 2 by linarith) htq0.le
      exact mul_nonneg this htr0.le
    have h2 : 0 ≤ (tq - q) * tr := mul_nonneg (by linarith) htr0.le
    nlinarith
  have h3 : Wq * Wq * tr < K * (K + 3) * tq * tq * tr := by
    have := mul_lt_mul_of_pos_left hXY hW
    nlinarith
  have h4 : Wq * Wq < K * (K + 3) * tq * tq := by
    by_contra hc
    push Not at hc
    nlinarith
  have h5 : Wq < (K + 2) * tq := by
    by_contra hc
    push Not at hc
    have : (K + 2) * tq * ((K + 2) * tq) ≤ Wq * Wq := mul_le_mul hc hc (by nlinarith) hW.le
    have h8 : 0 < (K + 4) * (tq * tq) := mul_pos (by linarith) (mul_pos htq0 htq0)
    nlinarith [h8, this, h4]
  have h6 : (3 * q - 3 - K) * tq < (K + 2) * tq := by rw [hWq] at h5; linarith
  have h7 : 3 * q - 3 - K < K + 2 := lt_of_mul_lt_mul_right h6 htq0.le
  linarith

/-- The identities for `Ω = K(K+3) - δ_q δ_r`, its positivity and its parity. -/
theorem caseA_Om {Om : ℤ} (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ≤ tq)
    (htr : r ≤ tr) (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * tr) (heq : Wq * Wr = K * (K + 3) * tq * tr)
    (hOm : Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K)) (hW : 0 < Wq) (hKq : K ≤ 3 * q) :
    Om * tq * tr = 3 * (q + 1) * Wr + 3 * (r + 1) * (3 * q - 3 - K) * tq ∧
    Om * tq * tr = 3 * (r + 1) * Wq + 3 * (q + 1) * (3 * r - 3 - K) * tr ∧
    1 ≤ Om ∧ Om % 2 = 1 := by
  have I1 : Om * tq * tr = 3 * (q + 1) * Wr + 3 * (r + 1) * (3 * q - 3 - K) * tq := by
    rw [hOm]; rw [hWq, hWr] at heq; rw [hWr]; linear_combination -heq
  have I2 : Om * tq * tr = 3 * (r + 1) * Wq + 3 * (q + 1) * (3 * r - 3 - K) * tr := by
    rw [hOm]; rw [hWq, hWr] at heq; rw [hWq]; linear_combination -heq
  have htq0 : 0 < tq := by linarith
  have htr0 : 0 < tr := by linarith
  refine ⟨I1, I2, ?_, ?_⟩
  · have hdr : 0 < 3 * r - 3 - K := by linarith
    have hpos : 0 < Om * (tq * tr) := by
      have h1 : 0 < 3 * (r + 1) * Wq := mul_pos (by linarith) hW
      have h2 : 0 < 3 * (q + 1) * (3 * r - 3 - K) * tr :=
        mul_pos (mul_pos (by linarith) hdr) htr0
      rw [← mul_assoc]; linarith
    have := pos_of_mul_pos_left hpos (mul_pos htq0 htr0).le
    linarith
  · obtain ⟨κ, rfl⟩ : ∃ κ, K = 2 * κ + 1 := ⟨K / 2, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i, q = 2 * i + 1 := ⟨q / 2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
    have : Om = 2 * (3 * κ + 1 - 18 * i * j + 6 * i * κ + 6 * j * κ + 3 * i + 3 * j) + 1 := by
      rw [hOm]; ring
    omega

/-- `t_q ≤ 3(q+1) W_r` (from `H t_q = 3(q+1) W_r` with `H = K(K+3) t_r - δ_q W_r ≥ 1`). -/
theorem caseA_H (hq : 5 ≤ q) (htq : q ≤ tq)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq) (heq : Wq * Wr = K * (K + 3) * tq * tr)
    (hW : 0 < Wr) : tq ≤ 3 * (q + 1) * Wr := by
  have htq0 : 0 < tq := by linarith
  have hH : (K * (K + 3) * tr - (3 * q - 3 - K) * Wr) * tq = 3 * (q + 1) * Wr := by
    rw [hWq] at heq; linear_combination -heq
  have hHpos : 0 < K * (K + 3) * tr - (3 * q - 3 - K) * Wr := by
    have : 0 < 3 * (q + 1) * Wr := mul_pos (by linarith) hW
    rw [← hH] at this
    exact pos_of_mul_pos_left this htq0.le
  nlinarith

/-- `δ_q W_r < K(K+3) t_r` (because `W_q > δ_q t_q`). -/
theorem caseA_dWr (hq : 5 ≤ q) (htq : q ≤ tq) (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (heq : Wq * Wr = K * (K + 3) * tq * tr) (hW : 0 < Wr) :
    (3 * q - 3 - K) * Wr < K * (K + 3) * tr := by
  have htq0 : 0 < tq := by linarith
  have h1 : (3 * q - 3 - K) * tq * Wr < Wq * Wr := by
    have : (3 * q - 3 - K) * tq < Wq := by rw [hWq]; linarith
    exact mul_lt_mul_of_pos_right this hW
  rw [heq] at h1
  have h2 : tq * ((3 * q - 3 - K) * Wr) < tq * (K * (K + 3) * tr) := by linarith
  exact lt_of_mul_lt_mul_left h2 htq0.le

/-- `c r^k ≤ r^(k+1)` for `0 ≤ c ≤ r`. -/
theorem le_pow_succ_of_le {r c : ℤ} (hc : 0 ≤ c) (h : c ≤ r) (k : ℕ) : c * r ^ k ≤ r ^ (k + 1) := by
  rw [pow_succ]
  have : 0 ≤ r ^ k := pow_nonneg (hc.trans h) k
  nlinarith

/-- Case `c ≥ 7` (`t_r ≥ r^6`): then `r ≤ 9`. -/
theorem caseA_c7 (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ≤ tq) (htr : r ≤ tr)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * tr) (heq : Wq * Wr = K * (K + 3) * tq * tr)
    (htr6 : r ^ 6 ≤ tr) : r ≤ 9 := by
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq htr hWq hWr heq
  have hKq := caseA_K_le hq htq hWq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨I1, -, hOm, -⟩ :=
    caseA_Om hK hq hqr htq htr hKo hqo hro hWq hWr heq hOmd hWq0 hKq
  have htq0 : 0 < tq := by linarith
  have htr0 : 0 < tr := by linarith
  obtain ⟨H, hH⟩ : ∃ H, H = K * (K + 3) * tr - (3 * q - 3 - K) * Wr := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = K * (K + 3) * tq - (3 * r - 3 - K) * Wq := ⟨_, rfl⟩
  have eH : H * tq = 3 * (q + 1) * Wr := by linear_combination -heq + Wr * hWq + tq * hH
  have eG : G * tr = 3 * (r + 1) * Wq := by linear_combination -heq + Wq * hWr + tr * hG
  have hHpos : 0 < H := by
    have : 0 < H * tq := by rw [eH]; exact mul_pos (by linarith) hWr0
    exact pos_of_mul_pos_left this htq0.le
  have hGpos : 0 < G := by
    have : 0 < G * tr := by rw [eG]; exact mul_pos (by linarith) hWq0
    exact pos_of_mul_pos_left this htr0.le
  have hHG : H * G = 9 * (q + 1) * (r + 1) * (K * (K + 3)) := by
    have h0 : (H * G - 9 * (q + 1) * (r + 1) * (K * (K + 3))) * (tq * tr) = 0 := by
      linear_combination (G * tr) * eH + (3 * (q + 1) * Wr) * eG
        + (9 * (q + 1) * (r + 1)) * heq
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact absurd h (mul_pos htq0 htr0).ne'
  have hHle : H ≤ 9 * (q + 1) * (r + 1) * (K * (K + 3)) := by
    rw [← hHG]
    have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ G by linarith) hHpos.le
    linarith
  have eOm : Om * tr = H + 3 * (r + 1) * (3 * q - 3 - K) := by
    have h0 : (Om * tr - H - 3 * (r + 1) * (3 * q - 3 - K)) * tq = 0 := by
      linear_combination I1 - eH
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact absurd h htq0.ne'
  have htrle : tr ≤ H + 3 * (r + 1) * (3 * q - 3 - K) := by
    rw [← eOm]
    have := mul_le_mul_of_nonneg_right hOm htr0.le
    linarith
  by_contra hr9
  push Not at hr9
  have hKK : K * (K + 3) ≤ 3 * q * (3 * q + 3) :=
    mul_le_mul hKq (by linarith) (by linarith) (by linarith)
  have hqr0 : 0 ≤ 9 * (q + 1) * (r + 1) := by
    have := mul_pos (show (0 : ℤ) < q + 1 by linarith) (show (0 : ℤ) < r + 1 by linarith)
    linarith
  have h1 : 9 * (q + 1) * (r + 1) * (K * (K + 3))
      ≤ 9 * (q + 1) * (r + 1) * (3 * q * (3 * q + 3)) := mul_le_mul_of_nonneg_left hKK hqr0
  have hq3 : q * (q + 1) * (q + 1) ≤ r * r * r := by
    have a1 : q * (q + 1) ≤ r * r :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    exact mul_le_mul a1 (by linarith) (by linarith) (mul_self_nonneg r)
  have h2 : 81 * (q * (q + 1) * (q + 1)) * (r + 1) ≤ 81 * (r * r * r) * (r + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : 3 * (r + 1) * (3 * q - 3 - K) ≤ 3 * (r + 1) * (3 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have p1 := le_pow_succ_of_le (r := r) (c := 10) (by norm_num) (by linarith) 1
  have p2 := le_pow_succ_of_le (r := r) (c := 10) (by norm_num) (by linarith) 2
  have p3 := le_pow_succ_of_le (r := r) (c := 10) (by norm_num) (by linarith) 3
  have p4 := le_pow_succ_of_le (r := r) (c := 10) (by norm_num) (by linarith) 4
  have p5 := le_pow_succ_of_le (r := r) (c := 10) (by norm_num) (by linarith) 5
  norm_num at p1 p2 p3 p4 p5
  linarith

/-- `K(K+3) < 9 q²` when `7 ≤ K ≤ 3q - 4`. -/
theorem caseA_KK (hK : 7 ≤ K) (hKq : K ≤ 3 * q - 4) : K * (K + 3) < 9 * q ^ 2 := by
  have a1 : 0 ≤ (3 * q - 4 - K) * (3 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have a2 : 0 ≤ K * (3 * q - 4 - K) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Case `t_q ≥ q^6`: `74 t_r < 900 r (r+1)`. -/
theorem caseA_c46 (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ^ 6 ≤ tq) (htr : r ≤ tr)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * tr) (heq : Wq * Wr = K * (K + 3) * tq * tr) :
    74 * tr < 900 * r * (r + 1) := by
  have q1 := le_pow_succ_of_le (c := 5) (by norm_num) hq 1
  have q2 := le_pow_succ_of_le (c := 5) (by norm_num) hq 2
  have q3 := le_pow_succ_of_le (c := 5) (by norm_num) hq 3
  have q4 := le_pow_succ_of_le (c := 5) (by norm_num) hq 4
  have q5 := le_pow_succ_of_le (c := 5) (by norm_num) hq 5
  norm_num at q1 q2 q3 q4 q5
  have htq1 : q ≤ tq := by linarith
  have htq2 : q + q ^ 2 ≤ tq := by linarith
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq1 htr hWq hWr heq
  have hKq := caseA_K_le' hq htq2 hKo hqo hWq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨I1, -, hOm, -⟩ :=
    caseA_Om hK hq hqr htq1 htr hKo hqo hro hWq hWr heq hOmd hWq0 (by linarith)
  have htq0 : 0 < tq := by linarith
  have htr0 : 0 < tr := by linarith
  have hdW := caseA_dWr hq htq1 hWq heq hWr0
  have hKK := caseA_KK hK hKq
  have hA : tq * tr ≤ 3 * (q + 1) * Wr + 3 * (r + 1) * (3 * q - 3 - K) * tq := by
    have := mul_le_mul_of_nonneg_right hOm (mul_pos htq0 htr0).le
    linarith
  have hX : 3 * (q + 1) * Wr < 27 * (q + 1) * q ^ 2 * tr := by
    have a1 : Wr < 9 * q ^ 2 * tr := by
      have : K * (K + 3) * tr < 9 * q ^ 2 * tr := mul_lt_mul_of_pos_right hKK htr0
      have : Wr ≤ (3 * q - 3 - K) * Wr := le_mul_of_one_le_left hWr0.le (by linarith)
      linarith
    have := mul_lt_mul_of_pos_left a1 (show (0 : ℤ) < 3 * (q + 1) by linarith)
    linarith
  have h26 : 2700 * (q + 1) * q ^ 2 ≤ 26 * tq := by linarith
  have h74 : 74 * tr < 300 * (r + 1) * (3 * q - 3 - K) := by
    have a1 := mul_le_mul_of_nonneg_right h26 htr0.le
    have a2 : 74 * tr * tq < 300 * (r + 1) * (3 * q - 3 - K) * tq := by linarith
    exact lt_of_mul_lt_mul_right a2 htq0.le
  have : 300 * (r + 1) * (3 * q - 3 - K) ≤ 300 * (r + 1) * (3 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- Case `c = 2` (`t_r = r`) with `t_q ≥ q^6`: impossible. -/
theorem caseA_c2 (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ^ 6 ≤ tq)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * r) (heq : Wq * Wr = K * (K + 3) * tq * r) :
    False := by
  have q1 := le_pow_succ_of_le (c := 5) (by norm_num) hq 1
  have q2 := le_pow_succ_of_le (c := 5) (by norm_num) hq 2
  have q3 := le_pow_succ_of_le (c := 5) (by norm_num) hq 3
  have q4 := le_pow_succ_of_le (c := 5) (by norm_num) hq 4
  have q5 := le_pow_succ_of_le (c := 5) (by norm_num) hq 5
  norm_num at q1 q2 q3 q4 q5
  have htq1 : q ≤ tq := by linarith
  have htq2 : q + q ^ 2 ≤ tq := by linarith
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq1 le_rfl hWq hWr heq
  have hKq := caseA_K_le' hq htq2 hKo hqo hWq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨I1, -, hOm, hOmo⟩ :=
    caseA_Om hK hq hqr htq1 le_rfl hKo hqo hro hWq hWr heq hOmd hWq0 (by linarith)
  have htq0 : 0 < tq := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = Om - 3 * (3 * q - 3 - K) := ⟨_, rfl⟩
  have eJ : J * tq * r = 3 * (q + 1) * Wr + 3 * (3 * q - 3 - K) * tq := by
    rw [hJ]; linear_combination I1
  have hJpos : 0 < J := by
    have : 0 < J * (tq * r) := by
      rw [← mul_assoc, eJ]
      have := mul_pos (show (0 : ℤ) < 3 * (q + 1) by linarith) hWr0
      have := mul_pos (show (0 : ℤ) < 3 * (3 * q - 3 - K) by linarith) htq0
      linarith
    exact pos_of_mul_pos_left this (mul_pos htq0 hr0).le
  have hJ2 : 2 ≤ J := by omega
  have hA : 2 * (tq * r) ≤ 3 * (q + 1) * Wr + 3 * (3 * q - 3 - K) * tq := by
    have := mul_le_mul_of_nonneg_right hJ2 (mul_pos htq0 hr0).le
    linarith
  have hdW := caseA_dWr hq htq1 hWq heq hWr0
  have hKK := caseA_KK hK hKq
  have hX : 3 * (q + 1) * Wr < 27 * (q + 1) * q ^ 2 * r := by
    have a1 : Wr < 9 * q ^ 2 * r := by
      have : K * (K + 3) * r < 9 * q ^ 2 * r := mul_lt_mul_of_pos_right hKK hr0
      have : Wr ≤ (3 * q - 3 - K) * Wr := le_mul_of_one_le_left hWr0.le (by linarith)
      linarith
    have := mul_lt_mul_of_pos_left a1 (show (0 : ℤ) < 3 * (q + 1) by linarith)
    linarith
  have h26 : 2700 * (q + 1) * q ^ 2 ≤ 26 * tq := by linarith
  have h174 : 174 * r < 300 * (3 * q - 3 - K) := by
    have a1 := mul_le_mul_of_nonneg_right h26 hr0.le
    have a2 : 174 * r * tq < 300 * (3 * q - 3 - K) * tq := by linarith
    exact lt_of_mul_lt_mul_right a2 htq0.le
  have hH := caseA_H hq htq1 hWq heq hWr0
  have h5 : (3 * q - 3 - K) * tq < 3 * (q + 1) * (K * (K + 3)) * r := by
    have a1 := mul_le_mul_of_nonneg_left hH (show (0 : ℤ) ≤ 3 * q - 3 - K by linarith)
    have a2 := mul_lt_mul_of_pos_left hdW (show (0 : ℤ) < 3 * (q + 1) by linarith)
    linarith
  have hM0 : 0 < 3 * (q + 1) * (K * (K + 3)) :=
    mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
  have h6 : 174 * tq < 900 * (q + 1) * (K * (K + 3)) := by
    have a1 := mul_lt_mul_of_pos_left h174 hM0
    have a2 : (3 * q - 3 - K) * (174 * tq)
        < (3 * q - 3 - K) * (900 * (q + 1) * (K * (K + 3))) := by linarith
    exact lt_of_mul_lt_mul_left a2 (by linarith)
  have h7 : 900 * (q + 1) * (K * (K + 3)) ≤ 8100 * (q + 1) * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hKK.le (show (0 : ℤ) ≤ 900 * (q + 1) by linarith)
    linarith
  linarith

/-- Case `b = 3`, `c = 5`: impossible. -/
theorem caseA_c5b (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * (q + q ^ 2))
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * (r + r ^ 2 + r ^ 3 + r ^ 4))
    (heq : Wq * Wr = K * (K + 3) * (q + q ^ 2) * (r + r ^ 2 + r ^ 3 + r ^ 4)) : False := by
  have r1 := le_pow_succ_of_le (r := r) (c := 7) (by norm_num) (by linarith) 1
  have r2 := le_pow_succ_of_le (r := r) (c := 7) (by norm_num) (by linarith) 2
  have r3 := le_pow_succ_of_le (r := r) (c := 7) (by norm_num) (by linarith) 3
  norm_num at r1 r2 r3
  have htq1 : q ≤ q + q ^ 2 := by have := sq_nonneg q; linarith
  have htr1 : r ≤ r + r ^ 2 + r ^ 3 + r ^ 4 := by linarith
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq1 htr1 hWq hWr heq
  have hKq := caseA_K_le' hq le_rfl hKo hqo hWq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨-, I2, hOm, hOmo⟩ :=
    caseA_Om hK hq hqr htq1 htr1 hKo hqo hro hWq hWr heq hOmd hWq0 (by linarith)
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = q * Om - 3 * (3 * r - 3 - K) := ⟨_, rfl⟩
  have eM0 : (q + 1) * (M * (r + r ^ 2 + r ^ 3 + r ^ 4)
      - 3 * (r + 1) * (3 + q * (3 * q - 3 - K))) = 0 := by
    rw [hM]; linear_combination I2 + 3 * (r + 1) * hWq
  have eM : M * (r + r ^ 2 + r ^ 3 + r ^ 4) = 3 * (r + 1) * (3 + q * (3 * q - 3 - K)) := by
    rcases mul_eq_zero.1 eM0 with h | h
    · linarith
    · linarith
  have hMe : M % 2 = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, q = 2 * i + 1 := ⟨q / 2, by omega⟩
    obtain ⟨w, hw⟩ : ∃ w, Om = 2 * w + 1 := ⟨Om / 2, by omega⟩
    have : q * Om = 2 * (2 * i * w + i + w) + 1 := by rw [hi, hw]; ring
    omega
  have hT0 : 0 < r + r ^ 2 + r ^ 3 + r ^ 4 := by linarith
  have hqd : 0 < q * (3 * q - 3 - K) := mul_pos (by linarith) (by linarith)
  have hMpos : 0 < M := by
    have : 0 < M * (r + r ^ 2 + r ^ 3 + r ^ 4) := by
      rw [eM]; exact mul_pos (by linarith) (by linarith)
    exact pos_of_mul_pos_left this hT0.le
  have hM2 : 2 ≤ M := by omega
  have h1 : 2 * (r + r ^ 2 + r ^ 3 + r ^ 4) ≤ 3 * (r + 1) * (3 + q * (3 * q - 3 - K)) := by
    rw [← eM]; exact mul_le_mul_of_nonneg_right hM2 hT0.le
  have h2 : q * (3 * q - 3 - K) < r * (3 * r) :=
    mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : (r + 1) * (2 * (r + r ^ 3)) ≤ (r + 1) * (3 * (3 + q * (3 * q - 3 - K))) := by
    linarith
  have h4 := le_of_mul_le_mul_left h3 (by linarith : (0 : ℤ) < r + 1)
  linarith

/-- Case `c = 3` (`t_r = r + r²`) with `t_q ≥ q^8`: impossible. -/
theorem caseA_c3a (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (htq : q ^ 8 ≤ tq)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * tq)
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * (r + r ^ 2))
    (heq : Wq * Wr = K * (K + 3) * tq * (r + r ^ 2)) : False := by
  have q1 := le_pow_succ_of_le (c := 5) (by norm_num) hq 1
  have q2 := le_pow_succ_of_le (c := 5) (by norm_num) hq 2
  have q3 := le_pow_succ_of_le (c := 5) (by norm_num) hq 3
  have q4 := le_pow_succ_of_le (c := 5) (by norm_num) hq 4
  have q5 := le_pow_succ_of_le (c := 5) (by norm_num) hq 5
  have q6 := le_pow_succ_of_le (c := 5) (by norm_num) hq 6
  have q7 := le_pow_succ_of_le (c := 5) (by norm_num) hq 7
  norm_num at q1 q2 q3 q4 q5 q6 q7
  have htq1 : q ≤ tq := by linarith
  have htq2 : q + q ^ 2 ≤ tq := by linarith
  have htr1 : r ≤ r + r ^ 2 := by have := sq_nonneg r; linarith
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq1 htr1 hWq hWr heq
  have hKq := caseA_K_le' hq htq2 hKo hqo hWq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨I1, -, hOm, hOmo⟩ :=
    caseA_Om hK hq hqr htq1 htr1 hKo hqo hro hWq hWr heq hOmd hWq0 (by linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = r * Om - 3 * (3 * q - 3 - K) := ⟨_, rfl⟩
  have eL0 : (r + 1) * (L * tq - 3 * (q + 1) * (3 + r * (3 * r - 3 - K))) = 0 := by
    rw [hL]; linear_combination I1 + 3 * (q + 1) * hWr
  have eL : L * tq = 3 * (q + 1) * (3 + r * (3 * r - 3 - K)) := by
    rcases mul_eq_zero.1 eL0 with h | h
    · linarith
    · linarith
  have hLe : L % 2 = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
    obtain ⟨w, hw⟩ : ∃ w, Om = 2 * w + 1 := ⟨Om / 2, by omega⟩
    have : r * Om = 2 * (2 * j * w + j + w) + 1 := by rw [hj, hw]; ring
    omega
  have hE0 : 0 < 3 + r * (3 * r - 3 - K) := by
    have := mul_pos (show (0 : ℤ) < r by linarith) (show (0 : ℤ) < 3 * r - 3 - K by linarith)
    linarith
  have htq0 : 0 < tq := by linarith
  have hLpos : 0 < L := by
    have : 0 < L * tq := by rw [eL]; exact mul_pos (by linarith) hE0
    exact pos_of_mul_pos_left this htq0.le
  have hL2 : 2 ≤ L := by omega
  have h1 : 2 * tq ≤ 3 * (q + 1) * (3 + r * (3 * r - 3 - K)) := by
    rw [← eL]; exact mul_le_mul_of_nonneg_right hL2 htq0.le
  have hdr2 : 3 * r - 3 - K ≤ (3 * q - 3 - K) * (3 * r - 3 - K) :=
    le_mul_of_one_le_left (by linarith) (by linarith)
  have hKK := caseA_KK hK hKq
  have hKK2 : (K + 2) * (K + 2) ≤ (3 * q - 2) * (3 * q - 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hr3 : 3 * r < 9 * q ^ 2 := by linarith
  have hdr9 : 3 * r - 3 - K < 9 * q ^ 2 := by linarith
  have hrd : r * (3 * r - 3 - K) < 3 * q ^ 2 * (9 * q ^ 2) :=
    mul_lt_mul'' (by linarith) hdr9 (by linarith) (by linarith)
  have h2 : 3 * (q + 1) * (3 + r * (3 * r - 3 - K)) < 3 * (q + 1) * (3 + 27 * q ^ 4) := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    linarith
  linarith

/-- Case `b = 5`, `c = 3`: the range of `q`, the bound `2(q³+q) < 15 K(K+3)`, and the
quadratic equation in `r` used for the finite check. -/
theorem caseA_c3b (hK : 7 ≤ K) (hq : 5 ≤ q) (hqr : q + 2 ≤ r)
    (hKo : K % 2 = 1) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hWq : Wq = 3 * (q + 1) + (3 * q - 3 - K) * (q + q ^ 2 + q ^ 3 + q ^ 4))
    (hWr : Wr = 3 * (r + 1) + (3 * r - 3 - K) * (r + r ^ 2))
    (heq : Wq * Wr = K * (K + 3) * (q + q ^ 2 + q ^ 3 + q ^ 4) * (r + r ^ 2)) :
    K + 4 ≤ 3 * q ∧ 3 * q ≤ 2 * K + 4 ∧ 2 * (q ^ 3 + q) < 15 * (K * (K + 3)) ∧
    (3 + (3 * q - 3 - K) * (q ^ 3 + q)) * (3 + r * (3 * r - 3 - K)) =
      K * (K + 3) * (q ^ 3 + q) * r := by
  have hq0 : 0 ≤ q := by linarith
  have e2 := pow_nonneg hq0 2
  have e3 := pow_nonneg hq0 3
  have e4 := pow_nonneg hq0 4
  have htq1 : q ≤ q + q ^ 2 + q ^ 3 + q ^ 4 := by linarith
  have htq2 : q + q ^ 2 ≤ q + q ^ 2 + q ^ 3 + q ^ 4 := by linarith
  have htr1 : r ≤ r + r ^ 2 := by have := sq_nonneg r; linarith
  obtain ⟨hWq0, hWr0⟩ := caseA_pos hK hq hqr htq1 htr1 hWq hWr heq
  have hKq := caseA_K_le' hq htq2 hKo hqo hWq hWq0
  have hrange := caseA_range hK hq hqr htq1 htr1 hWq hWr heq hWq0
  obtain ⟨Om, hOmd⟩ : ∃ Om : ℤ, Om = K * (K + 3) - (3 * q - 3 - K) * (3 * r - 3 - K) :=
    ⟨_, rfl⟩
  obtain ⟨I1, -, hOm, hOmo⟩ :=
    caseA_Om hK hq hqr htq1 htr1 hKo hqo hro hWq hWr heq hOmd hWq0 (by linarith)
  have hqr0 : 0 < (q + 1) * (r + 1) := mul_pos (by linarith) (by linarith)
  have hQ : (3 + (3 * q - 3 - K) * (q ^ 3 + q)) * (3 + r * (3 * r - 3 - K)) =
      K * (K + 3) * (q ^ 3 + q) * r := by
    have h0 : ((q + 1) * (r + 1)) * ((3 + (3 * q - 3 - K) * (q ^ 3 + q))
        * (3 + r * (3 * r - 3 - K)) - K * (K + 3) * (q ^ 3 + q) * r) = 0 := by
      linear_combination heq - (3 * (r + 1) + (3 * r - 3 - K) * (r + r ^ 2)) * hWq - Wq * hWr
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  refine ⟨by linarith, hrange, ?_, hQ⟩
  have htq0 : 0 < q + q ^ 2 + q ^ 3 + q ^ 4 := by linarith
  have htr0 : 0 < r + r ^ 2 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = r * Om - 3 * (3 * q - 3 - K) := ⟨_, rfl⟩
  have eL0 : (r + 1) * (L * (q + q ^ 2 + q ^ 3 + q ^ 4)
      - 3 * (q + 1) * (3 + r * (3 * r - 3 - K))) = 0 := by
    rw [hL]; linear_combination I1 + 3 * (q + 1) * hWr
  have eL : L * (q + q ^ 2 + q ^ 3 + q ^ 4) = 3 * (q + 1) * (3 + r * (3 * r - 3 - K)) := by
    rcases mul_eq_zero.1 eL0 with h | h
    · linarith
    · linarith
  have hLe : L % 2 = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
    obtain ⟨w, hw⟩ : ∃ w, Om = 2 * w + 1 := ⟨Om / 2, by omega⟩
    have : r * Om = 2 * (2 * j * w + j + w) + 1 := by rw [hj, hw]; ring
    omega
  have hE0 : 0 < 3 + r * (3 * r - 3 - K) := by
    have := mul_pos (show (0 : ℤ) < r by linarith) (show (0 : ℤ) < 3 * r - 3 - K by linarith)
    linarith
  have hLpos : 0 < L := by
    have : 0 < L * (q + q ^ 2 + q ^ 3 + q ^ 4) := by
      rw [eL]; exact mul_pos (by linarith) hE0
    exact pos_of_mul_pos_left this htq0.le
  have hL2 : 2 ≤ L := by omega
  have hLb : 2 * (q ^ 3 + q) ≤ 3 * (3 + r * (3 * r - 3 - K)) := by
    have a1 : 2 * (q + q ^ 2 + q ^ 3 + q ^ 4) ≤ 3 * (q + 1) * (3 + r * (3 * r - 3 - K)) := by
      rw [← eL]; exact mul_le_mul_of_nonneg_right hL2 htq0.le
    have a2 : (q + 1) * (2 * (q ^ 3 + q)) ≤ (q + 1) * (3 * (3 + r * (3 * r - 3 - K))) := by
      linarith
    exact le_of_mul_le_mul_left a2 (by linarith)
  have hOb : (q ^ 3 + q) * r ≤
      3 * (3 + r * (3 * r - 3 - K)) + 3 * (3 * q - 3 - K) * (q ^ 3 + q) := by
    have a1 := mul_le_mul_of_nonneg_right hOm (mul_pos htq0 htr0).le
    rw [hWr] at I1
    have a3 : ((q + 1) * (r + 1)) * ((q ^ 3 + q) * r) ≤ ((q + 1) * (r + 1)) *
        (3 * (3 + r * (3 * r - 3 - K)) + 3 * (3 * q - 3 - K) * (q ^ 3 + q)) := by
      linarith
    exact le_of_mul_le_mul_left a3 hqr0
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = q ^ 3 + q := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = 3 * q - 3 - K := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = K * (K + 3) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℤ, E = 3 + r * (3 * r - 3 - K) := ⟨_, rfl⟩
  rw [← hP, ← hD, ← hM, ← hE] at hQ
  rw [← hP, ← hE] at hLb
  rw [← hP, ← hD, ← hE] at hOb
  rw [← hP, ← hM]
  have hP0 : 0 < P := by rw [hP]; linarith
  have hM0 : 0 < M := by rw [hM]; exact mul_pos (by linarith) (by linarith)
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hA0 : 0 < 3 + D * P := by have := mul_pos (by linarith : (0 : ℤ) < D) hP0; linarith
  have hL' : 2 * (3 + D * P) ≤ 3 * M * r := by
    have a1 := mul_le_mul_of_nonneg_left hLb hA0.le
    have a2 : P * (2 * (3 + D * P)) ≤ P * (3 * M * r) := by linarith
    exact le_of_mul_le_mul_left a2 hP0
  have hO' : r * (3 + D * P) ≤ 3 * M * r + 3 * D * (3 + D * P) := by
    have a1 := mul_le_mul_of_nonneg_left hOb hA0.le
    have a2 : P * (r * (3 + D * P)) ≤ P * (3 * M * r + 3 * D * (3 + D * P)) := by linarith
    exact le_of_mul_le_mul_left a2 hP0
  by_contra hc
  push Not at hc
  have hDP : P ≤ D * P := le_mul_of_one_le_left hP0.le hD1
  have hAM : 0 < 3 + D * P - 3 * M := by linarith
  have b1 := mul_le_mul_of_nonneg_right hL' hAM.le
  have b2 : r * (3 + D * P - 3 * M) ≤ 3 * D * (3 + D * P) := by linarith
  have b3 := mul_le_mul_of_nonneg_left b2 (show (0 : ℤ) ≤ 3 * M by linarith)
  have b4 : (3 + D * P) * (2 * (3 + D * P - 3 * M)) ≤ (3 + D * P) * (9 * M * D) := by linarith
  have b5 := le_of_mul_le_mul_left b4 hA0
  have b6 := mul_le_mul_of_nonneg_left hc (show (0 : ℤ) ≤ D by linarith)
  have b7 : M ≤ M * D := le_mul_of_one_le_right hM0.le hD1
  linarith

/-- The quadratic `A (3 + r (3r - 3 - K)) = C r` has no integer root `r ≥ 1` other than `r0`
when `3 A r0 < A (K+3) + C < 3 A (r0 + 1)`. -/
theorem quad_root {A C K r : ℤ} (r0 : ℤ) (h : A * (3 + r * (3 * r - 3 - K)) = C * r)
    (hA : 0 < A) (hr : 1 ≤ r) (h1 : A * (K + 3) + C < 3 * A * (r0 + 1))
    (h2 : 3 * A * r0 < A * (K + 3) + C) : r = r0 := by
  rcases lt_trichotomy r r0 with hlt | heq | hgt
  · exfalso
    have e1 : 0 ≤ A * (r * (r0 - 1 - r)) :=
      mul_nonneg hA.le (mul_nonneg (by linarith) (by linarith))
    have e2 : 0 ≤ (A * (K + 3) + C - 3 * A * r0 - 1) * (r - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have e3 : 0 ≤ A * (r - 1) := mul_nonneg hA.le (by linarith)
    linarith
  · exact heq
  · exfalso
    have e1 : 0 ≤ A * (r * (r - r0 - 1)) :=
      mul_nonneg hA.le (mul_nonneg (by linarith) (by linarith))
    have e2 : 0 ≤ (3 * A * (r0 + 1) - (A * (K + 3) + C)) * r :=
      mul_nonneg (by linarith) (by linarith)
    linarith

end CaseA

/-- The finite check for `b = 5`, `c = 3` (16 pairs `(a, q)`): for each, the
quadratic of `caseA_c3b` pins `r` to one integer `r0` (`quad_root`), which is not a solution
or is `< q + 2`. -/
theorem caseA_c3b_finite {a q r : ℕ} (ha : 2 ≤ a) (hq5 : 5 ≤ q) (hqo : q % 2 = 1)
    (hqr : q + 2 ≤ r) (h1 : (2 * 2 ^ a - 1 : ℤ) + 4 ≤ 3 * q)
    (h2 : (3 * q : ℤ) ≤ 2 * (2 * 2 ^ a - 1) + 4)
    (h3 : 2 * ((q : ℤ) ^ 3 + q) < 15 * ((2 * 2 ^ a - 1) * ((2 * 2 ^ a - 1) + 3)))
    (hQ : (3 + (3 * (q : ℤ) - 3 - (2 * 2 ^ a - 1)) * ((q : ℤ) ^ 3 + q)) *
        (3 + (r : ℤ) * (3 * r - 3 - (2 * 2 ^ a - 1))) =
      (2 * 2 ^ a - 1) * ((2 * 2 ^ a - 1) + 3) * ((q : ℤ) ^ 3 + q) * r) : False := by
  have hK0 : (1 : ℤ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hq67 : q ≤ 67 := by
    have hKK : (2 * 2 ^ a - 1 : ℤ) * ((2 * 2 ^ a - 1) + 3) ≤ (3 * q - 4) * (3 * q - 1) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    have hq' : (68 : ℤ) ≤ q := by exact_mod_cast hc
    have := mul_le_mul_of_nonneg_left hq' (sq_nonneg (q : ℤ))
    nlinarith
  have ha6 : a ≤ 6 := by
    have h99 : (2 : ℤ) ^ a ≤ 99 := by
      have : (q : ℤ) ≤ 67 := by exact_mod_cast hq67
      linarith
    have h' : 2 ^ a ≤ 99 := by exact_mod_cast h99
    by_contra hc
    have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key : (a = 2 ∧ q = 5) ∨
      (a = 3 ∧ q = 7) ∨
      (a = 3 ∧ q = 9) ∨
      (a = 3 ∧ q = 11) ∨
      (a = 4 ∧ q = 13) ∨
      (a = 4 ∧ q = 15) ∨
      (a = 4 ∧ q = 17) ∨
      (a = 4 ∧ q = 19) ∨
      (a = 5 ∧ q = 23) ∨
      (a = 5 ∧ q = 25) ∨
      (a = 5 ∧ q = 27) ∨
      (a = 5 ∧ q = 29) ∨
      (a = 5 ∧ q = 31) ∨
      (a = 6 ∧ q = 45) ∨
      (a = 6 ∧ q = 47) ∨
      (a = 6 ∧ q = 49) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hk33 : k ≤ 33 := by omega
    interval_cases a <;> interval_cases k <;> revert h1 h2 h3 <;> norm_num
  have hr1 : (1 : ℤ) ≤ r := by omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (quad_root 7 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 35 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 15 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 11 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by omega)
  · exact absurd (quad_root 81 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 43 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 31 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 26 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 483 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 175 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 114 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 87 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 73 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 1143 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 543 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)
  · exact absurd (quad_root 367 hQ (by norm_num) hr1 (by norm_num) (by norm_num))
      (fun h => by rw [h] at hQ; norm_num at hQ)


/-! ### Case A: assembly -/

/-- `(p - 1) t = p^e - p` for `t = σ(p^e) - 1 - p^e = p + ⋯ + p^(e-1)`. -/
theorem t_key {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p : ℤ) - 1) * ((σ 1 (p ^ e) : ℤ) - 1 - (p : ℤ) ^ e) = (p : ℤ) ^ e - p := by
  linear_combination sigma_prime_pow_key hp e

/-- Lower bounds for `t` from `(p - 1) t = p^e - p`. -/
theorem t_ge {p t s : ℤ} {e k : ℕ} (hp : 2 ≤ p) (ht : (p - 1) * t = p ^ e - p) (hke : k ≤ e)
    (hs : (p - 1) * s ≤ p ^ k - p) : s ≤ t := by
  have h1 : p ^ k ≤ p ^ e := pow_le_pow_right₀ (by linarith) hke
  by_contra hc
  push Not at hc
  have : (p - 1) * t < (p - 1) * s := mul_lt_mul_of_pos_left hc (by linarith)
  linarith

/-- Exact values of `t` from `(p - 1) t = p^e - p`. -/
theorem t_eq {p t s : ℤ} {e : ℕ} (hp : 2 ≤ p) (ht : (p - 1) * t = p ^ e - p)
    (hs : (p - 1) * s = p ^ e - p) : t = s := by
  have h0 : (p - 1) * (t - s) = 0 := by linear_combination ht - hs
  rcases mul_eq_zero.1 h0 with h | h
  · linarith
  · linarith

/-- Finite check for `c ≥ 7`: then `r = 7`, `q = 5`, `a ≤ 3`. -/
theorem caseA_finite7 {a b c q r : ℕ} (hr : r.Prime) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 7 ≤ c)
    (hq5 : 5 ≤ q) (hqr : q + 2 ≤ r) (hr9 : r ≤ 9) (hK : 2 * 2 ^ a ≤ 3 * q + 1)
    (h : σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c))) : False := by
  have hr7 : r = 7 := by
    have : 7 ≤ r := by omega
    interval_cases r <;> first | rfl | (norm_num at hr)
  subst hr7
  obtain rfl : q = 5 := by omega
  have ha3 : a ≤ 3 := by
    by_contra hc'
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases a
  · exact box_2_5_7_c7 le_rfl le_rfl hb hc h
  · exact box_2_5_7_a3 le_rfl le_rfl hb (by omega) h

/-- Finite check for `c ∈ {4, 6}`: `r ≤ 12` leaves `(a, q, r) ∈ {(2,5,7), (2,5,11), (3,7,11)}`. -/
theorem caseA_finite46 {a b c q r : ℕ} (hq : q.Prime) (hr : r.Prime) (ha : 2 ≤ a) (hb : 7 ≤ b)
    (hc : 4 ≤ c) (hq5 : 5 ≤ q) (hqr : q + 2 ≤ r) (hr12 : r ≤ 12)
    (hK1 : 2 * 2 ^ a + 3 ≤ 3 * q) (hK2 : 3 * q ≤ 4 * 2 ^ a + 2)
    (h : σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c))) : False := by
  have ha3 : a ≤ 3 := by
    by_contra hc'
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr7 : 7 ≤ r := by omega
  interval_cases a <;> norm_num at hK1 hK2
  · obtain rfl : q = 5 := by
      have : q ≤ 6 := by omega
      interval_cases q
      · rfl
      · norm_num at hq
    interval_cases r <;> (try (norm_num at hr; done))
    · exact box_2_5_7_b7 le_rfl le_rfl hb hc h
    · exact box_2_5_11 le_rfl le_rfl (by omega) (by omega) h
  · obtain rfl : q = 7 := by
      have : 7 ≤ q := by omega
      have : q ≤ 10 := by omega
      interval_cases q <;> first | rfl | norm_num at hq
    have : 9 ≤ r := by omega
    interval_cases r <;> (try (norm_num at hr; done))
    exact box_2_7_11 le_rfl le_rfl (by omega) (by omega) h

/-- **Case A**: no solution `2^a q^b r^c` with primes `5 ≤ q < r` and `a, b, c ≥ 2`. -/
theorem caseA {a b c q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hq5 : 5 ≤ q) (hqr : q < r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c))) : False := by
  have hqo : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  have hro : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
  have hqr2 : q + 2 ≤ r := by omega
  obtain ⟨hc2, hc3, hc5⟩ :=
    caseA_two_adic hq hr hqo hro hb (two_adic_rel (by omega) hq hr h)
  have k2 := sigma_two_pow_add_one a
  have k2' : ((σ 1 (2 ^ a) : ℕ) : ℤ) = 2 * 2 ^ a - 1 := by
    have : ((σ 1 (2 ^ a) + 1 : ℕ) : ℤ) = ((2 * 2 ^ a : ℕ) : ℤ) := by rw [k2]
    push_cast at this
    linarith
  have kq := t_key hq b
  have kr := t_key hr c
  have hZ : ((σ 1 (2 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) : ℕ) : ℤ) =
      ((2 * ((1 + 2 ^ a) * (1 + q ^ b) * (1 + r ^ c)) : ℕ) : ℤ) := by rw [h]
  push_cast at hZ
  have heq : (3 * ((q : ℤ) + 1) + (3 * q - 3 - (2 * 2 ^ a - 1)) *
        ((σ 1 (q ^ b) : ℤ) - 1 - (q : ℤ) ^ b)) *
      (3 * ((r : ℤ) + 1) + (3 * r - 3 - (2 * 2 ^ a - 1)) *
        ((σ 1 (r ^ c) : ℤ) - 1 - (r : ℤ) ^ c)) =
      (2 * 2 ^ a - 1) * ((2 * 2 ^ a - 1) + 3) * ((σ 1 (q ^ b) : ℤ) - 1 - (q : ℤ) ^ b) *
        ((σ 1 (r ^ c) : ℤ) - 1 - (r : ℤ) ^ c) := by
    linear_combination (-3) * hZ + 3 * (σ 1 (q ^ b) : ℤ) * (σ 1 (r ^ c) : ℤ) * k2'
      + 3 * (3 * ((r : ℤ) + 1) + (3 * r - 3 - (2 * 2 ^ a - 1)) *
        ((σ 1 (r ^ c) : ℤ) - 1 - (r : ℤ) ^ c)) * kq
      + 3 * (3 * (1 + (q : ℤ) ^ b) - (2 * 2 ^ a - 1) *
        ((σ 1 (q ^ b) : ℤ) - 1 - (q : ℤ) ^ b)) * kr
  generalize (σ 1 (q ^ b) : ℤ) - 1 - (q : ℤ) ^ b = tq at heq kq
  generalize (σ 1 (r ^ c) : ℤ) - 1 - (r : ℤ) ^ c = tr at heq kr
  have e2 : ((2 ^ a : ℕ) : ℤ) = (2 : ℤ) ^ a := by push_cast; ring
  generalize hKd : (2 * 2 ^ a - 1 : ℤ) = K at heq
  have hK7 : (7 : ℤ) ≤ K := by
    have : (2 : ℤ) ^ 2 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
    norm_num at this
    linarith
  have hKo : K % 2 = 1 := by omega
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have hqr' : (q : ℤ) + 2 ≤ r := by exact_mod_cast hqr2
  have hqo' : (q : ℤ) % 2 = 1 := by omega
  have hro' : (r : ℤ) % 2 = 1 := by omega
  have hq2 : (2 : ℤ) ≤ q := by linarith
  have hr2 : (2 : ℤ) ≤ r := by linarith
  have hr0 : (0 : ℤ) ≤ r := by linarith
  have htq : (q : ℤ) ≤ tq := t_ge hq2 kq hb (le_of_eq (by ring))
  have htr : (r : ℤ) ≤ tr := t_ge hr2 kr hc (le_of_eq (by ring))
  have htq6 : 7 ≤ b → (q : ℤ) ^ 6 ≤ tq := fun hb7 => t_ge hq2 kq hb7 (by
    have : (q : ℤ) ≤ q ^ 6 := le_self_pow₀ (by linarith) (by norm_num)
    linarith)
  have htq8 : 9 ≤ b → (q : ℤ) ^ 8 ≤ tq := fun hb9 => t_ge hq2 kq hb9 (by
    have : (q : ℤ) ≤ q ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith)
  rcases (show c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ 7 ≤ c by omega) with
    rfl | rfl | rfl | rfl | rfl | hc7
  · -- `c = 2`
    have htr_eq : tr = r := t_eq hr2 kr (by ring)
    subst htr_eq
    exact caseA_c2 hK7 hq' hqr' (htq6 (hc2 (by norm_num))) hKo hqo' hro' rfl rfl heq
  · -- `c = 3`
    have htr_eq : tr = r + r ^ 2 := t_eq hr2 kr (by ring)
    subst htr_eq
    rcases hc3 rfl with rfl | hb9
    · have htq_eq : tq = q + q ^ 2 + q ^ 3 + q ^ 4 := t_eq hq2 kq (by ring)
      subst htq_eq
      obtain ⟨h1, h2, h3, hQ⟩ := caseA_c3b hK7 hq' hqr' hKo hqo' hro' rfl rfl heq
      subst hKd
      exact caseA_c3b_finite ha hq5 hqo hqr2 h1 h2 h3 hQ
    · exact caseA_c3a hK7 hq' hqr' (htq8 hb9) hKo hqo' hro' rfl rfl heq
  · -- `c = 4`
    have hb7 := hc2 (by norm_num)
    have htr3 : (r : ℤ) + r ^ 2 + r ^ 3 ≤ tr := t_ge hr2 kr (le_refl 4) (le_of_eq (by ring))
    have h74 := caseA_c46 hK7 hq' hqr' (htq6 hb7) htr hKo hqo' hro' rfl rfl heq
    have hr12 : (r : ℤ) ≤ 12 := by
      by_contra hc'
      push Not at hc'
      have r1 := le_pow_succ_of_le (r := (r : ℤ)) (c := 13) (by norm_num) (by linarith) 1
      have r2 := le_pow_succ_of_le (r := (r : ℤ)) (c := 13) (by norm_num) (by linarith) 2
      norm_num at r1 r2
      linarith
    obtain ⟨hWq0, -⟩ := caseA_pos hK7 hq' hqr' htq htr rfl rfl heq
    have hKq := caseA_K_le' hq' (t_ge hq2 kq (by omega : 3 ≤ b) (le_of_eq (by ring)))
      hKo hqo' rfl hWq0
    have hrange := caseA_range hK7 hq' hqr' htq htr rfl rfl heq hWq0
    subst hKd
    exact caseA_finite46 hq hr ha hb7 le_rfl hq5 hqr2 (by exact_mod_cast hr12) (by omega)
      (by omega) h
  · -- `c = 5`
    have htr_eq : tr = r + r ^ 2 + r ^ 3 + r ^ 4 := t_eq hr2 kr (by ring)
    subst htr_eq
    rcases hc5 rfl with rfl | hb11
    · have htq_eq : tq = q + q ^ 2 := t_eq hq2 kq (by ring)
      subst htq_eq
      exact caseA_c5b hK7 hq' hqr' hKo hqo' hro' rfl rfl heq
    · have r1 := le_pow_succ_of_le (r := (r : ℤ)) (c := 7) (by norm_num) (by linarith) 1
      have r2 := le_pow_succ_of_le (r := (r : ℤ)) (c := 7) (by norm_num) (by linarith) 2
      have r3 := le_pow_succ_of_le (r := (r : ℤ)) (c := 7) (by norm_num) (by linarith) 3
      norm_num at r1 r2 r3
      have h74 := caseA_c46 hK7 hq' hqr' (htq6 (by omega)) (by linarith) hKo hqo' hro' rfl rfl
        heq
      linarith
  · -- `c = 6`
    have hb7 := hc2 (by norm_num)
    have htr3 : (r : ℤ) + r ^ 2 + r ^ 3 ≤ tr := t_ge hr2 kr (by norm_num : 4 ≤ 6)
      (le_of_eq (by ring))
    have h74 := caseA_c46 hK7 hq' hqr' (htq6 hb7) htr hKo hqo' hro' rfl rfl heq
    have hr12 : (r : ℤ) ≤ 12 := by
      by_contra hc'
      push Not at hc'
      have r1 := le_pow_succ_of_le (r := (r : ℤ)) (c := 13) (by norm_num) (by linarith) 1
      have r2 := le_pow_succ_of_le (r := (r : ℤ)) (c := 13) (by norm_num) (by linarith) 2
      norm_num at r1 r2
      linarith
    obtain ⟨hWq0, -⟩ := caseA_pos hK7 hq' hqr' htq htr rfl rfl heq
    have hKq := caseA_K_le' hq' (t_ge hq2 kq (by omega : 3 ≤ b) (le_of_eq (by ring)))
      hKo hqo' rfl hWq0
    have hrange := caseA_range hK7 hq' hqr' htq htr rfl rfl heq hWq0
    subst hKd
    exact caseA_finite46 hq hr ha hb7 (by norm_num) hq5 hqr2 (by exact_mod_cast hr12)
      (by omega) (by omega) h
  · -- `c ≥ 7`
    have htr6 : (r : ℤ) ^ 6 ≤ tr := t_ge hr2 kr hc7 (by
      have : (r : ℤ) ≤ r ^ 6 := le_self_pow₀ (by linarith) (by norm_num)
      linarith)
    have hr9 := caseA_c7 hK7 hq' hqr' htq htr hKo hqo' hro' rfl rfl heq htr6
    obtain ⟨hWq0, -⟩ := caseA_pos hK7 hq' hqr' htq htr rfl rfl heq
    have hKq := caseA_K_le hq' htq rfl hWq0
    subst hKd
    exact caseA_finite7 hr ha hb hc7 hq5 hqr2 (by exact_mod_cast hr9) (by omega) h

/-! ### Case B (odd primes) and the `{2, 3, r}` case -/

/-- **Case B**: no solution `p^a q^b r^c` with odd primes `3 ≤ p < q < r` and `a, b, c ≥ 2`. -/
theorem caseB {a b c p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hp3 : 3 ≤ p)
    (hpq : p < q) (hqr : q < r) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + p ^ a) * (1 + q ^ b) * (1 + r ^ c))) : False := by
  have hu : 0 < (1 + p ^ a) * (1 + q ^ b) * (1 + r ^ c) := by positivity
  rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with rfl | rfl | hp5
  · rcases (show q = 4 ∨ q = 5 ∨ q = 6 ∨ 7 ≤ q by omega) with rfl | rfl | rfl | hq7
    · norm_num at hq
    · -- `q = 5`: `r ∈ {7, 11, 13}` (boxes) or `r ≥ 17` (`3/2 · 5/4 · 17/16 < 2`)
      rcases (show r ≤ 16 ∨ 17 ≤ r by omega) with hr16 | hr17
      · have h7 : r = 7 ∨ r = 11 ∨ r = 13 := by
          interval_cases r <;> first | omega | norm_num at hr
        rcases h7 with rfl | rfl | rfl
        · exact box_3_5_7 ha hb hc h
        · exact box_3_5_11 ha hb hc h
        · exact box_3_5_13 ha hb hc h
      · exact absurd h (prod3_lt (mul_sigma_lt_of_le hp (m := 2) (by omega) a).le
          (mul_sigma_lt_of_le hq (m := 4) (by omega) b).le
          (mul_sigma_lt_of_le hr (m := 16) (by omega) c).le hu (by norm_num)).ne
    · norm_num at hq
    · -- `q ≥ 7`, `r ≥ 11`: `3/2 · 7/6 · 11/10 < 2`
      have hr11 : 11 ≤ r := by
        by_contra hc'
        have : 8 ≤ r := by omega
        interval_cases r <;> norm_num at hr
      exact absurd h (prod3_lt (mul_sigma_lt_of_le hp (m := 2) (by omega) a).le
        (mul_sigma_lt_of_le hq (m := 6) (by omega) b).le
        (mul_sigma_lt_of_le hr (m := 10) (by omega) c).le hu (by norm_num)).ne
  · norm_num at hp
  · -- `p ≥ 5`: `(5/4)^3 < 2`
    exact absurd h (prod3_lt (mul_sigma_lt_of_le hp (m := 4) (by omega) a).le
      (mul_sigma_lt_of_le hq (m := 4) (by omega) b).le
      (mul_sigma_lt_of_le hr (m := 4) (by omega) c).le hu (by norm_num)).ne

/-- `σ(p^e) = 1 + p X` for some `X`, i.e. `σ(p^e) ≡ 1 (mod p)`. -/
theorem sigma_prime_pow_eq_one_add_mul {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ∃ X, σ 1 (p ^ e) = 1 + p * X := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ']
  refine ⟨∑ i ∈ range e, p ^ i, ?_⟩
  rw [Finset.mul_sum, add_comm]
  simp only [pow_zero, pow_succ']

/-- `1 + p^e < σ(p^e)` for `e ≥ 2`. -/
theorem one_add_pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    1 + p ^ e < σ 1 (p ^ e) := by
  have k := t_key hp e
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (p : ℤ) ^ 2 ≤ (p : ℤ) ^ e := pow_le_pow_right₀ (by linarith) he
  have ht : (0 : ℤ) < (σ 1 (p ^ e) : ℤ) - 1 - (p : ℤ) ^ e := by
    by_contra hc
    push Not at hc
    nlinarith
  have : ((1 + p ^ e : ℕ) : ℤ) < (σ 1 (p ^ e) : ℤ) := by push_cast; linarith
  exact_mod_cast this

/-- **The `{2, 3, r}` case**: no solution `2^a 3^b r^c` with a prime `r ≥ 5` and
`a, b, c ≥ 2`. -/
theorem case23 {a b c r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (h : σ 1 (2 ^ a) * σ 1 (3 ^ b) * σ 1 (r ^ c) =
      2 * ((1 + 2 ^ a) * (1 + 3 ^ b) * (1 + r ^ c))) : False := by
  have hu : 0 < (1 + 2 ^ a) * (1 + 3 ^ b) * (1 + r ^ c) := by positivity
  have b3 := one_add_pow_le_sigma hr (by omega : 1 ≤ c)
  rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
  · have s4 : σ 1 (2 ^ 2) = 7 := by
      rw [sigma_one_apply_prime_pow Nat.prime_two]
      norm_num [Finset.sum_range_succ]
    rcases (show b = 2 ∨ b = 3 ∨ 4 ≤ b by omega) with rfl | rfl | hb4
    · -- `91 σ(r^c) = 100 (1 + r^c)` forces `r ∣ 9`
      have s9 : σ 1 (3 ^ 2) = 13 := by
        rw [sigma_one_apply_prime_pow Nat.prime_three]
        norm_num [Finset.sum_range_succ]
      obtain ⟨X, hX⟩ := sigma_prime_pow_eq_one_add_mul hr c
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      rw [s4, s9, hX, pow_succ r d] at h
      have key : 91 * (r * X) = 9 + 100 * (r ^ d * r) := by linarith
      have h1 : r ∣ 9 + 100 * (r ^ d * r) := by
        rw [← key]
        exact Dvd.dvd.mul_left (dvd_mul_right r X) 91
      have h9 : r ∣ 9 := (Nat.dvd_add_left (Dvd.dvd.mul_left (dvd_mul_left r _) 100)).mp h1
      have : r ≤ 9 := Nat.le_of_dvd (by norm_num) h9
      interval_cases r <;> first | omega | norm_num at hr
    · -- `280 σ(r^c) = 280 (1 + r^c)` contradicts `1 + r^c < σ(r^c)`
      have s27 : σ 1 (3 ^ 3) = 40 := by
        rw [sigma_one_apply_prime_pow Nat.prime_three]
        norm_num [Finset.sum_range_succ]
      rw [s4, s27] at h
      have := one_add_pow_lt_sigma hr hc
      linarith
    · -- `7/5 · 121/82 > 2`
      have b1 := sigma_ge_of_le (e₀ := 2) Nat.prime_two (le_refl 2)
      have b2 := sigma_ge_of_le (e₀ := 4) Nat.prime_three hb4
      refine absurd h (prod3_gt b1 b2 b3 hu ?_).ne'
      rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_two]
      rw [sigma_one_apply_prime_pow (i := 4) Nat.prime_three]
      norm_num [Finset.sum_range_succ]
  · -- `a ≥ 3`: `15/9 · 13/10 > 2`
    have b1 := sigma_ge_of_le (e₀ := 3) Nat.prime_two ha3
    have b2 := sigma_ge_of_le (e₀ := 2) Nat.prime_three hb
    refine absurd h (prod3_gt b1 b2 b3 hu ?_).ne'
    rw [sigma_one_apply_prime_pow (i := 3) Nat.prime_two]
    rw [sigma_one_apply_prime_pow (i := 2) Nat.prime_three]
    norm_num [Finset.sum_range_succ]

/-! ### Three-prime cores -/

/-- No solution `p^a q^b r^c` with primes `p < q < r` and `a, b, c ≥ 2`. -/
theorem three_prime_sorted {a b c p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) =
      2 * ((1 + p ^ a) * (1 + q ^ b) * (1 + r ^ c))) : False := by
  rcases (show p = 2 ∨ 3 ≤ p by have := hp.two_le; omega) with rfl | hp3
  · rcases (show q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | hq5
    · have hr5 : 5 ≤ r := by
        rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h5
        · norm_num at hr
        · exact h5
      exact case23 hr hr5 ha hb hc h
    · norm_num at hq
    · exact caseA hq hr hq5 hqr ha hb hc h
  · exact caseB hp hq hr hp3 hpq hqr ha hb hc h

/-- **Three-prime cores**: for distinct primes `p, q, r` and exponents `a, b, c ≥ 2`,
`p^a q^b r^c` is not a term. -/
theorem not_a_three_prime_pow {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ A (p ^ a * q ^ b * r ^ c) := by
  rintro ⟨-, hσ⟩
  have h1 : (p ^ a).Coprime (q ^ b) := ((Nat.coprime_primes hp hq).2 hpq).pow a b
  have h2 : (p ^ a * q ^ b).Coprime (r ^ c) :=
    Nat.Coprime.mul_left (((Nat.coprime_primes hp hr).2 hpr).pow a c)
      (((Nat.coprime_primes hq hr).2 hqr).pow b c)
  rw [isMultiplicative_sigma.map_mul_of_coprime h2, isMultiplicative_sigma.map_mul_of_coprime h1,
    usigma_mul h2, usigma_mul h1, usigma_prime_pow hp (by omega),
    usigma_prime_pow hq (by omega), usigma_prime_pow hr (by omega)] at hσ
  rcases lt_or_gt_of_ne hpq with h₁ | h₁ <;> rcases lt_or_gt_of_ne hpr with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hqr with h₃ | h₃
  · exact three_prime_sorted hp hq hr h₁ h₃ ha hb hc hσ
  · exact three_prime_sorted hp hr hq h₂ h₃ ha hc hb (by convert hσ using 1 <;> ring)
  · omega
  · exact three_prime_sorted hr hp hq h₂ h₁ hc ha hb (by convert hσ using 1 <;> ring)
  · exact three_prime_sorted hq hp hr h₁ h₂ hb ha hc (by convert hσ using 1 <;> ring)
  · omega
  · exact three_prime_sorted hq hr hp h₃ h₂ hb hc ha (by convert hσ using 1 <;> ring)
  · exact three_prime_sorted hr hq hp h₃ h₁ hc hb ha (by convert hσ using 1 <;> ring)

/-- A powerful solution with at most three distinct prime factors is `108`. -/
theorem eq_108_of_powerful_of_card_le_three {n : ℕ} (h : A n) (hpow : Powerful n)
    (hcard : n.primeFactors.card ≤ 3) : n = 108 := by
  rcases Nat.lt_or_ge n.primeFactors.card 3 with hlt | hge
  · exact eq_108_of_powerful h hpow (by omega)
  · exfalso
    have hn : n ≠ 0 := h.1.ne'
    have hfact := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at hfact
    obtain ⟨p, q, r, hpq, hpr, hqr, hs⟩ := Finset.card_eq_three.mp (le_antisymm hcard hge)
    have hpmem : p ∈ n.primeFactors := by rw [hs]; simp
    have hqmem : q ∈ n.primeFactors := by rw [hs]; simp
    have hrmem : r ∈ n.primeFactors := by rw [hs]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
    rw [hs, Finset.prod_insert (by simp [hpq, hpr]), Finset.prod_pair hqr] at hfact
    have ha : 2 ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).mp (hpow p hpmem)
    have hb : 2 ≤ n.factorization q := (hq.pow_dvd_iff_le_factorization hn).mp (hpow q hqmem)
    have hc : 2 ≤ n.factorization r := (hr.pow_dvd_iff_le_factorization hn).mp (hpow r hrmem)
    rw [← hfact, ← mul_assoc] at h
    exact not_a_three_prime_pow hp hq hr hpq hpr hqr ha hb hc h

/-- The induction of `exists_eq_108_mul_of_card_le_two`, for any bound `k` on `ω(C(n))`
under which every powerful solution is `108`. -/
theorem exists_eq_108_mul_of_card_le {k : ℕ}
    (hk : ∀ m, A m → Powerful m → m.primeFactors.card ≤ k → m = 108) {n : ℕ} (h : A n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ k) :
    ∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn : 0 < n := h.1
    by_cases hex : ∃ p ∈ n.primeFactors, ¬ p ^ 2 ∣ n
    · obtain ⟨p, hpmem, hp2⟩ := hex
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
      obtain ⟨m, rfl⟩ := hpn
      have hpm : ¬ p ∣ m := fun hpm => hp2 (by rw [pow_two]; exact mul_dvd_mul_left p hpm)
      have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hn)
      have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
      have hsqp : Squarefree p := hp.squarefree
      have hAm : A m := by
        rw [mul_comm] at h
        exact (a_mul_iff hsqp hcop).1 h
      have hlt : m < p * m := by
        have := hp.two_le
        nlinarith
      have hsub : (m.primeFactors.filter fun q => q ^ 2 ∣ m) ⊆
          ((p * m).primeFactors.filter fun q => q ^ 2 ∣ p * m) := by
        intro q hq
        rw [Finset.mem_filter] at hq ⊢
        refine ⟨?_, Dvd.dvd.mul_left hq.2 p⟩
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1.1, Dvd.dvd.mul_left hq.1.2.1 p, by positivity⟩
      have hcard : (m.primeFactors.filter fun q => q ^ 2 ∣ m).card ≤ k :=
        le_trans (Finset.card_le_card hsub) hω
      obtain ⟨s, hs, hcs, rfl⟩ := ih m hlt hAm hcard
      refine ⟨s * p, ?_, ?_, by ring⟩
      · have hsp : Nat.Coprime s p :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpm (h.mul_left 108))).symm
        exact (Nat.squarefree_mul hsp).2 ⟨hs, hsqp⟩
      · have h108p : Nat.Coprime 108 p :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpm (h.mul_right s))).symm
        exact Nat.Coprime.mul_right hcs h108p
    · have hex' : ∀ p ∈ n.primeFactors, p ^ 2 ∣ n :=
        fun p hp => not_not.mp (fun h => hex ⟨p, hp, h⟩)
      have hpow : Powerful n := hex'
      have hfilt : (n.primeFactors.filter fun p => p ^ 2 ∣ n) = n.primeFactors :=
        Finset.filter_true_of_mem hex'
      rw [hfilt] at hω
      refine ⟨1, squarefree_one, Nat.coprime_one_right 108, ?_⟩
      rw [hk n h hpow hω]

/-- **Three-prime theorem**: if `n ∈ A063880` and at most three primes `p` satisfy `p² ∣ n`
(i.e. `ω(C(n)) ≤ 3`), then `n = 108 s` with `s` squarefree and coprime to `108`. -/
theorem exists_eq_108_mul_of_card_le_three {n : ℕ} (h : A n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 3) :
    ∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s :=
  exists_eq_108_mul_of_card_le (fun _ hm hpow hc => eq_108_of_powerful_of_card_le_three hm hpow hc)
    h hω

/-- In the subfamily `ω(C(n)) ≤ 3`, every term is `108 (mod 216)`. -/
theorem mod_216_of_card_le_three {n : ℕ} (h : A n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 3) : n % 216 = 108 := by
  obtain ⟨s, hs, hcs, rfl⟩ := exists_eq_108_mul_of_card_le_three h hω
  have h2 : Nat.Coprime 2 s := Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 108) hcs
  have hodd : ¬ 2 ∣ s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 h2
  omega

/-- In the subfamily `ω(C(n)) ≤ 3`, the only primitive term is `108`. -/
theorem eq_108_of_isPrimitiveTerm_of_card_le_three {n : ℕ} (h : IsPrimitiveTerm n)
    (hω : (n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 3) : n = 108 := by
  have hA : A n := h.1
  obtain ⟨s, hs, hcs, rfl⟩ := exists_eq_108_mul_of_card_le_three hA hω
  by_cases hs1 : s = 1
  · subst hs1; rfl
  · exfalso
    have hs0 : s ≠ 0 := by rintro rfl; simp [A] at hA
    have hs2 : 2 ≤ s := by omega
    have hmem : 108 ∈ (108 * s).properDivisors :=
      Nat.mem_properDivisors.2 ⟨dvd_mul_right 108 s, by omega⟩
    exact Set.disjoint_left.mp h.2 hmem a_108

end AgenticConjectures.OeisA063880
