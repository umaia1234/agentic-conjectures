import Mathlib

/-!
# OEIS A063880 — `σ(n) = 2 σ*(n)`: solutions whose powerful core has at most two primes

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
* The hypothesis `ω(C(n)) ≤ 2` is encoded as
  `(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2` — the primes `p` with
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

end AgenticConjectures.OeisA063880
