import Mathlib

/-!
# OEIS A056777 / Choudhury–Wei Conjecture 1.1 — `n + 12` is never a prime power

A056777 lists the composite numbers `n` with
`φ(n + 12) = φ(n) + 12` and `σ(n + 12) = σ(n) + 12`. Choudhury–Wei
(arXiv:2606.10331, Conjecture 1.1) conjecture that every such `n` is
`p * (p + 8)` for a prime quadruple `p, p+2, p+6, p+8`; that conjecture is
open and is recorded here as `statement` (a `Prop`, never proved).

This module formalizes the *partial* theorem of
`problems/oeis-a056777/PROOF.md`: for every `n ∈ A056777`, `n + 12` is not a
prime power (`add_twelve_ne_prime_pow`, `not_isPrimePow_add_twelve`).

It also contains three further structural constraints, none of which resolves the conjecture:

* `not_isPrimePow`: `n` itself is not a prime power (Choudhury–Wei Theorem 3.1, reproved here
  from the key inequality applied to `n + 12`);
* `semiprime_case`, `comesFromPrimeQuadruple_of_semiprime`: if `n = p q` and `n + 12 = p' q'`
  are products of two distinct primes, then `(p, p', q', q) = (p, p+2, p+6, p+8)` (the `⇒`
  direction of Choudhury–Wei Theorem 2.2; only the totient equation is used);
* `even_sigma`, `even_sigma_add_twelve`: `σ(n)` and `σ(n + 12)` are even, i.e. neither `n` nor
  `n + 12` is a square or twice a square (via `sq_or_two_mul_sq_of_odd_sigma`).

## Correspondence with the upstream snapshot

* `A` is the upstream predicate `OeisA56777.A` from
  `problems/oeis-a056777/upstream/56777.lean`
  (`¬n.Prime ∧ 1 < n ∧ totient (n + 12) = totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12`),
  copied term for term — the only spelling difference is mathlib's scoped
  notation `φ` for `Nat.totient`; since `1 < n` and `¬ n.Prime` force `n ≥ 4`,
  this is exactly "composite `n ≥ 4`" as in the paper and in `PROOF.md`.
  `ComesFromPrimeQuadruple` and `statement` mirror the upstream conjecture
  `comesFromPrimeQuadruple_of_a`.
* `φ` is `Nat.totient` and `σ 1` is `ArithmeticFunction.sigma 1`, both
  standard mathlib functions on `ℕ`; no subtraction semantics are involved in
  the statement (all equations are additive).
* "Prime power" means `q ^ ℓ` with `q` prime and `ℓ ≥ 1` (mathlib's
  `IsPrimePow`); the version `add_twelve_ne_prime_pow` even allows `ℓ = 0`
  (then `q ^ 0 = 1 ≠ n + 12` trivially).

## Proof outline

Write `N = n + 12`, `A(m) = m - φ(m)`, `B(m) = σ(m) - m`. The two equations
give `A(N) = A(n)` and `B(N) = B(n)`. The key lemma
`totient_mul_sigma_add_lt_of_not_isPrimePow` says `φ(m)σ(m) + m < m²`
whenever `m > 1` is not a prime power (informally: `Q(m) := m² - φ(m)σ(m) > m`).
For `N = q^ℓ` the identities pin down `φ(n)`, `σ(n)` in terms of `q, ℓ`, and:

* `q ≥ 5`: `n` cannot be a prime power (else `q ∣ 12`), so the key lemma
  applies and reduces to `(q² - 2q - 11) q^{ℓ-1} < 12 (q - 2)`, which leaves
  only `(q, ℓ) = (5, 2)`, i.e. `n = 13`, prime — contradiction.
* `q = 3`: `n = 3m` with `m` odd, `m > 2`, and the totient equation forces
  `φ(m) = m - 2`, odd — contradicting `Nat.totient_even`.
* `q = 2`: `n = 4w` with `w` odd and `8 ∣ w + 3`, and the two equations give
  `φ(w) = w - 3` and `7σ(w) = 8w + 11`. If `w` is a prime power, `φ(w) = w - 3`
  forces `w = 9`, but `8 ∤ 12`; otherwise the key lemma gives `w ≤ 9`, so
  `8 ∣ w + 3` leaves only `w = 5`, which `7σ(w) = 8w + 11` excludes (`7 ∤ 51`).

The `q = 2` case therefore replaces the "`σ(n)` odd ⇒ `n` is a square or twice a
square" argument of `PROOF.md` by a second use of the key lemma; the statement
proved is the same.
-/

namespace AgenticConjectures.OeisA056777

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- Membership in A056777, the upstream predicate `OeisA56777.A` term for term
(`φ` is mathlib's notation for `Nat.totient`, spelled `totient` upstream):
`n` is composite and satisfies `φ(n+12) = φ(n) + 12` and `σ(n+12) = σ(n) + 12`. -/
def A (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ φ (n + 12) = φ n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- `n = p (p + 8)` for a prime quadruple `p, p+2, p+6, p+8` (upstream
`OeisA56777.ComesFromPrimeQuadruple`). -/
def ComesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8)

/-- Choudhury–Wei Conjecture 1.1 (open, not proved here): every member of A056777
comes from a prime quadruple. -/
def statement : Prop := ∀ n, A n → ComesFromPrimeQuadruple n

/-- Sanity check: `65 ∈ A056777` (`65 = 5 * 13`, `77 = 7 * 11`). -/
theorem a_65 : A 65 := by
  refine ⟨?_, by norm_num, by decide, by decide⟩
  rw [show (65 : ℕ) = 5 * 13 by norm_num]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-! ### The key inequality `φ(m) σ(m) + m < m²` for non-prime-powers -/

/-- `φ(p^(k+1)) σ(p^(k+1)) + p^k = p^(2k+2)` for a prime `p`. -/
theorem totient_mul_sigma_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    φ (p ^ (k + 1)) * σ 1 (p ^ (k + 1)) + p ^ k = p ^ (2 * k + 2) := by
  rw [Nat.totient_prime_pow hp (by omega), ArithmeticFunction.sigma_one_apply_prime_pow hp,
    Nat.add_sub_cancel]
  have hp1 : 1 ≤ p := hp.one_le
  have G := geom_sum_mul (p : ℤ) (k + 2)
  zify [hp1]
  linear_combination (p : ℤ) ^ k * G

/-- `φ(m) σ(m) ≤ m²` for every `m` (multiplicativity plus the prime-power identity). -/
theorem totient_mul_sigma_le (m : ℕ) : φ m * σ 1 m ≤ m * m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := totient_mul_sigma_prime_pow_succ hp k
    have : p ^ (2 * k + 2) = p ^ (k + 1) * p ^ (k + 1) := by ring
    omega
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab]
    calc φ a * φ b * (σ 1 a * σ 1 b) = (φ a * σ 1 a) * (φ b * σ 1 b) := by ring
      _ ≤ (a * a) * (b * b) := Nat.mul_le_mul iha ihb
      _ = a * b * (a * b) := by ring

/-- If `m > 1` is not a prime power then `φ(m) σ(m) + m < m²`
(informally `Q(m) = m² - φ(m)σ(m) > m`, inequality (7) of `PROOF.md`). -/
theorem totient_mul_sigma_add_lt_of_not_isPrimePow {m : ℕ} (hm : 1 < m)
    (h : ¬ IsPrimePow m) : φ m * σ 1 m + m < m * m := by
  set r := m.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, u, hru, hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) r hr.ne_one
  have hrm : r ∣ m := Nat.minFac_dvd m
  -- the exponent of the least prime factor is positive
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
    refine ⟨e - 1, ?_⟩
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      simp at hmu
      exact absurd (hmu ▸ hrm) hru
    · omega
  -- the cofactor `u` exceeds `1` (else `m` is a prime power) …
  have hu0 : u ≠ 0 := by rintro rfl; simp at hmu; omega
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply h
    rw [hmu, mul_one]
    exact hr.isPrimePow.pow (by omega)
  have hu2 : 1 < u := by omega
  -- … and even exceeds `r`, since all its prime factors are `> r`
  have hru' : r < u := by
    have hs : u.minFac.Prime := Nat.minFac_prime hu1
    have hsu : u.minFac ∣ u := Nat.minFac_dvd u
    have hsm : u.minFac ∣ m := hsu.trans ⟨r ^ (e' + 1), by rw [hmu]; ring⟩
    have h1 : r ≤ u.minFac := Nat.minFac_le_of_dvd hs.two_le hsm
    have h2 : r ≠ u.minFac := by
      intro heq
      exact hru (heq ▸ hsu)
    have h3 : u.minFac ≤ u := Nat.minFac_le (by omega)
    omega
  have hcop : (r ^ (e' + 1)).Coprime u := ((hr.coprime_iff_not_dvd).mpr hru).pow_left _
  have hP := totient_mul_sigma_prime_pow_succ hr e'
  have hU := totient_mul_sigma_le u
  rw [hmu, Nat.totient_mul hcop, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  set y := r ^ e' with hy
  have hy0 : 0 < y := pow_pos hr.pos e'
  have hre : r ^ (e' + 1) = y * r := by rw [hy, pow_succ]
  have hr2 : r ^ (2 * e' + 2) = y * y * r * r := by rw [hy]; ring
  rw [hre] at hP ⊢
  rw [hr2] at hP
  set P := φ (y * r) * σ 1 (y * r) with hP_def
  set V := φ u * σ 1 u with hV_def
  have h1 : y * r * u < y * u * u := by
    have : r * u < u * u := Nat.mul_lt_mul_of_pos_right hru' (by omega)
    calc y * r * u = y * (r * u) := by ring
      _ < y * (u * u) := Nat.mul_lt_mul_of_pos_left this hy0
      _ = y * u * u := by ring
  have h2 : P * V ≤ P * (u * u) := Nat.mul_le_mul_left P hU
  calc φ (y * r) * φ u * (σ 1 (y * r) * σ 1 u) + y * r * u
      = P * V + y * r * u := by rw [hP_def, hV_def]; ring
    _ < P * V + y * u * u := by omega
    _ ≤ P * (u * u) + y * (u * u) := by nlinarith
    _ = (P + y) * (u * u) := by ring
    _ = y * y * r * r * (u * u) := by rw [hP]
    _ = y * r * u * (y * r * u) := by ring

/-! ### The three cases `q = 2`, `q = 3`, `q ≥ 5` -/

/-- Case `q = 2`: `n + 12` is not a power of two. -/
theorem add_twelve_ne_two_pow {n : ℕ} (h : A n) (ℓ : ℕ) : n + 12 ≠ 2 ^ ℓ := by
  intro hN
  obtain ⟨hnp, hn1, hφ, hσ⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := by
    refine ⟨ℓ - 2, ?_⟩
    rcases Nat.lt_or_ge ℓ 2 with h2 | h2
    · interval_cases ℓ <;> simp at hN
    · omega
  set z := 2 ^ k with hz
  have hn : n + 12 = 4 * z := by rw [hN, hz, pow_succ, pow_succ]; ring
  have hφN : φ (2 ^ (k + 2)) = 2 * z := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega), show k + 2 - 1 = k + 1 by omega, hz,
      pow_succ]
    omega
  have hgeom : ∀ j, ∑ i ∈ range j, 2 ^ i + 1 = 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hσN : σ 1 (2 ^ (k + 2)) + 1 = 8 * z := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, hgeom, hz]; ring
  rw [hN, hφN] at hφ
  rw [hN] at hσ
  -- `φ n + 12 = 2z` forces `z ≥ 6`, hence `k ≥ 3` and `8 ∣ z`
  have hk3 : 3 ≤ k := by
    by_contra hk
    have : z ≤ 4 := by
      interval_cases k <;> simp [hz]
    omega
  have h8 : 8 ∣ z := by
    have := Nat.pow_dvd_pow 2 hk3
    simpa [hz] using this
  clear_value z
  -- write `z = w + 3`, so `n = 4w` with `w` odd
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 3 := ⟨z - 3, by omega⟩
  have hnw : n = 4 * w := by omega
  have hwodd : ¬ 2 ∣ w := by omega
  have hcop : Nat.Coprime 4 w := by
    have : Nat.Coprime (2 ^ 2) w := ((Nat.prime_two.coprime_iff_not_dvd).mpr hwodd).pow_left 2
    simpa using this
  have hφ4 : φ 4 = 2 := by decide
  have hσ4 : σ 1 4 = 7 := by decide
  have hφw : φ w + 3 = w := by
    rw [hnw, Nat.totient_mul hcop, hφ4] at hφ
    omega
  have hσw : 7 * σ 1 w = 8 * w + 11 := by
    rw [hnw, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hσ4] at hσ
    omega
  have hw1 : 1 < w := by omega
  by_cases hpp : IsPrimePow w
  · -- `w = p^a` with `φ(w) = w - 3` forces `w = 9`, but `8 ∤ 12`
    obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff _).mp hpp
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := by
      rcases a with _ | _ | b
      · omega
      · rw [pow_one] at hpa
        subst hpa
        rw [Nat.totient_prime hp] at hφw
        have := hp.two_le
        omega
      · exact ⟨b, rfl⟩
    have hφp : φ w = p ^ (b + 1) * (p - 1) := by
      rw [← hpa, Nat.totient_prime_pow hp (by omega), show b + 2 - 1 = b + 1 by omega]
    have hwp : w = p ^ (b + 1) * p := by rw [← hpa, pow_succ]
    have hy3 : p ^ (b + 1) = 3 := by
      have hp1 : 1 ≤ p := hp.one_le
      have := hφw
      rw [hφp] at this
      rw [hwp] at this
      zify [hp1] at this ⊢
      linarith
    have hp3 : p ∣ 3 := hy3 ▸ dvd_pow_self p (by omega)
    have hp3' : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    have hp2 := hp.two_le
    interval_cases p
    · omega
    · rw [hy3] at hwp
      omega
  · -- otherwise the key inequality gives `(w-3)(8w+11) + 7w < 7w²`, i.e. `w ≤ 9`;
    -- `8 ∣ w + 3` then leaves only `w = 5`, killed by `7 ∤ 8 * 5 + 11`
    have hQ := totient_mul_sigma_add_lt_of_not_isPrimePow hw1 hpp
    have hw9 : w ≤ 9 := by
      have hφZ : (φ w : ℤ) = w - 3 := by
        have := hφw; zify at this; linarith
      have hσZ : (7 : ℤ) * σ 1 w = 8 * w + 11 := by exact_mod_cast hσw
      have hQZ : (φ w : ℤ) * σ 1 w + w < w * w := by exact_mod_cast hQ
      have h7 : (7 : ℤ) * (φ w * σ 1 w + w) < 7 * (w * w) := by linarith
      rw [hφZ] at h7
      have h8' : ((w : ℤ) - 3) * (7 * σ 1 w) = (w - 3) * (8 * w + 11) := by rw [hσZ]
      have hw9Z : (w : ℤ) ≤ 9 := by nlinarith
      exact_mod_cast hw9Z
    omega

/-- Case `q = 3`: `n + 12` is not a power of three. -/
theorem add_twelve_ne_three_pow {n : ℕ} (h : A n) (ℓ : ℕ) : n + 12 ≠ 3 ^ ℓ := by
  intro hN
  obtain ⟨hnp, hn1, hφ, -⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := by
    refine ⟨ℓ - 1, ?_⟩
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0; simp at hN
    · omega
  set y := 3 ^ k with hy
  have hn : n + 12 = 3 * y := by rw [hN, hy, pow_succ]; ring
  have hφN : φ (3 ^ (k + 1)) = 2 * y := by
    rw [Nat.totient_prime_pow Nat.prime_three (by omega), Nat.add_sub_cancel, hy]; ring
  rw [hN, hφN] at hφ
  have hyodd : Odd y := Odd.pow (by decide)
  obtain ⟨t, ht⟩ := hyodd
  -- `n ≥ 2` forces `y ≥ 5`, hence `k ≥ 2` and `9 ∣ y`
  have hk2 : 2 ≤ k := by
    by_contra hk
    have : y ≤ 3 := by
      interval_cases k <;> simp [hy]
    omega
  have h9 : 9 ∣ y := by
    have := Nat.pow_dvd_pow 3 hk2
    simpa [hy] using this
  clear_value y
  -- write `y = m + 4`, so `n = 3m` with `m` odd, `3 ∤ m`, and `φ(m) = m - 2`
  obtain ⟨m, rfl⟩ : ∃ m, y = m + 4 := ⟨y - 4, by omega⟩
  have hnm : n = 3 * m := by omega
  have hcop : Nat.Coprime 3 m := (Nat.prime_three.coprime_iff_not_dvd).mpr (by omega)
  have hφn : φ n = 2 * φ m := by
    rw [hnm, Nat.totient_mul hcop, Nat.totient_prime Nat.prime_three]
  obtain ⟨s, hs⟩ := Nat.totient_even (by omega : 2 < m)
  omega

/-- Case `q ≥ 5`: `n + 12` is not a power of a prime `q ≥ 5`. -/
theorem add_twelve_ne_prime_pow_of_five_le {n : ℕ} (h : A n) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (ℓ : ℕ) : n + 12 ≠ q ^ ℓ := by
  intro hN
  obtain ⟨hnp, hn1, hφ, hσ⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := by
    refine ⟨ℓ - 1, ?_⟩
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0; simp at hN
    · omega
  set x := q ^ k with hx
  have hx1 : 1 ≤ x := Nat.one_le_pow _ _ hq.pos
  have hxdiv : x = 1 ∨ q ∣ x := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · left; rw [hx, hk, pow_zero]
    · right; exact dvd_pow_self q (by omega)
  have hn : n + 12 = q * x := by rw [hN, hx, pow_succ]; ring
  have hq1 : 1 ≤ q := hq.one_le
  -- totient equation: `φ n + x = n`
  have hφN : φ (q ^ (k + 1)) = x * (q - 1) := by
    rw [Nat.totient_prime_pow hq (by omega), Nat.add_sub_cancel]
  have hφn : φ n + x = n := by
    rw [hN, hφN] at hφ
    zify [hq1] at hφ hn ⊢
    linarith
  -- sigma equation: `σ n = n + S` with `S (q - 1) = q x - 1`
  set S := ∑ i ∈ range (k + 1), q ^ i with hS_def
  have hσN : σ 1 (q ^ (k + 1)) = S + q * x := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq, Finset.sum_range_succ, hx, pow_succ]
    ring
  have hσn : σ 1 n = n + S := by
    rw [hN, hσN] at hσ
    omega
  have hSZ : (S : ℤ) * (q - 1) = q * x - 1 := by
    have G := geom_sum_mul (q : ℤ) (k + 1)
    rw [hS_def, hx]
    push_cast
    rw [G, pow_succ]
    ring
  -- Step 1: `n` is not a prime power (else `q ∣ 12`)
  have hnpp : ¬ IsPrimePow n := by
    intro hpp
    obtain ⟨r, a, hr, ha, hra⟩ := (isPrimePow_nat_iff _).mp hpp
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := by
      rcases a with _ | _ | b
      · omega
      · rw [pow_one] at hra; exact absurd (hra ▸ hr) hnp
      · exact ⟨b, rfl⟩
    have hφr : φ n = r ^ (b + 1) * (r - 1) := by
      rw [← hra, Nat.totient_prime_pow hr (by omega), show b + 2 - 1 = b + 1 by omega]
    have hnr : n = r ^ (b + 1) * r := by rw [← hra, pow_succ]
    have hyx : r ^ (b + 1) = x := by
      have hr1 : 1 ≤ r := hr.one_le
      have := hφn
      rw [hφr] at this
      rw [hnr] at this
      zify [hr1] at this ⊢
      linarith
    have hrq : r ∣ q := by
      have : r ∣ x := hyx ▸ dvd_pow_self r (by omega)
      rw [hx] at this
      exact hr.dvd_of_dvd_pow this
    have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
    subst hrq'
    have hqn : r ∣ n := by rw [hnr]; exact Dvd.intro_left _ rfl
    have hq12 : r ∣ 12 := by
      have h1 : r ∣ n + 12 := by rw [hn]; exact Dvd.intro _ rfl
      exact (Nat.dvd_add_right hqn).mp h1
    have hq12' : r ≤ 12 := Nat.le_of_dvd (by norm_num) hq12
    interval_cases r <;> omega
  -- Step 2: the key inequality, pushed through the identities:
  -- `(q² - 2q - 11) x < 12 (q - 2)`
  have hQ := totient_mul_sigma_add_lt_of_not_isPrimePow hn1 hnpp
  have h4 : q * q * x + 24 < 2 * q * x + 11 * x + 12 * q := by
    have hφZ : (φ n : ℤ) = n - x := by
      have := hφn; zify at this; linarith
    have hσZ : (σ 1 n : ℤ) = n + S := by exact_mod_cast hσn
    have hnZ : (n : ℤ) + 12 = q * x := by exact_mod_cast hn
    have hQZ : (φ n : ℤ) * σ 1 n + n < n * n := by exact_mod_cast hQ
    rw [hφZ, hσZ] at hQZ
    have E1 : (n : ℤ) * (S + 1 - x) < x * S := by linarith
    have hqpos : (0 : ℤ) < q - 1 := by
      have : (5 : ℤ) ≤ q := by exact_mod_cast hq5
      linarith
    have E2 : (q - 1 : ℤ) * (n * (S + 1 - x)) < (q - 1) * (x * S) :=
      mul_lt_mul_of_pos_left E1 hqpos
    have E3 : (n : ℤ) * (x + q - 2) < q * x * x - x := by
      have h1 : (S : ℤ) * (q - 1) * n = (q * x - 1) * n := by rw [hSZ]
      have h2 : (S : ℤ) * (q - 1) * x = (q * x - 1) * x := by rw [hSZ]
      linarith
    have E4 : (q : ℤ) * q * x + 24 < 2 * q * x + 11 * x + 12 * q := by
      have h1 : ((n : ℤ) + 12) * (x + q - 2) = q * x * (x + q - 2) := by rw [hnZ]
      linarith
    exact_mod_cast E4
  -- Step 3: hence `q ≤ 12`
  have hq12 : q ≤ 12 := by
    by_contra hcon
    have hqZ : (13 : ℤ) ≤ q := by exact_mod_cast (show 13 ≤ q by omega)
    have hxZ : (1 : ℤ) ≤ x := by exact_mod_cast hx1
    have h4Z : (q : ℤ) * q * x + 24 < 2 * q * x + 11 * x + 12 * q := by exact_mod_cast h4
    nlinarith [mul_nonneg (sub_nonneg.mpr hxZ) (show (0 : ℤ) ≤ q * q - 2 * q - 11 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ q - 1 by linarith) (show (0 : ℤ) ≤ q - 13 by linarith)]
  -- Step 4: finite check; the only survivor `(q, x) = (5, 5)` gives `n = 13`, prime
  interval_cases q <;> first
    | omega
    | (have h13 : n = 13 := by omega
       rw [h13] at hnp
       exact hnp (by norm_num))

/-! ### Main theorem -/

/-- **Main theorem.** For `n ∈ A056777` and any prime `q`, `n + 12 ≠ q ^ ℓ`. -/
theorem add_twelve_ne_prime_pow {n : ℕ} (h : A n) {q : ℕ} (hq : q.Prime) (ℓ : ℕ) :
    n + 12 ≠ q ^ ℓ := by
  obtain h2 | h3 | h5 : q = 2 ∨ q = 3 ∨ 5 ≤ q := by
    have := hq.two_le
    by_contra! hlt
    obtain ⟨h2, h3, hlt⟩ := hlt
    interval_cases q
    · exact h2 rfl
    · exact h3 rfl
    · norm_num at hq
  · subst h2; exact add_twelve_ne_two_pow h ℓ
  · subst h3; exact add_twelve_ne_three_pow h ℓ
  · exact add_twelve_ne_prime_pow_of_five_le h hq h5 ℓ

/-- **Main theorem**, `IsPrimePow` form: for `n ∈ A056777`, `n + 12` is not a prime power. -/
theorem not_isPrimePow_add_twelve {n : ℕ} (h : A n) : ¬ IsPrimePow (n + 12) := by
  intro hpp
  obtain ⟨q, ℓ, hq, -, hN⟩ := (isPrimePow_nat_iff _).mp hpp
  exact add_twelve_ne_prime_pow h hq ℓ hN.symm

/-! ### `n` itself is not a prime power (Choudhury–Wei Theorem 3.1) -/

/-- **Choudhury–Wei Theorem 3.1**: for `n ∈ A056777`, `n` itself is not a prime power.
With `n = r^(b+2)` and `x = r^(b+1)` one has `φ(n)σ(n) + x = n²`, `φ(n) + x = n` and
`σ(n) ≥ n + x`; since `n + 12` is not a prime power (`not_isPrimePow_add_twelve`), the key
inequality for `n + 12` then forces `n + 12 < x`, impossible as `x < n`. -/
theorem not_isPrimePow {n : ℕ} (h : A n) : ¬ IsPrimePow n := by
  intro hpp
  have hN := not_isPrimePow_add_twelve h
  obtain ⟨hnp, hn1, hφ, hσ⟩ := h
  obtain ⟨r, a, hr, ha, hra⟩ := (isPrimePow_nat_iff _).mp hpp
  -- `a ≥ 2`, since `n` is not prime
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := by
    rcases a with _ | _ | b
    · omega
    · rw [pow_one] at hra; exact absurd (hra ▸ hr) hnp
    · exact ⟨b, rfl⟩
  -- the key inequality for `n + 12`, rewritten with the two equations
  have hQ := totient_mul_sigma_add_lt_of_not_isPrimePow (by omega : 1 < n + 12) hN
  rw [hφ, hσ] at hQ
  -- prime-power data for `n = r ^ (b + 2)`, with `x = r ^ (b + 1)`
  have hr1 : 1 ≤ r := hr.one_le
  set x := r ^ (b + 1) with hx
  have hnx : n = x * r := by rw [← hra, hx, pow_succ]
  have hP : φ n * σ 1 n + x = n * n := by
    have := totient_mul_sigma_prime_pow_succ hr (b + 1)
    rw [show b + 1 + 1 = b + 2 from rfl, hra, ← hx] at this
    rw [this, ← hra]
    ring
  have hφx : φ n + x = n := by
    have h1 : φ n = x * (r - 1) := by
      rw [← hra, Nat.totient_prime_pow hr (by omega), show b + 2 - 1 = b + 1 by omega]
    rw [h1, hnx]
    zify [hr1]
    ring
  have hσx : n + x ≤ σ 1 n := by
    rw [← hra, ArithmeticFunction.sigma_one_apply_prime_pow hr, Finset.sum_range_succ,
      Finset.sum_range_succ, ← hx]
    omega
  have hxn : 2 * x ≤ n := by rw [hnx]; nlinarith [hr.two_le]
  nlinarith [hQ, hP, hφx, hσx, hxn]

/-! ### The semiprime case (Choudhury–Wei Theorem 2.2) -/

/-- For distinct primes `p ≠ q`: `φ(pq) + p + q = pq + 1`. -/
theorem totient_mul_add_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    φ (p * q) + p + q = p * q + 1 := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]
  zify [hp.one_le, hq.one_le]
  ring

/-- **Choudhury–Wei Theorem 2.2** (`⇒`; only the totient equation is needed): if `n = p q` and
`n + 12 = p' q'` with primes `p < q`, `p' < q'` and `φ(n + 12) = φ(n) + 12`, then
`(p, p', q', q) = (p, p + 2, p + 6, p + 8)`. The totient equation gives `p' + q' = p + q`;
then `p < p'` and `(p' - p)(q' - p) = 12`, and parity leaves only `(2, 6)`. -/
theorem semiprime_case {n p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime)
    (hq' : q'.Prime) (hpq : p < q) (hpq' : p' < q') (hn : n = p * q) (hN : n + 12 = p' * q')
    (hφ : φ (n + 12) = φ n + 12) : p' = p + 2 ∧ q' = p + 6 ∧ q = p + 8 := by
  have h1 := totient_mul_add_of_primes hp hq hpq.ne
  have h2 := totient_mul_add_of_primes hp' hq' hpq'.ne
  rw [← hn] at h1
  rw [← hN, hφ] at h2
  have hs : p' + q' = p + q := by omega
  have hprod : p' * q' = p * q + 12 := by rw [← hN, hn]
  -- `p < p'`: otherwise `(p - p') (q - p') ≥ 0` contradicts `p' q' = p q + 12`
  have hlt : p < p' := by
    by_contra hle
    push Not at hle
    have hq'q : q' = q + (p - p') := by omega
    rw [hq'q] at hprod
    have e : p = p' + (p - p') := by omega
    set d := p - p'
    rw [e] at hprod
    nlinarith [Nat.mul_le_mul_left d (show p' ≤ q by omega)]
  obtain ⟨x, rfl⟩ : ∃ x, p' = p + x := ⟨p' - p, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, q' = p + y := ⟨q' - p, by omega⟩
  have hq_eq : q = p + x + y := by omega
  subst hq_eq
  have hxy : x * y = 12 := by nlinarith
  have hx12 : x ≤ 12 := by
    rcases Nat.eq_zero_or_pos y with hy | hy
    · subst hy; omega
    · nlinarith
  have hxy' : x < y := by omega
  have hp2 := hp.two_le
  -- `x * y = 12` with `x < y`: `(x, y) = (2, 6)` is the prime quadruple (closed by `omega`);
  -- `(1, 12)` needs `p = 2` and then `q' = 14`; `(3, 4)` fails by parity
  interval_cases x
  all_goals first
    | omega
    | (have hy : y = 12 := by omega
       subst hy
       rcases hp.eq_two_or_odd with h2 | h2
       · subst h2; norm_num at hq'
       · rcases hp'.eq_two_or_odd with h2' | h2' <;> omega)
    | (rcases hp'.eq_two_or_odd with h2 | h2 <;> rcases hq'.eq_two_or_odd with h2' | h2' <;>
        omega)

/-- The semiprime case in the form of the conjecture: if `n ∈ A056777` and both `n` and
`n + 12` are products of two distinct primes, then `n` comes from a prime quadruple. -/
theorem comesFromPrimeQuadruple_of_semiprime {n p q p' q' : ℕ} (h : A n) (hp : p.Prime)
    (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime) (hpq : p < q) (hpq' : p' < q')
    (hn : n = p * q) (hN : n + 12 = p' * q') : ComesFromPrimeQuadruple n := by
  obtain ⟨h2, h6, h8⟩ := semiprime_case hp hq hp' hq' hpq hpq' hn hN h.2.2.1
  subst h2 h6 h8
  exact ⟨p, hp, hp', hq', hq, hn⟩

/-! ### Parity of `σ`: neither `n` nor `n + 12` is a square or twice a square -/

/-- For odd `p`, `∑_{i<k} p^i ≡ k (mod 2)`. -/
theorem geom_sum_mod_two_of_odd {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp hp.pow]
    omega

/-- If `σ(m)` is odd, then `m` is a square or twice a square. -/
theorem sq_or_two_mul_sq_of_odd_sigma (m : ℕ) (h : Odd (σ 1 m)) :
    ∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at h
    rcases hp.eq_two_or_odd' with rfl | hpo
    · rcases Nat.even_or_odd e with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨2 ^ t, Or.inl (by ring)⟩
      · exact ⟨2 ^ t, Or.inr (by ring)⟩
    · -- `σ(p^e) ≡ e + 1 (mod 2)` for odd `p`, so `e` is even
      have h2 := geom_sum_mod_two_of_odd hpo (e + 1)
      rw [Nat.odd_iff] at h
      obtain ⟨t, rfl⟩ : ∃ t, e = 2 * t := ⟨e / 2, by omega⟩
      exact ⟨p ^ t, Or.inl (by ring)⟩
  | zero => exact ⟨0, Or.inl (by simp)⟩
  | one => exact ⟨1, Or.inl (by simp)⟩
  | coprime a b ha hb hab iha ihb =>
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab] at h
    obtain ⟨s, hs⟩ := iha (Nat.odd_mul.mp h).1
    obtain ⟨t, ht⟩ := ihb (Nat.odd_mul.mp h).2
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨s * t, Or.inl (by ring)⟩
    · exact ⟨s * t, Or.inr (by ring)⟩
    · exact ⟨s * t, Or.inr (by ring)⟩
    · exact ⟨2 * s * t, Or.inl (by ring)⟩

/-- **`σ`-parity.** For `n ∈ A056777`, `σ(n)` is even (hence so is `σ(n + 12) = σ(n) + 12`):
otherwise `n` and `n + 12` would both be squares or twice squares. `k² + 12 = j²` forces
`(k, j) = (2, 4)`, i.e. `n = 4 ∉ A056777`; `k² + 12 = 2j²` and `2k² + 12 = j²` are impossible
mod 32, and `2k² + 12 = 2j²` mod 8. -/
theorem even_sigma {n : ℕ} (h : A n) : Even (σ 1 n) := by
  by_contra hev
  rw [Nat.not_even_iff_odd] at hev
  obtain ⟨hnp, hn1, hφ, hσ⟩ := h
  have hodd : Odd (σ 1 (n + 12)) := by
    rw [hσ]
    exact hev.add_even (by decide)
  obtain ⟨k, hk⟩ := sq_or_two_mul_sq_of_odd_sigma n hev
  obtain ⟨j, hj⟩ := sq_or_two_mul_sq_of_odd_sigma (n + 12) hodd
  have h32a : ∀ a b : ZMod 32, a ^ 2 + 12 ≠ 2 * b ^ 2 := by decide
  have h32b : ∀ a b : ZMod 32, 2 * a ^ 2 + 12 ≠ b ^ 2 := by decide
  have h8 : ∀ a b : ZMod 8, 2 * a ^ 2 + 12 ≠ 2 * b ^ 2 := by decide
  rcases hk with rfl | rfl <;> rcases hj with hj | hj
  · -- `k² + 12 = j²`: then `k < j`, so `2k + 1 ≤ 12`; only `(k, j) = (2, 4)`, i.e. `n = 4`
    have hkj : k < j := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul hc hc]
    have hk5 : k ≤ 5 := by
      nlinarith [Nat.mul_le_mul (Nat.succ_le_of_lt hkj) (Nat.succ_le_of_lt hkj)]
    have hj6 : j ≤ 6 := by nlinarith [Nat.mul_le_mul hk5 hk5]
    interval_cases k <;> interval_cases j <;> first
      | (norm_num at hj; done)
      | exact absurd hφ (by decide)
  · exact h32a k j (by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 32) hj)
  · exact h32b k j (by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 32) hj)
  · exact h8 k j (by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 8) hj)

/-- For `n ∈ A056777`, `σ(n + 12)` is even as well. -/
theorem even_sigma_add_twelve {n : ℕ} (h : A n) : Even (σ 1 (n + 12)) := by
  rw [h.2.2.2]
  exact (even_sigma h).add (by decide)

end AgenticConjectures.OeisA056777
