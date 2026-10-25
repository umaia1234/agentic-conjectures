import Mathlib

/-!
# OEIS A000224 — even inputs, prime powers, and products of two primes

The definition below matches the pinned upstream snapshot
`problems/oeis-a000224/upstream/224_2322a58c.lean`: it counts distinct squares
modulo `n`, including zero. The upstream conjecture says, for `n > 1`, that
`(n * n) ≡ 1` modulo `A000224 n * (A000224 n - 1)` exactly when `n` is an odd
prime.

We prove the upstream equivalence for every `n > 1` that is even, a prime
power, or a product of two distinct primes:

* `even_not_conjecture_rhs`: no even `n > 1` satisfies the congruence;
* `two_mul_A000224_prime_pow_add_two`, `A000224_prime_pow_even`,
  `A000224_prime_pow_odd`: the square count modulo an odd prime power,
  `2(p+1)·A000224(p^e) = p^(e+1) + p + 2` (`e` even) or `p^(e+1) + 2p + 1`
  (`e` odd), obtained from the recursion
  `A000224(p^(e+2)) = A000224(p^e) + φ(p^(e+2))/2`;
* `odd_prime_conjecture_rhs`, `odd_prime_pow_not_conjecture_rhs`: every odd
  prime satisfies the congruence, and no `p^e` with `p` an odd prime and
  `e ≥ 2` does;
* `A000224_mul`, `odd_primes_mul_not_conjecture_rhs`: `A000224` is
  multiplicative on coprime arguments, and no product of two distinct odd
  primes satisfies the congruence (the last step is a finite check discharged
  by `decide`);
* `conjecture_prime_pow`, `conjecture_mul_primes`,
  `conjecture_of_primeFactorsList_length_le_two`, `counterexample_shape`: the
  upstream equivalence holds whenever `n` is a prime power, a product of two
  distinct primes, or has at most two prime factors counted with multiplicity;
  hence a counterexample is odd, not a prime power, and has `Ω(n) ≥ 3`.

The full upstream conjecture is not proved here.

Faithfulness: the `n = 0` convention, natural-number subtraction, and
`Nat.ModEq` statement are copied exactly; the `1 < n` hypotheses (implied by
the prime-power and two-prime hypotheses) exclude the boundary values from the
upstream conjecture. The left-hand side `n.Prime ∧ n ≠ 2` is the upstream one
verbatim. `n.primeFactorsList.length` is `Ω(n)`.
-/

namespace AgenticConjectures.OeisA000224

open Finset

/-- OEIS A000224: the number of distinct quadratic residues modulo `n`,
including zero. This is copied from the pinned upstream statement. -/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

/-- No even `n > 1` satisfies the congruence side of the A000224 conjecture. -/
theorem even_not_conjecture_rhs {n : ℕ} (_hn : 1 < n) (heven : Even n) :
    ¬ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  intro hmod
  have hd : 2 ∣ A000224 n * (A000224 n - 1) := Nat.two_dvd_mul_sub_one _
  have hmod2 : (n * n) ≡ 1 [MOD 2] := hmod.of_dvd hd
  have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd heven.two_dvd
  have hsqmod : (n * n) % 2 = 0 := by simp [Nat.mul_mod, hnmod]
  change (n * n) % 2 = 1 % 2 at hmod2
  rw [hsqmod] at hmod2
  norm_num at hmod2

/-! ## Counting squares modulo an odd prime power -/

/-- For a prime `p` and `0 < e`, `p` divides `k ^ 2 % p ^ e` exactly when it divides `k`. -/
private lemma prime_dvd_sq_mod_iff {p e k : ℕ} (hp : p.Prime) (he : 0 < e) :
    p ∣ k ^ 2 % p ^ e ↔ p ∣ k := by
  rw [Nat.dvd_mod_iff (dvd_pow_self p he.ne')]
  exact ⟨hp.dvd_of_dvd_pow, fun h => dvd_pow h two_ne_zero⟩

/-- The squares modulo `p ^ e` split into those divisible by `p` (squares of multiples of
`p`) and those prime to `p` (squares of units). -/
private lemma card_sq_split {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ((range (p ^ e)).image (fun k => k ^ 2 % p ^ e)).card =
      (((range (p ^ e)).filter (fun k => p ∣ k)).image (fun k => k ^ 2 % p ^ e)).card +
      (((range (p ^ e)).filter (fun k => ¬ p ∣ k)).image (fun k => k ^ 2 % p ^ e)).card := by
  rw [← card_union_of_disjoint, ← image_union, filter_union_filter_not_eq]
  rw [Finset.disjoint_left]
  simp only [mem_image, mem_filter, mem_range, not_exists, not_and]
  rintro _ ⟨k, ⟨_, hk⟩, rfl⟩ j ⟨_, hj⟩ hjk
  exact hj ((prime_dvd_sq_mod_iff hp he).mp (hjk ▸ (prime_dvd_sq_mod_iff hp he).mpr hk))

/-- Modulo an odd prime power, two units with the same square agree up to sign. -/
private lemma eq_or_add_eq_of_sq_mod_eq {p e k l : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : k < p ^ e) (hl : l < p ^ e) (hpk : ¬ p ∣ k) (hpl : ¬ p ∣ l)
    (h : k ^ 2 % p ^ e = l ^ 2 % p ^ e) : k = l ∨ k + l = p ^ e := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ^ e ∣ ((l : ℤ) - k) * ((l : ℤ) + k) := by
    have h' := Nat.modEq_iff_dvd.mp h
    push_cast at h'
    rw [show ((l : ℤ) - k) * ((l : ℤ) + k) = (l : ℤ) ^ 2 - (k : ℤ) ^ 2 by ring]
    exact h'
  by_cases hsub : (p : ℤ) ∣ (l : ℤ) - k
  · have hadd : ¬ (p : ℤ) ∣ (l : ℤ) + k := by
      intro hadd
      have h2l : (p : ℤ) ∣ 2 * (l : ℤ) := by
        have := dvd_add hsub hadd
        rwa [show (l : ℤ) - k + (l + k) = 2 * l by ring] at this
      rcases hpZ.dvd_or_dvd h2l with h2 | hl'
      · have : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact hpl (by exact_mod_cast hl')
    have hcop : IsCoprime ((p : ℤ) ^ e) ((l : ℤ) + k) :=
      ((Prime.coprime_iff_not_dvd hpZ).mpr hadd).pow_left
    have h1 : (p : ℤ) ^ e ∣ (l : ℤ) - k := hcop.dvd_of_dvd_mul_right hdvd
    left
    have hmod : k ≡ l [MOD p ^ e] := Nat.modEq_iff_dvd.mpr (by push_cast; exact h1)
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at hmod
  · have hcop : IsCoprime ((p : ℤ) ^ e) ((l : ℤ) - k) :=
      ((Prime.coprime_iff_not_dvd hpZ).mpr hsub).pow_left
    have h1 : (p : ℤ) ^ e ∣ (l : ℤ) + k := hcop.dvd_of_dvd_mul_left hdvd
    right
    have hnat : p ^ e ∣ k + l := by
      have : ((p ^ e : ℕ) : ℤ) ∣ ((k + l : ℕ) : ℤ) := by push_cast; rwa [add_comm]
      exact Int.natCast_dvd_natCast.mp this
    obtain ⟨c, hc⟩ := hnat
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hpk (dvd_zero p))
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · rfl
      · nlinarith
    rw [hc, hc1, mul_one]

/-- Squaring is two-to-one on the units modulo an odd prime power, so there are
`φ(p ^ e) / 2` unit squares. -/
private lemma two_mul_card_unit_sq {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) :
    2 * (((range (p ^ e)).filter (fun k => ¬ p ∣ k)).image (fun k => k ^ 2 % p ^ e)).card =
      p ^ (e - 1) * (p - 1) := by
  have hUcard : ((range (p ^ e)).filter (fun k => ¬ p ∣ k)).card = p ^ (e - 1) * (p - 1) := by
    rw [← Nat.totient_prime_pow hp he, Nat.totient]
    congr 1
    ext k
    simp only [mem_filter, mem_range]
    rw [Nat.coprime_pow_left_iff he, hp.coprime_iff_not_dvd]
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  rw [← hUcard, card_eq_sum_card_image (fun k => k ^ 2 % p ^ e)
    ((range (p ^ e)).filter (fun k => ¬ p ∣ k)), sum_const_nat (m := 2), mul_comm]
  intro s hs
  obtain ⟨k0, hk0U, rfl⟩ := mem_image.mp hs
  have hk0 : k0 < p ^ e := mem_range.mp (mem_filter.mp hk0U).1
  have hpk0 : ¬ p ∣ k0 := (mem_filter.mp hk0U).2
  have hk0pos : 0 < k0 := Nat.pos_of_ne_zero (by rintro rfl; exact hpk0 (dvd_zero p))
  have hfib : ((range (p ^ e)).filter (fun k => ¬ p ∣ k)).filter
      (fun k => k ^ 2 % p ^ e = k0 ^ 2 % p ^ e) = {k0, p ^ e - k0} := by
    ext k
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hk, hpk⟩, hkk⟩
      rcases eq_or_add_eq_of_sq_mod_eq hp hp2 hk hk0 hpk hpk0 hkk with h | h
      · exact Or.inl h
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨hk0, hpk0⟩, rfl⟩
      · refine ⟨⟨by omega, ?_⟩, ?_⟩
        · intro hdvd
          apply hpk0
          have := Nat.dvd_sub (dvd_pow_self p he.ne') hdvd
          rwa [Nat.sub_sub_self hk0.le] at this
        · show (p ^ e - k0) ^ 2 ≡ k0 ^ 2 [MOD p ^ e]
          apply Nat.modEq_iff_dvd.mpr
          push_cast [Nat.cast_sub hk0.le]
          exact ⟨2 * k0 - p ^ e, by ring⟩
  rw [hfib, card_pair]
  intro h
  obtain ⟨m, hm⟩ := hodd
  omega

/-- The squares modulo `p ^ (e + 2)` divisible by `p` are `p ^ 2` times the squares
modulo `p ^ e`. -/
private lemma image_sq_dvd_eq {p e : ℕ} (hp : p.Prime) :
    ((range (p ^ (e + 2))).filter (fun k => p ∣ k)).image (fun k => k ^ 2 % p ^ (e + 2)) =
      ((range (p ^ e)).image (fun j => j ^ 2 % p ^ e)).image (fun t => p ^ 2 * t) := by
  have hmod : ∀ j, (p * j) ^ 2 % p ^ (e + 2) = p ^ 2 * (j ^ 2 % p ^ e) := by
    intro j
    rw [mul_pow, pow_add, mul_comm (p ^ e) (p ^ 2), Nat.mul_mod_mul_left]
  ext s
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨k, ⟨hk, j, rfl⟩, rfl⟩
    refine ⟨j ^ 2 % p ^ e, ⟨j % p ^ e, Nat.mod_lt _ (pow_pos hp.pos e), ?_⟩, (hmod j).symm⟩
    rw [← Nat.pow_mod]
  · rintro ⟨t, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨p * j, ⟨?_, dvd_mul_right p j⟩, hmod j⟩
    calc p * j < p * p ^ e := Nat.mul_lt_mul_of_pos_left hj hp.pos
      _ = p ^ (e + 1) := by ring
      _ ≤ p ^ (e + 2) := Nat.pow_le_pow_right hp.pos (by omega)

private lemma card_sq_dvd {p e : ℕ} (hp : p.Prime) :
    (((range (p ^ (e + 2))).filter (fun k => p ∣ k)).image
      (fun k => k ^ 2 % p ^ (e + 2))).card = A000224 (p ^ e) := by
  rw [image_sq_dvd_eq hp,
    card_image_of_injective _ (mul_right_injective₀ (pow_ne_zero 2 hp.ne_zero)),
    A000224, if_neg (pow_ne_zero _ hp.ne_zero)]

/-- The recursion `A000224 (p ^ (e + 2)) = A000224 (p ^ e) + φ(p ^ (e + 2)) / 2` for an odd
prime `p`, written without division. -/
theorem two_mul_A000224_prime_pow_add_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    2 * A000224 (p ^ (e + 2)) = p ^ (e + 1) * (p - 1) + 2 * A000224 (p ^ e) := by
  rw [A000224, if_neg (pow_ne_zero _ hp.ne_zero), card_sq_split hp (by omega), card_sq_dvd hp,
    mul_add, two_mul_card_unit_sq hp hp2 (by omega), show e + 2 - 1 = e + 1 by omega]
  ring

/-- For an odd prime `p`, `A000224 p = (p + 1) / 2`. -/
theorem two_mul_A000224_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * A000224 p = p + 1 := by
  have h0 : ((range (p ^ 1)).filter (fun k => p ∣ k)).image (fun k => k ^ 2 % p ^ 1) = {0} := by
    ext s
    simp only [pow_one, mem_image, mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨k, ⟨hk, hdvd⟩, rfl⟩
      rw [Nat.eq_zero_of_dvd_of_lt hdvd hk]
      simp
    · rintro rfl
      exact ⟨0, ⟨hp.pos, dvd_zero p⟩, by simp⟩
  have hsplit := card_sq_split hp one_pos
  have hunit := two_mul_card_unit_sq hp hp2 one_pos
  rw [h0, card_singleton] at hsplit
  simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at hsplit hunit
  rw [A000224, if_neg hp.ne_zero, hsplit]
  have := hp.one_le
  omega

/-- Closed form of `A000224 (p ^ e)` for an odd prime `p` and even `e`. -/
theorem A000224_prime_pow_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    2 * (p + 1) * A000224 (p ^ (2 * k)) = p ^ (2 * k + 1) + p + 2 := by
  induction k with
  | zero => simp [A000224]; ring
  | succ k ih =>
    have h := two_mul_A000224_prime_pow_add_two hp hp2 (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    zify [hp.one_le] at h ih ⊢
    linear_combination ((p : ℤ) + 1) * h + ih

/-- Closed form of `A000224 (p ^ e)` for an odd prime `p` and odd `e`. -/
theorem A000224_prime_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    2 * (p + 1) * A000224 (p ^ (2 * k + 1)) = p ^ (2 * k + 2) + 2 * p + 1 := by
  induction k with
  | zero =>
    have := two_mul_A000224_prime hp hp2
    simp only [mul_zero, zero_add, pow_one]
    nlinarith
  | succ k ih =>
    have h := two_mul_A000224_prime_pow_add_two hp hp2 (2 * k + 1)
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
    zify [hp.one_le] at h ih ⊢
    linear_combination ((p : ℤ) + 1) * h + ih

/-! ## Prime powers -/

/-- Every odd prime satisfies the congruence (with quotient `4`). -/
theorem odd_prime_conjecture_rhs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p * p) ≡ 1 [MOD A000224 p * (A000224 p - 1)] := by
  have h := two_mul_A000224_prime hp hp2
  obtain ⟨b, hb⟩ : ∃ b, A000224 p = b + 1 := ⟨A000224 p - 1, by omega⟩
  rw [hb, Nat.add_sub_cancel]
  have hpb : p = 2 * b + 1 := by omega
  refine ((Nat.modEq_iff_dvd' (by nlinarith [hp.one_le])).mpr ⟨4, ?_⟩).symm
  rw [hpb]
  ring_nf
  omega

/-- No power `p ^ e` of an odd prime with `e ≥ 2` satisfies the congruence. -/
theorem odd_prime_pow_not_conjecture_rhs {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 2 ≤ e) :
    ¬ (p ^ e * p ^ e) ≡ 1 [MOD A000224 (p ^ e) * (A000224 (p ^ e) - 1)] := by
  intro hmod
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `e` even: `p ∣ A000224 (p ^ e) - 1`, which is incompatible with the congruence.
    have hform := A000224_prime_pow_even hp hp2 k
    rw [show 2 * k = e by omega] at hform
    obtain ⟨d, hd⟩ : ∃ d, A000224 (p ^ e) = d + 1 :=
      ⟨A000224 (p ^ e) - 1, by
        have : A000224 (p ^ e) ≠ 0 := by rintro h; rw [h] at hform; simp at hform
        omega⟩
    rw [hd, Nat.add_sub_cancel] at hmod
    rw [hd] at hform
    have h2 : 2 * (p + 1) * d + p = p ^ (e + 1) := by linarith
    have hpd2 : p ∣ 2 * (p + 1) * d :=
      (Nat.dvd_add_left (dvd_refl p)).mp (h2 ▸ dvd_pow_self p (by omega))
    have hpd : p ∣ d := by
      rcases hp.dvd_mul.mp hpd2 with h | h
      · rcases hp.dvd_mul.mp h with h' | h'
        · have := Nat.le_of_dvd (by norm_num) h'; omega
        · have := (Nat.dvd_add_right (dvd_refl p)).mp h'
          exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      · exact h
    have hmodp : p ^ e * p ^ e ≡ 1 [MOD p] := hmod.of_dvd (hpd.mul_left _)
    have h0 : p ^ e * p ^ e % p = 0 :=
      Nat.mod_eq_zero_of_dvd ((dvd_pow_self p (by omega)).mul_right _)
    unfold Nat.ModEq at hmodp
    rw [h0, Nat.mod_eq_of_lt hp.one_lt] at hmodp
    exact absurd hmodp (by norm_num)
  · -- `e` odd: `A000224 (p ^ e) - 1` divides `p ^ 2 - 1` but is larger than it.
    have hk1 : 1 ≤ k := by omega
    have hform := A000224_prime_pow_odd hp hp2 k
    rw [← hk] at hform
    obtain ⟨d, hd⟩ : ∃ d, A000224 (p ^ e) = d + 1 :=
      ⟨A000224 (p ^ e) - 1, by
        have : A000224 (p ^ e) ≠ 0 := by rintro h; rw [h] at hform; simp at hform
        omega⟩
    rw [hd, Nat.add_sub_cancel] at hmod
    rw [hd] at hform
    have h2 : 2 * (p + 1) * d + 1 = p ^ (2 * k + 2) := by linarith
    have hmodd : p ^ e * p ^ e ≡ 1 [MOD d] := hmod.of_dvd (dvd_mul_left d _)
    have hX : p ^ (2 * k + 2) ≡ 1 [MOD d] :=
      ((Nat.modEq_iff_dvd' (by omega)).mpr (Dvd.intro_left (2 * (p + 1)) (by omega))).symm
    have hsplit : p ^ e * p ^ e = p ^ (2 * k) * p ^ (2 * k + 2) := by rw [hk]; ring
    rw [hsplit] at hmodd
    have h3 : p ^ (2 * k) ≡ 1 [MOD d] := by
      have := (hX.mul_left (p ^ (2 * k))).symm.trans hmodd
      rwa [mul_one] at this
    have h4 : p ^ 2 ≡ 1 [MOD d] := by
      have h5 : p ^ (2 * k + 2) ≡ p ^ 2 * 1 [MOD d] := by
        rw [show p ^ (2 * k + 2) = p ^ 2 * p ^ (2 * k) by ring]
        exact h3.mul_left _
      rw [mul_one] at h5
      exact h5.symm.trans hX
    have hp2pos : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have hdvd : d ∣ p ^ 2 - 1 := (Nat.modEq_iff_dvd' hp2pos).mp h4.symm
    have hdle : d ≤ p ^ 2 - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hp.one_lt)) hdvd
    have hX4 : p ^ 4 ≤ p ^ (2 * k + 2) := Nat.pow_le_pow_right hp.pos (by omega)
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    have hdle' : d + 1 ≤ (q + 3) ^ 2 := by omega
    nlinarith [Nat.mul_le_mul_left (2 * q + 8) hdle', Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3),
      Nat.zero_le (q ^ 2)]

/-- The upstream equivalence holds at every prime power `n = p ^ e`, `e ≥ 1`. -/
theorem conjecture_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ((p ^ e).Prime ∧ p ^ e ≠ 2) ↔
      (p ^ e * p ^ e) ≡ 1 [MOD A000224 (p ^ e) * (A000224 (p ^ e) - 1)] := by
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨fun ⟨hpr, hne⟩ => ?_, fun h => ?_⟩
    · obtain rfl := hpr.eq_one_of_pow
      exact absurd rfl hne
    · exact absurd h (even_not_conjecture_rhs (Nat.one_lt_two_pow he.ne')
        (Nat.even_pow.mpr ⟨even_two, he.ne'⟩))
  · rcases Nat.lt_or_ge e 2 with he2 | he2
    · obtain rfl : e = 1 := by omega
      simp only [pow_one]
      exact ⟨fun _ => odd_prime_conjecture_rhs hp hp2, fun _ => ⟨hp, hp2⟩⟩
    · refine ⟨fun ⟨hpr, _⟩ => ?_, fun h => ?_⟩
      · have := hpr.eq_one_of_pow
        omega
      · exact absurd h (odd_prime_pow_not_conjecture_rhs hp hp2 he2)

/-! ## Products of two distinct primes -/

/-- `A000224` is multiplicative on coprime positive arguments (Chinese remainder theorem). -/
theorem A000224_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    A000224 (m * n) = A000224 m * A000224 n := by
  rw [A000224, if_neg (Nat.mul_ne_zero hm.ne' hn.ne'), A000224, if_neg hm.ne', A000224,
    if_neg hn.ne', ← card_product]
  have hinj : Set.InjOn (fun s => (s % m, s % n))
      ((range (m * n)).image (fun k => k ^ 2 % (m * n)) : Set ℕ) := by
    intro s hs t ht hst
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hs ht
    obtain ⟨k, -, rfl⟩ := hs
    obtain ⟨l, -, rfl⟩ := ht
    simp only [Prod.mk.injEq] at hst
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hmn).mp hst).eq_of_lt_of_lt
      (Nat.mod_lt _ (Nat.mul_pos hm hn)) (Nat.mod_lt _ (Nat.mul_pos hm hn))
  rw [← card_image_of_injOn hinj]
  congr 1
  ext ⟨x, y⟩
  simp only [mem_image, mem_product, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨s, ⟨k, -, rfl⟩, rfl, rfl⟩
    refine ⟨⟨k % m, Nat.mod_lt _ hm, ?_⟩, ⟨k % n, Nat.mod_lt _ hn, ?_⟩⟩
    · rw [← Nat.pow_mod, Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
    · rw [← Nat.pow_mod, Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
  · rintro ⟨⟨i, -, rfl⟩, ⟨j, -, rfl⟩⟩
    obtain ⟨c, hci, hcj⟩ := Nat.chineseRemainder hmn i j
    refine ⟨(c % (m * n)) ^ 2 % (m * n),
      ⟨c % (m * n), Nat.mod_lt _ (Nat.mul_pos hm hn), rfl⟩, ?_, ?_⟩
    · have h1 : (c % (m * n)) ^ 2 % (m * n) ≡ i ^ 2 [MOD m] :=
        ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).pow 2)).of_dvd (dvd_mul_right m n)
          |>.trans (hci.pow 2)
      exact h1
    · have h1 : (c % (m * n)) ^ 2 % (m * n) ≡ j ^ 2 [MOD n] :=
        ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).pow 2)).of_dvd (dvd_mul_left n m)
          |>.trans (hcj.pow 2)
      exact h1

/-- The finite check closing the two-prime case: for `2 ≤ a ≤ 31` and every divisor
`b = 4a(a-1)/c > a` of `4a(a-1)`, `((2a-1)(2b-1))^2 ≢ 1 (mod ab - 1)`. -/
private theorem pq_finite_check : ∀ a < 32, ∀ c < 4 * a, 2 ≤ a → 4 * a * (a - 1) % c = 0 →
    a < 4 * a * (a - 1) / c →
    ¬ ((2 * a - 1) * (2 * (4 * a * (a - 1) / c) - 1)) *
        ((2 * a - 1) * (2 * (4 * a * (a - 1) / c) - 1)) ≡ 1
        [MOD a * (4 * a * (a - 1) / c) - 1] := by
  decide

/-- The arithmetic core of the two-prime case, with `p = 2a - 1`, `q = 2b - 1`, and
`A000224 (p * q) = a * b`. -/
private lemma core_pq {a b : ℕ} (ha : 2 ≤ a) (hab : a < b)
    (h : (2 * a - 1) * (2 * b - 1) * ((2 * a - 1) * (2 * b - 1)) ≡ 1
      [MOD a * b * (a * b - 1)]) : False := by
  -- Step 1: `b ∣ 4a(a-1)`, since `2b - 1 ≡ -1 (mod b)`.
  have hbdvd : b ∣ 4 * a * (a - 1) := by
    have hb : (2 * a - 1) * (2 * b - 1) * ((2 * a - 1) * (2 * b - 1)) ≡ 1 [MOD b] :=
      h.of_dvd (Dvd.intro (a * (a * b - 1)) (by ring))
    have hq2 : (2 * b - 1) * (2 * b - 1) ≡ 1 [MOD b] := by
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have e : (2 * (b' + 1) - 1) * (2 * (b' + 1) - 1) = 1 + (b' + 1) * (4 * b') := by
        rw [show 2 * (b' + 1) - 1 = 2 * b' + 1 by omega]; ring
      rw [e]
      exact Nat.add_mul_mod_self_left _ _ _
    have hp2 : (2 * a - 1) * (2 * a - 1) ≡ 1 [MOD b] := by
      have := hq2.mul_left ((2 * a - 1) * (2 * a - 1))
      rw [mul_one, show (2 * a - 1) * (2 * a - 1) * ((2 * b - 1) * (2 * b - 1)) =
        (2 * a - 1) * (2 * b - 1) * ((2 * a - 1) * (2 * b - 1)) by ring] at this
      exact this.symm.trans hb
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have e : (2 * (a' + 1) - 1) * (2 * (a' + 1) - 1) = 4 * (a' + 1) * a' + 1 := by
      rw [show 2 * (a' + 1) - 1 = 2 * a' + 1 by omega]; ring
    rw [e] at hp2
    have := (Nat.modEq_iff_dvd' (by omega)).mp hp2.symm
    rwa [Nat.add_sub_cancel, ← Nat.add_sub_cancel a' 1] at this
  -- Step 2: `a ≤ 31`, since otherwise `15 R(R-1) < n^2 - 1 < 16 R(R-1)` with `R = ab`.
  have ha31 : a ≤ 31 := by
    by_contra hbig
    obtain ⟨x, rfl⟩ : ∃ x, a = x + 32 := ⟨a - 32, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, b = y + 32 := ⟨b - 32, by omega⟩
    rw [show 2 * (x + 32) - 1 = 2 * x + 63 by omega, show 2 * (y + 32) - 1 = 2 * y + 63 by omega,
      show (x + 32) * (y + 32) - 1 = x * y + 32 * x + 32 * y + 1023 by ring_nf; omega] at h
    obtain ⟨K, hK⟩ :=
      (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr (by positivity))).mp h.symm
    have hlo : (2 * x + 63) * (2 * y + 63) * ((2 * x + 63) * (2 * y + 63)) =
        15 * ((x + 32) * (y + 32) * (x * y + 32 * x + 32 * y + 1023)) + 1 +
          (x ^ 2 * y ^ 2 + 48 * x ^ 2 * y + 516 * x ^ 2 + 48 * x * y ^ 2 + 2079 * x * y +
            17628 * x + 516 * y ^ 2 + 17628 * y + 39680) := by ring
    have hhi : (2 * x + 63) * (2 * y + 63) * ((2 * x + 63) * (2 * y + 63)) +
        (16 * x ^ 2 * y + 508 * x ^ 2 + 16 * x * y ^ 2 + 2016 * x * y + 47876 * x +
          508 * y ^ 2 + 47876 * y + 1007872) =
        16 * ((x + 32) * (y + 32) * (x * y + 32 * x + 32 * y + 1023)) + 1 := by ring
    rcases Nat.lt_or_ge K 16 with hK16 | hK16
    · have := Nat.mul_le_mul_left ((x + 32) * (y + 32) * (x * y + 32 * x + 32 * y + 1023))
        (show K ≤ 15 by omega)
      omega
    · have := Nat.mul_le_mul_left ((x + 32) * (y + 32) * (x * y + 32 * x + 32 * y + 1023)) hK16
      omega
  -- Step 3: the finite check.
  obtain ⟨c, hc⟩ := hbdvd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [mul_zero] at hc
      have : 0 < 4 * a * (a - 1) := Nat.mul_pos (by omega) (by omega)
      omega
    · exact hc0
  have hc4 : c < 4 * a := by
    by_contra hge
    have h1 : b * (4 * a) ≤ b * c := Nat.mul_le_mul_left b (by omega)
    have h2 : 4 * a * (a - 1) < b * (4 * a) := by
      calc 4 * a * (a - 1) < 4 * a * b := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = b * (4 * a) := by ring
    omega
  have hbc : 4 * a * (a - 1) / c = b := by rw [hc, Nat.mul_div_cancel _ hc0]
  have hchk := pq_finite_check a (by omega) c hc4 ha (by rw [hc]; simp) (by rw [hbc]; exact hab)
  rw [hbc] at hchk
  exact hchk (h.of_dvd (dvd_mul_left _ _))

/-- No product of two distinct odd primes satisfies the congruence. -/
theorem odd_primes_mul_not_conjecture_rhs {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ¬ (p * q * (p * q)) ≡ 1 [MOD A000224 (p * q) * (A000224 (p * q) - 1)] := by
  wlog hlt : p < q generalizing p q
  · rw [mul_comm p q]
    exact this hq hp hq2 hp2 (Ne.symm hpq) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hpq))
  intro hmod
  have hA := A000224_mul hp.pos hq.pos ((Nat.coprime_primes hp hq).mpr hpq)
  have ha := two_mul_A000224_prime hp hp2
  have hb := two_mul_A000224_prime hq hq2
  have hp3 := hp.two_le
  rw [hA] at hmod
  generalize A000224 p = a at ha hmod
  generalize A000224 q = b at hb hmod
  rw [show p = 2 * a - 1 by omega, show q = 2 * b - 1 by omega] at hmod
  exact core_pq (by omega) (by omega) hmod

/-- The upstream equivalence holds at every product `n = p * q` of two distinct primes. -/
theorem conjecture_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p * q).Prime ∧ p * q ≠ 2) ↔
      (p * q * (p * q)) ≡ 1 [MOD A000224 (p * q) * (A000224 (p * q) - 1)] := by
  refine ⟨fun ⟨hpr, _⟩ => absurd hpr (Nat.not_prime_mul hp.ne_one hq.ne_one), fun h => ?_⟩
  exfalso
  have h1 : 1 < p * q := Nat.one_lt_mul_iff.mpr ⟨hp.pos, hq.pos, Or.inl hp.one_lt⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact even_not_conjecture_rhs h1 (even_two.mul_right q) h
  by_cases hq2 : q = 2
  · subst hq2
    exact even_not_conjecture_rhs h1 (even_two.mul_left p) h
  exact odd_primes_mul_not_conjecture_rhs hp hq hp2 hq2 hpq h

/-! ## At most two prime factors -/

/-- The upstream equivalence holds for every `n > 1` with `Ω(n) ≤ 2`. -/
theorem conjecture_of_primeFactorsList_length_le_two {n : ℕ} (hn : 1 < n)
    (hΩ : n.primeFactorsList.length ≤ 2) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  have hprod := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  have hprime : ∀ p ∈ n.primeFactorsList, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList hp
  rcases hl : n.primeFactorsList with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · rw [hl, List.prod_nil] at hprod
    omega
  · rw [hl, List.prod_singleton] at hprod
    subst hprod
    simpa using conjecture_prime_pow (hprime p (by simp [hl])) one_pos
  · rw [hl, List.prod_cons, List.prod_singleton] at hprod
    subst hprod
    have hp := hprime p (by simp [hl])
    have hq := hprime q (by simp [hl])
    by_cases hpq : p = q
    · subst hpq
      rw [← sq]
      exact conjecture_prime_pow hp two_pos
    · exact conjecture_mul_primes hp hq hpq
  · rw [hl] at hΩ
    simp at hΩ

/-- A counterexample `n > 1` to the upstream equivalence is odd, is not a prime power, and has
`Ω(n) ≥ 3`. -/
theorem counterexample_shape {n : ℕ} (hn : 1 < n)
    (hfail : ¬ ((n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)])) :
    Odd n ∧ ¬ IsPrimePow n ∧ 3 ≤ n.primeFactorsList.length := by
  refine ⟨?_, fun hpp => ?_, ?_⟩
  · rcases Nat.even_or_odd n with he | ho
    · exact absurd ⟨fun ⟨hpr, hne⟩ => absurd (hpr.even_iff.mp he) hne,
        fun h => absurd h (even_not_conjecture_rhs hn he)⟩ hfail
    · exact ho
  · obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    exact hfail (conjecture_prime_pow hp he)
  · by_contra h
    exact hfail (conjecture_of_primeFactorsList_length_le_two hn (by omega))

end AgenticConjectures.OeisA000224
