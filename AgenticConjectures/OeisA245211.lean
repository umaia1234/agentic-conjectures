import Mathlib

/-!
# OEIS A245211 — prime powers and squarefree semiprimes

[OEIS A245211](https://oeis.org/A245211) defines

`a(n) = ∑_{d ∣ n, d < n} d · τ(d)`,

where `τ(d)` is the number of positive divisors of `d`, and conjectures that
`n = 21` is the only positive solution of `a(n) = n`.

## Correspondence with the upstream snapshot

* `A` is the sum over `n.properDivisors`, which is mathlib's set of positive
  divisors strictly less than `n`. That is the displayed OEIS sum, including
  the empty sum `A 1 = 0`. The upstream snapshot
  `problems/oeis-a245211/upstream/245211_cbf46b82.lean` instead subtracts the
  final term `n * τ(n)` from the sum over all positive divisors.
  `A_eq_full_sub` proves the two expressions agree for every `n`, so there is
  no subtraction-truncation gap: at `n = 0` both sides are `0`.
* `statement` is the upstream conjecture `oeis_245211_conjecture_0` copied
  term for term: `∀ n, 0 < n → (A n = n ↔ n = 21)`. The positive lower bound
  matches the OEIS indexing. It is essential: `A 0 = 0`, so the equivalence
  fails if `n = 0` is admitted. `statement` is not proved here.
* `τ` is `Finset.card` of `Nat.divisors`. Every quantity is a natural number.
  The only integer cast is the algebraic identity relating
  `1 + 2p + 2q = pq` to `(p - 2)(q - 2) = 5`, and that identity is pulled
  back to `ℕ`.

## What is proved

* `A_21`: `21` is a solution.
* `prime_power_ne`: no prime power `p ^ k` with `k ≥ 1` is a solution.
* `squarefree_semiprime_iff`: if `p` and `q` are distinct primes, then
  `A (p * q) = p * q` if and only if `p * q = 21`.
* `divisors_card_lt_of_solution`: every positive solution satisfies
  `τ(n / p) < p` for each prime divisor `p`. This is the strict single-term
  bound used to derive inequality (2) in `problems/oeis-a245211/README.md`.
  The rewritten shape `p > v_p(n) · τ(n) / (v_p(n) + 1)` is not formalized
  separately.

The coprimality-to-`2310` reduction, the squarefree three-prime and
even-`ω` exclusions, nonsquarefree numbers with two or more prime factors,
and the finite searches remain outside this module.
-/

namespace AgenticConjectures.OeisA245211

open Nat Finset

/-- OEIS A245211: `∑ d·τ(d)` over positive proper divisors of `n`. -/
def A (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d * d.divisors.card

/-- The upstream subtraction form agrees with `A`, including at `n = 0`. -/
theorem A_eq_full_sub (n : ℕ) :
    A n = (∑ d ∈ n.divisors, d * d.divisors.card) - n * n.divisors.card := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp [A, divisors_zero, properDivisors_zero]
  · have hsum : ∑ d ∈ n.divisors, d * d.divisors.card =
        ∑ d ∈ n.properDivisors, d * d.divisors.card + n * n.divisors.card := by
      conv_lhs => rw [← insert_self_properDivisors hn]
      rw [sum_insert self_notMem_properDivisors, add_comm]
    rw [hsum, A, Nat.add_sub_cancel]

/-- The OEIS conjecture, still open: the only positive solution is `21`. -/
def statement : Prop :=
  ∀ n : ℕ, 0 < n → (A n = n ↔ n = 21)

theorem A_one : A 1 = 0 := by
  simp [A, properDivisors_one]

lemma divisors_card_prime_pow {p k : ℕ} (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [divisors_prime_pow hp, card_map, card_range]

lemma A_prime_pow {p k : ℕ} (hp : p.Prime) :
    A (p ^ k) = ∑ j ∈ range k, (j + 1) * p ^ j := by
  rw [A, properDivisors_prime_pow hp, sum_map]
  refine sum_congr rfl ?_
  intro j _hj
  simp only [Function.Embedding.coeFn_mk]
  rw [divisors_card_prime_pow hp, mul_comm]

/-- Weighted geometric sum: `∑_{j < k} (p - 1) p^j + 1 = p^k` for `p ≥ 1`. -/
private lemma geom_sum_succ (p k : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ range k, (p - 1) * p ^ j) + 1 = p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, add_assoc, add_comm ((p - 1) * p ^ k) 1, ← add_assoc, ih]
    have hcoef : 1 + (p - 1) = p := Nat.add_sub_of_le hp
    calc
      p ^ k + (p - 1) * p ^ k = (1 + (p - 1)) * p ^ k := by rw [add_mul, one_mul]
      _ = p * p ^ k := by rw [hcoef]
      _ = p ^ (k + 1) := by rw [pow_succ']

theorem prime_power_ne {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    A (p ^ k) ≠ p ^ k := by
  rw [A_prime_pow hp]
  by_cases hpk : p ≤ k
  · have hk2 : 2 ≤ k := by
      have := hp.two_le
      omega
    have hne : (0 : ℕ) ≠ k - 1 := by omega
    have hsub : ({0, k - 1} : Finset ℕ) ⊆ range k := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_range.mpr (by omega)
      · exact mem_range.mpr (by omega)
    have hle := sum_le_sum_of_subset (f := fun j : ℕ => (j + 1) * p ^ j) hsub
    rw [sum_pair hne] at hle
    have hleft : (0 + 1) * p ^ 0 + ((k - 1) + 1) * p ^ (k - 1) =
        1 + k * p ^ (k - 1) := by
      have hk1 : (k - 1) + 1 = k := by omega
      simp [pow_zero, hk1]
    rw [hleft] at hle
    have hpow : p * p ^ (k - 1) = p ^ k := by
      cases k with
      | zero => omega
      | succ k => simp [Nat.pow_succ']
    have hmul : p * p ^ (k - 1) ≤ k * p ^ (k - 1) :=
      Nat.mul_le_mul_right _ hpk
    have hgt : p ^ k < 1 + k * p ^ (k - 1) := by
      rw [← hpow]
      omega
    have hlt : p ^ k < ∑ j ∈ range k, (j + 1) * p ^ j := lt_of_lt_of_le hgt hle
    omega
  · have hle : ∑ j ∈ range k, (j + 1) * p ^ j ≤ ∑ j ∈ range k, (p - 1) * p ^ j := by
      refine sum_le_sum ?_
      intro j hj
      have hjk : j < k := by simpa [mem_range] using hj
      have hcoef : j + 1 ≤ p - 1 := by
        have := hp.two_le
        have hlt : k < p := lt_of_not_ge hpk
        omega
      exact Nat.mul_le_mul_right _ hcoef
    have hgeom : (∑ j ∈ range k, (p - 1) * p ^ j) + 1 = p ^ k :=
      geom_sum_succ p k hp.one_lt.le
    have hlt : ∑ j ∈ range k, (j + 1) * p ^ j < p ^ k := by omega
    exact _root_.ne_of_lt hlt

lemma mem_divisors_two_primes {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : d ∣ p * q) : d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  by_cases hpd : p ∣ d
  · obtain ⟨d', rfl⟩ := hpd
    have hd' : d' ∣ q := (mul_dvd_mul_iff_left hp.ne_zero).mp hdvd
    rcases (dvd_prime hq).mp hd' with rfl | rfl
    · exact Or.inr (Or.inl (mul_one p))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · have hdq : d ∣ q :=
      ((hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_mul_left).mp hdvd
    rcases (dvd_prime hq).mp hdq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))

lemma properDivisors_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p * q).properDivisors = {1, p, q} := by
  ext d
  simp only [mem_properDivisors, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hdvd, hlt⟩
    rcases mem_divisors_two_primes hp hq hdvd with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h (_root_.ne_of_lt hlt)
  · intro hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨one_dvd _, by nlinarith [hp.two_le, hq.two_le]⟩
    · exact ⟨dvd_mul_right _ _, by nlinarith [hp.pos, hq.two_le]⟩
    · exact ⟨dvd_mul_left _ _, by nlinarith [hq.pos, hp.two_le]⟩

lemma A_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    A (p * q) = 1 + 2 * p + 2 * q := by
  have hcard1 : (1 : ℕ).divisors.card = 1 := by simp [divisors_one]
  have hcardp : p.divisors.card = 2 := by
    rw [hp.divisors, card_insert_of_notMem (by simp [Ne.symm hp.ne_one]), card_singleton]
  have hcardq : q.divisors.card = 2 := by
    rw [hq.divisors, card_insert_of_notMem (by simp [Ne.symm hq.ne_one]), card_singleton]
  have hnot1 : 1 ∉ insert p ({q} : Finset ℕ) := by
    simp [Ne.symm hp.ne_one, Ne.symm hq.ne_one]
  have hnotp : p ∉ ({q} : Finset ℕ) := by simp [hne]
  rw [A, properDivisors_two_primes hp hq hne,
    show ({1, p, q} : Finset ℕ) = insert 1 (insert p {q}) from rfl,
    sum_insert hnot1, sum_insert hnotp, sum_singleton, hcard1, hcardp, hcardq]
  omega

lemma eq_iff_sub_mul_eq_five {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    1 + 2 * p + 2 * q = p * q ↔ (p - 2) * (q - 2) = 5 := by
  zify [hp, hq]
  constructor <;> intro h <;> linarith

theorem A_21 : A 21 = 21 := by
  have h := A_two_primes (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) (by decide)
  norm_num at h
  simpa using h

/-- A product of two distinct primes solves `A n = n` exactly for `n = 21`. -/
theorem squarefree_semiprime_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    A (p * q) = p * q ↔ p * q = 21 := by
  constructor
  · intro hsol
    rw [A_two_primes hp hq hne] at hsol
    have h5 : (p - 2) * (q - 2) = 5 :=
      (eq_iff_sub_mul_eq_five hp.two_le hq.two_le).mp hsol
    have hdvd : p - 2 ∣ 5 := ⟨q - 2, h5.symm⟩
    rcases (dvd_prime (by decide : Nat.Prime 5)).mp hdvd with hp1 | hp5
    · have hp3 : p = 3 := by omega
      have hq5 : q - 2 = 5 := by simpa [hp1] using h5
      have hq7 : q = 7 := by omega
      simp [hp3, hq7]
    · have hp7 : p = 7 := by omega
      have hq1 : q - 2 = 1 := by
        have : 5 * (q - 2) = 5 := by simpa [hp5, mul_comm] using h5
        omega
      have hq3 : q = 3 := by omega
      simp [hp7, hq3]
  · intro h
    calc
      A (p * q) = A 21 := by rw [h]
      _ = 21 := A_21
      _ = p * q := h.symm

/-- Every positive solution is strictly larger, at the complementary divisor,
than the divisor count of `n / p`. -/
theorem divisors_card_lt_of_solution {n p : ℕ} (hp : p.Prime) (hdiv : p ∣ n) (hn : 0 < n)
    (hA : A n = n) : (n / p).divisors.card < p := by
  classical
  have hn_eq : n = n / p * p := (Nat.div_mul_cancel hdiv).symm
  set d := n / p
  have hd_pos : 0 < d := by
    have hle : p ≤ n := le_of_dvd hn hdiv
    exact Nat.div_pos hle hp.pos
  have hd_lt : d < n := by
    simpa [d] using Nat.div_lt_self hn hp.one_lt
  have hd_mem : d ∈ n.properDivisors := by
    rw [mem_properDivisors]
    refine ⟨?_, hd_lt⟩
    rw [hn_eq]
    exact dvd_mul_right d p
  have hone_mem : 1 ∈ n.properDivisors :=
    (one_mem_properDivisors_iff_one_lt).mpr (by omega)
  by_cases hd1 : d = 1
  · have hn_p : n = p := by rw [hn_eq, hd1, one_mul]
    have hAp : A p = 1 := by simp [A, hp.properDivisors, divisors_one]
    rw [hn_p, hAp] at hA
    exact absurd hA (Ne.symm hp.ne_one)
  · have hne : (1 : ℕ) ≠ d := Ne.symm hd1
    have hsub : ({1, d} : Finset ℕ) ⊆ n.properDivisors := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hone_mem
      · exact hd_mem
    have hle := sum_le_sum_of_subset (f := fun x : ℕ => x * x.divisors.card) hsub
    rw [sum_pair hne] at hle
    have hcard1 : (1 : ℕ).divisors.card = 1 := by simp [divisors_one]
    rw [hcard1, one_mul] at hle
    have hleA : 1 + d * d.divisors.card ≤ A n := by simpa [A] using hle
    rw [hA, hn_eq] at hleA
    have : d * d.divisors.card < d * p := by omega
    exact lt_of_mul_lt_mul_left this hd_pos.le

end AgenticConjectures.OeisA245211
