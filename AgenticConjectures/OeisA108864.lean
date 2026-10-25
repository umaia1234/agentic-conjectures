import Mathlib

/-!
# OEIS A108864 — an odd term after 1155

OEIS A108864 lists the numbers whose perfect deficiency (OEIS A109883) is at
most 10, and its only comment asks: "Is 1155 the last odd number in this
sequence?"  The Formal Conjectures file `FormalConjectures/OEIS/108864.lean`
(snapshot in `problems/oeis-a108864/upstream/108864.lean`, commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`) formalizes the question as the
proposition `∀ n > 58, Even (a n)`, where `a n = Nat.nth A n` is 0-indexed,
so that `a 58 = 1155` is OEIS `a(59)`.

This module proves `¬ statement`, the negation of that exact proposition.
The odd number `815634435 = 3 * 5 * 7 * 11 * 547 * 1291` has
`σ(815634435) = 1631268864 = 2 * 815634435 - 6`.  For a number `n ≥ 2` whose
proper divisors sum to at most `n`, the greedy fold of `perfectDeficiency`
subtracts every proper divisor and skips `n` itself
(`perfectDeficiency_eq`), so `perfectDeficiency 815634435 = 6 ≤ 10`.  Hence
`815634435` is a term, and `Nat.nth_count` places it at index
`Nat.count A 815634435`.  That index exceeds 58 because the 59 explicit terms
`1, 2, …, 1155` (`firstTerms`) lie below the witness; their membership is
checked by kernel evaluation of the upstream fold (`decide +kernel`), while the
witness itself is never evaluated by the fold.

Upstream correspondence: `perfectDeficiency`, `A`, the `DecidablePred A`
instance, and `a` are copied term for term, under the same
`open Nat Finset Int`, and `statement` is the type of upstream
`OeisA108864.conjecture`.  The only changes are the ones needed to compile
without the Formal Conjectures utilities: `module`, `public import
FormalConjecturesUtil` and `@[expose] public section` became `import Mathlib`;
the namespace `OeisA108864` became `AgenticConjectures.OeisA108864`; the
`@[category …]`/`@[AMS …]` attributes and the five `test` theorems `a_0`–`a_4`
were dropped; and the `sorry`-terminated `theorem conjecture` became
`def statement : Prop`.  None of these changes affects a proposition.  The
subtraction `m - d` in the fold is truncated `ℕ` subtraction, but it only fires
under the guard `d ≤ m`, so it never truncates.
-/

namespace AgenticConjectures.OeisA108864

open Nat Finset Int

/-- Upstream definition, verbatim: the perfect deficiency of `n` (A109883),
the remainder after greedily subtracting from `n` its divisors in increasing
order, skipping any divisor larger than the current remainder. -/
def perfectDeficiency (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n

/-- Upstream definition, verbatim: membership in A108864. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

/-- Upstream instance, verbatim. -/
instance : DecidablePred A := by
  unfold A
  infer_instance

/-- Upstream definition, verbatim: the 0-indexed sequence, `a n = Nat.nth A n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-- The exact proposition of upstream `OeisA108864.conjecture`: every term after
`a 58 = 1155` is even. -/
def statement : Prop :=
  ∀ n > 58, Even (a n)

/-! ### The greedy fold on a deficient or perfect number -/

/-- If the proper divisors of `n` sum to at most `n`, then after the fold has
processed the candidates `0, …, k - 1` (with `k ≤ n`) it has subtracted exactly
the divisors of `n` below `k`. -/
theorem foldl_range_eq {n : ℕ} (h : ∑ d ∈ n.properDivisors, d ≤ n) :
    ∀ k ≤ n,
      (List.range k).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n =
        n - ∑ d ∈ Finset.range k, if d ∣ n then d else 0 := by
  have hS : (∑ d ∈ Finset.range n, if d ∣ n then d else 0) = ∑ d ∈ n.properDivisors, d := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [Nat.mem_properDivisors, and_comm]
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hle : (∑ d ∈ Finset.range (k + 1), if d ∣ n then d else 0) ≤ n :=
      calc (∑ d ∈ Finset.range (k + 1), if d ∣ n then d else 0)
          ≤ ∑ d ∈ Finset.range n, if d ∣ n then d else 0 :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hk)
        _ = ∑ d ∈ n.properDivisors, d := hS
        _ ≤ n := h
    rw [Finset.sum_range_succ] at hle
    rw [List.range_succ, List.foldl_append, ih (by omega), Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hd : k ∣ n
    · rw [if_pos hd] at hle
      rw [if_pos ⟨hd, by omega⟩, if_pos hd]
      omega
    · rw [if_neg (fun hc => hd hc.1), if_neg hd]
      simp

/-- **Key lemma.** For `n ≥ 2` whose proper divisors sum to at most `n` (that
is, `σ(n) ≤ 2n`), the perfect deficiency is `n - ∑ proper divisors = 2n - σ(n)`. -/
theorem perfectDeficiency_eq {n : ℕ} (hn : 2 ≤ n) (h : ∑ d ∈ n.properDivisors, d ≤ n) :
    perfectDeficiency n = n - ∑ d ∈ n.properDivisors, d := by
  have hS : (∑ d ∈ Finset.range n, if d ∣ n then d else 0) = ∑ d ∈ n.properDivisors, d := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [Nat.mem_properDivisors, and_comm]
  have hpos : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩)
  have hlt : ¬ n ≤ n - ∑ d ∈ n.properDivisors, d := by omega
  unfold perfectDeficiency
  rw [List.range_succ, List.foldl_append, foldl_range_eq h n le_rfl, hS]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [if_neg (fun hc => hlt hc.2)]

/-! ### The witness `815634435 = 3 * 5 * 7 * 11 * 547 * 1291` -/

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]

/-- `σ(815634435) = 1631268864 = 2 * 815634435 - 6`, by multiplicativity. -/
theorem sigma_witness : ArithmeticFunction.sigma 1 815634435 = 1631268864 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  rw [show (815634435 : ℕ) = 3 * 5 * 7 * 11 * 547 * 1291 by norm_num,
    hm.map_mul_of_coprime (m := 3 * 5 * 7 * 11 * 547) (n := 1291) (by norm_num),
    hm.map_mul_of_coprime (m := 3 * 5 * 7 * 11) (n := 547) (by norm_num),
    hm.map_mul_of_coprime (m := 3 * 5 * 7) (n := 11) (by norm_num),
    hm.map_mul_of_coprime (m := 3 * 5) (n := 7) (by norm_num),
    hm.map_mul_of_coprime (m := 3) (n := 5) (by norm_num),
    sigma_one_prime (by norm_num : Nat.Prime 3), sigma_one_prime (by norm_num : Nat.Prime 5),
    sigma_one_prime (by norm_num : Nat.Prime 7), sigma_one_prime (by norm_num : Nat.Prime 11),
    sigma_one_prime (by norm_num : Nat.Prime 547),
    sigma_one_prime (by norm_num : Nat.Prime 1291)]
  norm_num

theorem sum_properDivisors_witness :
    ∑ d ∈ (815634435 : ℕ).properDivisors, d = 815634429 := by
  have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 815634435)
  rw [← ArithmeticFunction.sigma_one_apply, sigma_witness] at h
  omega

theorem perfectDeficiency_witness : perfectDeficiency 815634435 = 6 := by
  rw [perfectDeficiency_eq (by norm_num) (by rw [sum_properDivisors_witness]; norm_num),
    sum_properDivisors_witness]

/-- The odd number `815634435` is a term of A108864. -/
theorem A_witness : A 815634435 :=
  ⟨by norm_num, by rw [perfectDeficiency_witness]; norm_num⟩

/-! ### The witness has index greater than 58 -/

/-- Fifty-nine terms of A108864 below the witness (by the OEIS data these are
OEIS `a(1)`–`a(59)`, but only their membership is used). -/
def firstTerms : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26, 28, 30, 32,
    40, 42, 44, 50, 52, 60, 64, 68, 72, 110, 120, 126, 128, 130, 136, 144, 150, 152, 180,
    184, 204, 228, 256, 315, 462, 496, 512, 528, 592, 656, 750, 884, 1012, 1024, 1155]

/-- Kernel evaluation of the upstream fold on each listed number. -/
theorem firstTerms_spec : firstTerms.Nodup ∧ ∀ x ∈ firstTerms, A x ∧ x < 815634435 := by
  decide +kernel

theorem count_witness : 58 < Nat.count A 815634435 := by
  obtain ⟨hnd, hmem⟩ := firstTerms_spec
  have hsub : firstTerms.toFinset ⊆ {x ∈ Finset.range 815634435 | A x} := by
    intro x hx
    obtain ⟨hA, hlt⟩ := hmem x (List.mem_toFinset.mp hx)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hA⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at hcard
  have hlen : firstTerms.length = 59 := rfl
  rw [Nat.count_eq_card_filter_range]
  omega

/-- The witness is the term of index `Nat.count A 815634435 > 58`. -/
theorem a_count_witness : a (Nat.count A 815634435) = 815634435 :=
  Nat.nth_count A_witness

/-- **Refutation of upstream `OeisA108864.conjecture`.**  The term of index
`Nat.count A 815634435 > 58` is the odd number `815634435`. -/
theorem not_statement : ¬ statement := by
  intro h
  have heven := h _ count_witness
  rw [a_count_witness] at heven
  exact (by decide : ¬ Even 815634435) heven

end AgenticConjectures.OeisA108864
