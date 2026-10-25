import Mathlib

/-!
# OEIS A397621 — linear complexity of Pascal rows mod 2

[OEIS A397621](https://oeis.org/A397621) (offset 1) is "the linear complexity over GF(2) of
the binary expansion of n (as computed by the Berlekamp-Massey algorithm)". Its Formula
section records

> Conjecture: a(A001317(n)) = A080079(n).

[A001317](https://oeis.org/A001317) is row `n` of Pascal's triangle mod 2 read as a binary
number, and [A080079](https://oeis.org/A080079) has the closed form
`a(n) = -n + 2*2^floor(log(n)/log(2))` in its Formula section.

`statement` is the conjecture for every `n ≥ 1` (the offset of A080079), and
`a_A001317_eq_A080079` proves it, following `problems/oeis-a397621/PROOF.md`:
`binWord_A001317` is §3.3 (the word is `(1+x)^n` over `𝔽₂`), `not_hasRecurrence` is the
zero-run lower bound of §3.4.1–3.4.2, and `hasRecurrence` is the `(1+x)^d` upper bound of
§3.4.3.

## Definitions and semantic choices

* `HasRecurrence s N L` writes `s i + c₁ s (i-1) + ⋯ + c_L s (i-L) = 0` for `L ≤ i < N`
  with `c j` in place of `c_{j+1}`. Nothing forces `c_L ≠ 0`, so `L` is the span that
  Berlekamp–Massey returns, and `L = N` always works vacuously.
* `Nat.digits` lists the least significant bit first, so `binWord` reverses it.
* A comment in the entry calls `a(n)` the degree of the minimal connection polynomial. That
  reading differs from the Berlekamp–Massey span on the word `10`, where the data has
  `a(2) = 1`; `a_two` checks that our definition gives `1`.
* `A080079` is its closed form above, not its carry-sequence name.

There is no upstream FormalConjectures snapshot for this entry.
-/

namespace AgenticConjectures.OeisA397621

open Finset Polynomial

/-- The word `s 0, …, s (N-1)` over `𝔽₂` satisfies a linear recurrence of span `L`. -/
def HasRecurrence (s : ℕ → ZMod 2) (N L : ℕ) : Prop :=
  ∃ c : ℕ → ZMod 2, ∀ i, L ≤ i → i < N → s i + ∑ j ∈ range L, c j * s (i - (j + 1)) = 0

/-- Linear complexity over `𝔽₂`: the least span of a recurrence satisfied by the word. -/
noncomputable def linearComplexity (s : ℕ → ZMod 2) (N : ℕ) : ℕ :=
  sInf {L | HasRecurrence s N L}

/-- The binary expansion of `n`, most significant bit first. -/
def binWord (n i : ℕ) : ZMod 2 := ((Nat.digits 2 n).reverse.getD i 0 : ℕ)

/-- OEIS A397621. -/
noncomputable def a (n : ℕ) : ℕ := linearComplexity (binWord n) (Nat.digits 2 n).length

/-- OEIS A001317: row `n` of Pascal's triangle mod 2 read in binary. -/
def A001317 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k % 2 * 2 ^ k

/-- OEIS A080079, by its closed form. -/
def A080079 (n : ℕ) : ℕ := 2 * 2 ^ Nat.log 2 n - n

/-- The conjecture in the Formula section of OEIS A397621. -/
def statement : Prop := ∀ n, 1 ≤ n → a (A001317 n) = A080079 n

theorem ofDigits_map_range (b m : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits b ((List.range m).map f) = ∑ k ∈ range m, f k * b ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, sum_range_succ]
    simp [Nat.ofDigits_singleton]
    ring

theorem digits_A001317 (n : ℕ) :
    Nat.digits 2 (A001317 n) = (List.range (n + 1)).map fun k => n.choose k % 2 := by
  rw [A001317, ← ofDigits_map_range]
  refine Nat.digits_ofDigits 2 (by norm_num) _ (fun l hl => ?_) (fun h => ?_)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hl
    exact Nat.mod_lt _ (by norm_num)
  · simp [List.getLast_map, List.getLast_range]

theorem binWord_A001317 (n i : ℕ) : binWord (A001317 n) i = (n.choose i : ZMod 2) := by
  rw [binWord, digits_A001317]
  rcases lt_or_ge i (n + 1) with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_reverse, List.getElem_map,
      List.getElem_range, ZMod.natCast_mod]
    simp only [List.length_map, List.length_range]
    rw [show n + 1 - 1 - i = n - i by omega, Nat.choose_symm (by omega)]
  · rw [List.getD_eq_default _ _ (by simpa using hi), Nat.choose_eq_zero_of_lt (by omega)]

theorem X_add_one_pow_two_pow (h : ℕ) : (X + 1 : (ZMod 2)[X]) ^ 2 ^ h = X ^ 2 ^ h + 1 := by
  rw [add_pow_char_pow, one_pow]

theorem choose_add_cast {q : ℕ} (hq : (X + 1 : (ZMod 2)[X]) ^ q = X ^ q + 1) (r i : ℕ) :
    ((q + r).choose i : ZMod 2) =
      (if q ≤ i then (r.choose (i - q) : ZMod 2) else 0) + r.choose i := by
  rw [← coeff_X_add_one_pow (ZMod 2) (q + r) i, pow_add, hq, add_mul, one_mul, coeff_add,
    coeff_X_pow_mul']
  simp only [coeff_X_add_one_pow]

theorem not_hasRecurrence {q r L : ℕ} (hq : (X + 1 : (ZMod 2)[X]) ^ q = X ^ q + 1)
    (hr : r < q) (hL : L < q - r) :
    ¬ HasRecurrence (fun i => ((q + r).choose i : ZMod 2)) (q + r + 1) L := by
  rintro ⟨c, hc⟩
  have hsum : ∑ j ∈ range L, c j * ((q + r).choose (q - (j + 1)) : ZMod 2) = 0 :=
    sum_eq_zero fun j hj => by
      have := mem_range.1 hj
      rw [choose_add_cast hq, if_neg (by omega), zero_add, Nat.choose_eq_zero_of_lt (by omega),
        Nat.cast_zero, mul_zero]
  have hone : ((q + r).choose q : ZMod 2) = 1 := by
    rw [choose_add_cast hq, if_pos le_rfl, Nat.sub_self, Nat.choose_zero_right,
      Nat.choose_eq_zero_of_lt hr]
    simp
  have h := hc q (by omega) (by omega)
  simp only at h
  rw [hone, hsum, add_zero] at h
  exact one_ne_zero h

theorem hasRecurrence {q r : ℕ} (hq : (X + 1 : (ZMod 2)[X]) ^ (2 * q) = X ^ (2 * q) + 1)
    (hr : r < q) :
    HasRecurrence (fun i => ((q + r).choose i : ZMod 2)) (q + r + 1) (q - r) := by
  refine ⟨fun j => ((q - r).choose (j + 1) : ZMod 2), fun i hi hin => ?_⟩
  have key : ((X + 1 : (ZMod 2)[X]) ^ (q - r) * (X + 1) ^ (q + r)).coeff i = 0 := by
    rw [← pow_add, show q - r + (q + r) = 2 * q by omega, hq, coeff_add, coeff_X_pow, coeff_one,
      if_neg (by omega), if_neg (by omega), add_zero]
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  simp only [coeff_X_add_one_pow] at key
  rw [← sum_subset (range_subset_range.2 (show q - r + 1 ≤ i + 1 by omega)) fun k _ hk => by
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk), Nat.cast_zero, zero_mul]] at key
  rw [sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    add_comm] at key
  exact key

theorem linearComplexity_pascal_aux {q r : ℕ} (hq : (X + 1 : (ZMod 2)[X]) ^ q = X ^ q + 1)
    (hq2 : (X + 1 : (ZMod 2)[X]) ^ (2 * q) = X ^ (2 * q) + 1) (hr : r < q) :
    linearComplexity (fun i => ((q + r).choose i : ZMod 2)) (q + r + 1) = q - r := by
  refine le_antisymm (Nat.sInf_le (hasRecurrence hq2 hr)) ?_
  refine le_csInf ⟨_, hasRecurrence hq2 hr⟩ fun L hL => ?_
  by_contra hlt
  exact not_hasRecurrence hq hr (by omega) hL

theorem linearComplexity_pascal {n : ℕ} (hn : 1 ≤ n) :
    linearComplexity (fun i => (n.choose i : ZMod 2)) (n + 1) = A080079 n := by
  have hq1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hq2 : n < 2 * 2 ^ Nat.log 2 n := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rwa [pow_succ, mul_comm] at this
  have h := linearComplexity_pascal_aux (q := 2 ^ Nat.log 2 n) (r := n - 2 ^ Nat.log 2 n)
    (X_add_one_pow_two_pow _) (by rw [← pow_succ']; exact X_add_one_pow_two_pow _) (by omega)
  rw [Nat.add_sub_cancel' hq1] at h
  rw [h, A080079]
  omega

theorem a_A001317_eq_A080079 : statement := by
  intro n hn
  have h : a (A001317 n) = linearComplexity (fun i => (n.choose i : ZMod 2)) (n + 1) := by
    rw [a, digits_A001317, List.length_map, List.length_range]
    congr 1
    funext i
    exact binWord_A001317 n i
  rw [h, linearComplexity_pascal hn]

/-- The data value `a(2) = 1`: the word `10` satisfies the span-1 recurrence
`s 1 = 0 · s 0`, while every connection polynomial generating it has degree at least 2. -/
theorem a_two : a 2 = 1 := by
  have h0 : binWord 2 0 = 1 := by simp [binWord]
  have h1 : binWord 2 1 = 0 := by simp [binWord]
  have hrec : HasRecurrence (binWord 2) 2 1 := ⟨fun _ => 0, fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    simp [h1]⟩
  have hlen : (Nat.digits 2 2).length = 2 := by simp
  rw [a, hlen]
  refine le_antisymm (Nat.sInf_le hrec) (le_csInf ⟨1, hrec⟩ fun L hL => ?_)
  rcases Nat.eq_zero_or_pos L with rfl | h
  · obtain ⟨c, hc⟩ := hL
    have := hc 0 le_rfl (by simp)
    simp [h0] at this
  · exact h

end AgenticConjectures.OeisA397621
