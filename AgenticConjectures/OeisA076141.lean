import Mathlib

/-!
# OEIS A076141 — reduction for "`n` occurs at most once in the binary expansion of `n²`"

A076141 counts the occurrences of the binary expansion of `n` as a contiguous block of the
binary expansion of `n ^ 2`. The OEIS entry conjectures that the count is at most `1`
(upstream `oeis_a076141_conjecture`), recorded here as the open `statement`; it is not proved.

This module proves the reduction behind the exhaustive searches of `problems/oeis-a076141/`
(see `DETAILS.md` there):

* `a_eq_countP`: for `n ≠ 0` the upstream count `a n` is the number of bit positions `s` with
  `Occ n L s`, i.e. `⌊n² / 2^s⌋ mod 2^L = n`, where `L` is the bit length of `n`.
* `occ_of_occ_two_mul`, `occ_descent`, `exists_odd_of_two_occ`: occurrences of `2 n` give
  occurrences of `n`, so the occurrences of `n` map injectively to those of its odd part and
  below every counterexample there is an odd one.
* `three_le_of_occ`, `occ_lt`: every occurrence of an odd `n ≥ 3` starts at a bit position
  `s` with `3 ≤ s < L`.
* `not_occ_pair_of_close`, `not_occ_pair_of_far`: occurrences at `s` and `s + d` (`d ≥ 1`)
  cannot coexist if `2 d + s + 1 ≤ L`, nor if `d < s` and `s + d < L`.
* `pair_geometry`, `reduction`: a counterexample yields an odd `k ≥ 3` of bit length `L` with
  occurrences `s < t`, `3 ≤ s`, `2 s ≤ t`, `L + s ≤ 2 t` and `t < L`.
* `a_le_two`: three occurrences are impossible, so `a n ≤ 2` for every `n` (unconditional).
* `pair_covered`, `a_le_one_of_search`: therefore only the positions `SearchedPos L`
  (`[3, L / 3 + 1]` and `[τ, L - 1]`) need to be examined; `a_le_one_of_search` derives
  `a n ≤ 1` for all `n < 2 ^ N` from the hypothesis that the searches check.

The searches themselves, and the completeness of their single-occurrence methods, are not
formalized: `a_le_one_of_search` is an implication whose hypothesis is checked only by the
programs, and nothing in this module proves `statement`.

## Correspondence with the upstream snapshot

* `list_count_infix`, `binary_pattern_nat` and `a` are copied term for term from
  `problems/oeis-a076141/upstream/76141_34382c19.lean`. The upstream file opens `List` and
  `Nat`, but every name in these definitions is fully qualified, so the copies are the same
  terms.
* `statement` is the proposition of the upstream `oeis_a076141_conjecture`,
  `∀ n : ℕ, a n ≤ 1`.
* Upstream encodes `0` by the pattern `[0]`, so `a 0 = 1` (`a_zero`); every `n ≠ 0` uses
  `Nat.digits 2`, most significant bit first, without leading zeros.
* `Occ n L s` counts bit positions from the least significant end; the upstream window offset
  `i` (from the most significant end) corresponds to `s = M - L - i`, where `M` is the bit
  length of `n ^ 2` (`a_eq_countP`).
-/

namespace AgenticConjectures.OeisA076141

/-! ### Upstream definitions (copied term for term) -/

/-- Upstream `list_count_infix`: the number of times `pattern` appears as a contiguous sublist
in `target`. -/
def list_count_infix {α : Type*} [DecidableEq α] (pattern : List α) (target : List α) : ℕ :=
  if pattern.isEmpty then 0
  else
    let n := pattern.length
    let m := target.length
    if n > m then 0
    else
      (List.range (m - n + 1)).countP fun i =>
        (target.drop i).take n = pattern

/-- Upstream `binary_pattern_nat`: binary digits of `n`, most significant first; `[0]` for `0`. -/
def binary_pattern_nat (n : ℕ) : List ℕ :=
  match n with
  | 0 => [0]
  | m + 1 => (Nat.digits 2 (m + 1)).reverse

/-- Upstream `a`: the number of occurrences of the binary pattern of `n` in that of `n ^ 2`. -/
def a (n : ℕ) : ℕ :=
  let pattern := binary_pattern_nat n
  let target := binary_pattern_nat (n^2)
  list_count_infix pattern target

/-- The upstream conjecture `oeis_a076141_conjecture` (open; recorded, not proved). -/
def statement : Prop := ∀ n : ℕ, a n ≤ 1

/-- `n` (read as an `L`-bit number) occurs in `n ^ 2` at bit position `s` (bit `0` is the least
significant bit). -/
def Occ (n L s : ℕ) : Prop := n ^ 2 / 2 ^ s % 2 ^ L = n

instance (n L s : ℕ) : Decidable (Occ n L s) :=
  inferInstanceAs (Decidable (n ^ 2 / 2 ^ s % 2 ^ L = n))

/-! ### Two occurrences: block decomposition and the key identity -/

/-- Occurrences at `s` and `s + d` (`d ≤ L`) split `n ^ 2` into blocks
`A | n | m | B` (equation (A076-12) of `DETAILS.md`). -/
private lemma pair_data {n L s d : ℕ} (hdL : d ≤ L) (h1 : Occ n L s) (h2 : Occ n L (s + d)) :
    ∃ A B m b : ℕ, m < 2 ^ d ∧ B < 2 ^ s ∧
      n ^ 2 = A * 2 ^ (s + d + L) + n * 2 ^ (s + d) + m * 2 ^ s + B ∧
      n * 2 ^ d + m = 2 ^ L * b + n := by
  set x := n ^ 2 with hx
  set W := x / 2 ^ s % 2 ^ (d + L) with hW
  have hWdiv : W / 2 ^ d = n := by
    rw [hW, pow_add, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add]
    exact h2
  have hWmod : W % 2 ^ d = n % 2 ^ d := by
    rw [hW, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : d ≤ d + L))]
    rw [← h1, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hdL)]
  have hWeq : W = n * 2 ^ d + n % 2 ^ d := by
    have := Nat.div_add_mod W (2 ^ d)
    rw [hWdiv, hWmod] at this
    rw [← this]; ring
  have hWmodL : W % 2 ^ L = n := by
    rw [hW, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : L ≤ d + L))]
    exact h1
  refine ⟨x / 2 ^ (s + d + L), x % 2 ^ s, n % 2 ^ d, W / 2 ^ L,
    Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), ?_, ?_⟩
  · have ha := Nat.div_add_mod x (2 ^ s)
    have hb := Nat.div_add_mod (x / 2 ^ s) (2 ^ (d + L))
    have hc : x / 2 ^ s / 2 ^ (d + L) = x / 2 ^ (s + d + L) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, add_assoc]
    rw [hc, ← hW, hWeq] at hb
    set A := x / 2 ^ (s + d + L) with hA
    set B := x % 2 ^ s with hB
    have e1 : (2:ℕ) ^ (s + d + L) = 2 ^ s * 2 ^ (d + L) := by rw [← pow_add, add_assoc]
    have e2 : (2:ℕ) ^ (s + d) = 2 ^ s * 2 ^ d := by rw [← pow_add]
    rw [e1, e2]
    calc x = 2 ^ s * (x / 2 ^ s) + x % 2 ^ s := ha.symm
      _ = 2 ^ s * (2 ^ (d + L) * (x / 2 ^ (s + d + L)) + (n * 2 ^ d + n % 2 ^ d))
            + x % 2 ^ s := by rw [hb]
      _ = _ := by ring
  · have := Nat.div_add_mod W (2 ^ L)
    rw [hWmodL] at this
    rw [← hWeq, this]

/-- Equation (A076-13) of `DETAILS.md`, with `P = 2^s`, `D = 2^d`, `U = 2^u`. -/
private lemma key_identity (n A B m b P D U : ℤ)
    (h1 : n ^ 2 = A * (P ^ 2 * D ^ 2 * U) + n * (P * D) + m * P + B)
    (h2 : n * D + m = (P * D * U) * b + n) :
    (P * D) * (P * D * U) * (U * b ^ 2 - (D - 1) * b - (D - 1) ^ 2 * A) =
      (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 + 2 * (P * D * U) * b * m := by
  linear_combination (D - 1) ^ 2 * h1 + (-(D - 1) * n + m - P * D * U * b + P * D * (D - 1)) * h2

private lemma odd_two_pow_sub_one {d : ℕ} (hd : 0 < d) : Odd (2 ^ d - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hd.ne'⟩) odd_one

/-- The low block `m` of a pair is nonzero. -/
private lemma low_block_pos {n L d m b : ℕ} (hn0 : 0 < n) (hnL : n < 2 ^ L) (hd : 0 < d)
    (e2 : n * 2 ^ d + m = 2 ^ L * b + n) : 1 ≤ m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst hm0
  have hcop : Nat.Coprime (2 ^ L) (2 ^ d - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_two_pow_sub_one hd))
  have hmul : n * (2 ^ d - 1) = 2 ^ L * b := by
    rw [Nat.mul_sub_one]; omega
  have hdvd : 2 ^ L ∣ n := by
    have : 2 ^ L ∣ (2 ^ d - 1) * n := ⟨b, by rw [mul_comm]; exact hmul⟩
    exact hcop.dvd_of_dvd_mul_left this
  exact absurd (Nat.le_of_dvd hn0 hdvd) (by omega)

/-- Integer form of the pair data, with `L = s + d + u`. -/
private lemma pair_data_int {n s d u : ℕ} (h1 : Occ n (s + d + u) s)
    (h2 : Occ n (s + d + u) (s + d)) :
    ∃ A B m b : ℕ, m < 2 ^ d ∧ B < 2 ^ s ∧
      n * 2 ^ d + m = 2 ^ (s + d + u) * b + n ∧
      (n : ℤ) ^ 2 = (A : ℤ) * ((2 : ℤ) ^ s) ^ 2 * ((2 : ℤ) ^ d) ^ 2 * 2 ^ u
        + n * (2 ^ s * 2 ^ d) + m * 2 ^ s + B ∧
      (n : ℤ) * 2 ^ d + m = 2 ^ s * 2 ^ d * 2 ^ u * b + n := by
  obtain ⟨A, B, m, b, hm, hB, e1, e2⟩ := pair_data (by omega) h1 h2
  refine ⟨A, B, m, b, hm, hB, e2, ?_, ?_⟩
  · have h := congrArg (fun z : ℕ => (z : ℤ)) e1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    rw [h]; ring
  · have h := congrArg (fun z : ℕ => (z : ℤ)) e2
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    rw [h]; ring

private lemma close_bounds (D P U B m : ℤ) (hD : 2 ≤ D) (hP : 1 ≤ P) (hUD : 2 * D ≤ U)
    (hm1 : 1 ≤ m) (hmD : m ≤ D - 1) (hB0 : 0 ≤ B) (hBP : B ≤ P - 1) :
    -(P * D * U) < (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 ∧
      (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 < P * D * U := by
  have hD1 : 0 ≤ D - 1 := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hm0 : 0 ≤ m := by linarith
  have a1 : 0 ≤ (D - 1) * P * m := mul_nonneg (mul_nonneg hD1 hP0) hm0
  have a2 : (D - 1) ^ 2 * B ≤ (D - 1) ^ 2 * (P - 1) :=
    mul_le_mul_of_nonneg_left hBP (sq_nonneg _)
  have a3 : (D - 1) ^ 2 * (P - 1) < D ^ 2 * P := by
    have : 0 ≤ (P - 1) * (2 * D - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have a4 : 2 * (D ^ 2 * P) ≤ P * D * U := by
    have : 0 ≤ P * D * (U - 2 * D) := mul_nonneg (mul_nonneg hP0 (by linarith)) (by linarith)
    nlinarith
  have a5 : 0 < D ^ 2 * P := by positivity
  have b1 : (D - 1) * P * m ≤ (D - 1) * P * (D - 1) :=
    mul_le_mul_of_nonneg_left hmD (mul_nonneg hD1 hP0)
  have b2 : m ^ 2 ≤ (D - 1) ^ 2 := pow_le_pow_left₀ hm0 hmD 2
  have b3 : (D - 1) ^ 2 * (P + 1) < 2 * (D ^ 2 * P) := by
    have : 0 ≤ D ^ 2 * (P - 1) := mul_nonneg (sq_nonneg _) (by linarith)
    have : 0 ≤ P * (2 * D - 1) := mul_nonneg hP0 (by linarith)
    nlinarith
  have b4 : 0 ≤ (D - 1) ^ 2 * B := mul_nonneg (sq_nonneg _) hB0
  constructor
  · nlinarith
  · nlinarith

private lemma far_bounds (D P U B m b : ℤ) (hD : 2 ≤ D) (hPD : 2 * D ≤ P) (hU : 2 ≤ U)
    (hm1 : 1 ≤ m) (hmD : m ≤ D - 1) (hB0 : 0 ≤ B) (hBP : B ≤ P - 1) (hb : b ≤ D - 1)
    (hb2 : D ≤ 2 * b) :
    0 < (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 + 2 * (P * D * U) * b * m ∧
      (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 + 2 * (P * D * U) * b * m <
        P * D * (P * D * U) := by
  have hD1 : 0 ≤ D - 1 := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hb0 : 0 ≤ b := by linarith
  set E := P * D * U with hE
  have hE2 : 2 * (P * D) ≤ E := by
    have : 0 ≤ P * D * (U - 2) := mul_nonneg (mul_nonneg hP0 (by linarith)) (by linarith)
    nlinarith
  have hE0 : 0 ≤ E := by nlinarith
  have b4 : 0 ≤ (D - 1) ^ 2 * B := mul_nonneg (sq_nonneg _) hB0
  constructor
  · -- Y = (D-1)^2 B + m (2 E b - (D-1) P - m) and the bracket is positive
    have c1 : E * D ≤ E * (2 * b) := mul_le_mul_of_nonneg_left hb2 hE0
    have c2 : (D - 1) * P + m < E * D := by
      have : 2 * (P * D) * D ≤ E * D := mul_le_mul_of_nonneg_right hE2 (by linarith)
      have : 0 ≤ P * D * (D - 2) := mul_nonneg (mul_nonneg hP0 (by linarith)) (by linarith)
      nlinarith
    have c3 : 1 ≤ 2 * E * b - (D - 1) * P - m := by linarith
    have c4 : m * 1 ≤ m * (2 * E * b - (D - 1) * P - m) :=
      mul_le_mul_of_nonneg_left c3 hm0
    nlinarith
  · have d1 : b * m ≤ (D - 1) * (D - 1) := mul_le_mul hb hmD hm0 hD1
    have d2 : 2 * E * b * m ≤ 2 * E * ((D - 1) * (D - 1)) := by
      have := mul_le_mul_of_nonneg_left d1 (by linarith : (0 : ℤ) ≤ 2 * E)
      linarith [this]
    have d3 : (D - 1) ^ 2 * B ≤ (D - 1) ^ 2 * (P - 1) :=
      mul_le_mul_of_nonneg_left hBP (sq_nonneg _)
    have d4 : 0 ≤ (D - 1) * P * m := mul_nonneg (mul_nonneg hD1 hP0) hm0
    -- P D E ≥ 2 D^2 E and D^2 P ≤ D E / 2
    have d5 : 2 * D * D * E ≤ P * D * E := by
      have : 0 ≤ (P - 2 * D) * D * E := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hE0
      nlinarith
    have d6 : 2 * (D * (D * P)) ≤ D * E := by
      have := mul_le_mul_of_nonneg_left hE2 (by linarith : (0 : ℤ) ≤ D)
      nlinarith
    have d7 : 0 ≤ (D - 1) ^ 2 := sq_nonneg _
    have d8 : 0 < E := by nlinarith
    have d9 : 0 ≤ D * E := mul_nonneg (by linarith) hE0
    nlinarith

/-- From `X = 0` (the close case) to a contradiction. -/
private lemma close_contra (D P B m : ℤ) (hD : 2 ≤ D) (hDeven : Even D) (hm1 : 1 ≤ m)
    (hmD : m ≤ D - 1) (hBP : B ≤ P - 1)
    (hX0 : (D - 1) ^ 2 * B - (D - 1) * P * m - m ^ 2 = 0) : False := by
  have hsq : (2 * m + (D - 1) * P) ^ 2 = (D - 1) ^ 2 * (P ^ 2 + 4 * B) := by
    linear_combination -4 * hX0
  have hdvd : (D - 1) ∣ 2 * m + (D - 1) * P := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨P ^ 2 + 4 * B, hsq⟩
  have hdvd2 : (D - 1) ∣ 2 * m := by
    have := dvd_sub hdvd (dvd_mul_right (D - 1) P)
    simpa using this
  obtain ⟨j, hj⟩ := hdvd2
  have hodd : Odd (D - 1) := Even.sub_odd hDeven odd_one
  have hjeven : Even j := by
    have hev : Even ((D - 1) * j) := by rw [← hj]; exact even_two_mul _
    rcases Int.even_mul.mp hev with h | h
    · exact absurd h (Int.not_even_iff_odd.mpr hodd)
    · exact h
  obtain ⟨i, hi⟩ := hjeven
  have hmi : m = (D - 1) * i := by
    have h2 : 2 * m = 2 * ((D - 1) * i) := by rw [hj, hi]; ring
    linarith
  have hDpos : 0 < D - 1 := by linarith
  have hi_pos : 0 < i := by
    by_contra h
    push Not at h
    have : (D - 1) * i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le h
    linarith
  have hi_le : i ≤ 1 := by
    by_contra h
    push Not at h
    have : (D - 1) * 2 ≤ (D - 1) * i := mul_le_mul_of_nonneg_left (by omega) hDpos.le
    linarith
  have hi1 : i = 1 := by omega
  rw [hi1, mul_one] at hmi
  rw [hmi] at hX0
  have h2 : (D - 1) ^ 2 * (B - (P + 1)) = 0 := by linear_combination hX0
  rcases mul_eq_zero.mp h2 with h | h
  · have : 0 < (D - 1) ^ 2 := by positivity
    linarith
  · linarith

/-- If `0 < Y < c` then `Y` is not a multiple `c * Z` of `c`. -/
private lemma not_mul_between (c Y Z : ℤ) (h : c * Z = Y) (h0 : 0 < Y) (h1 : Y < c) : False := by
  have hc : 0 < c := by linarith
  rcases le_or_gt Z 0 with hZ | hZ
  · have : c * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hZ
    linarith
  · have : c * 1 ≤ c * Z := mul_le_mul_of_nonneg_left (by omega) hc.le
    linarith

private lemma two_pow_even {d : ℕ} (hd : 0 < d) : Even ((2 : ℤ) ^ d) :=
  (Int.even_pow).mpr ⟨even_two, hd.ne'⟩

private lemma two_le_two_pow {d : ℕ} (hd : 0 < d) : (2 : ℤ) ≤ 2 ^ d := by
  calc (2 : ℤ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd

/-- **Close pairs are impossible.**  If `1 ≤ n < 2 ^ L`, two occurrences of `n`
at bit positions `s` and `s + d` (`d ≥ 1`) with `2 d + s + 1 ≤ L` cannot coexist. -/
theorem not_occ_pair_of_close {n L s d : ℕ} (hn0 : 0 < n) (hnL : n < 2 ^ L) (hd : 0 < d)
    (hclose : 2 * d + s + 1 ≤ L) (h1 : Occ n L s) (h2 : Occ n L (s + d)) : False := by
  obtain ⟨u, rfl⟩ : ∃ u, L = s + d + u := ⟨L - (s + d), by omega⟩
  obtain ⟨A, B, m, b, hm, hB, e2n, e1, e2⟩ := pair_data_int h1 h2
  have hm1 : 1 ≤ m := low_block_pos hn0 hnL hd e2n
  have key := key_identity (n : ℤ) A B m b (2 ^ s) (2 ^ d) (2 ^ u)
    (by rw [e1]; ring) (by rw [e2])
  have hUD : 2 * (2 : ℤ) ^ d ≤ 2 ^ u := by
    calc 2 * (2 : ℤ) ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ u := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmZ : (m : ℤ) ≤ 2 ^ d - 1 := by
    have : (m : ℤ) < 2 ^ d := by exact_mod_cast hm
    linarith
  have hBZ : (B : ℤ) ≤ 2 ^ s - 1 := by
    have : (B : ℤ) < 2 ^ s := by exact_mod_cast hB
    linarith
  obtain ⟨hlo, hhi⟩ := close_bounds (2 ^ d) (2 ^ s) (2 ^ u) B m (two_le_two_pow hd)
    (one_le_pow₀ (by norm_num)) hUD (by exact_mod_cast hm1) hmZ (by positivity) hBZ
  -- the left side of `key` minus `2 E b m` is a multiple of `E = 2 ^ L`
  set E : ℤ := 2 ^ s * 2 ^ d * 2 ^ u with hE
  set X : ℤ := ((2 : ℤ) ^ d - 1) ^ 2 * B - (2 ^ d - 1) * 2 ^ s * m - (m : ℤ) ^ 2 with hX
  have hXk : E * ((2 ^ s * 2 ^ d) * ((2 : ℤ) ^ u * b ^ 2 - (2 ^ d - 1) * b
      - (2 ^ d - 1) ^ 2 * A) - 2 * b * m) = X := by
    rw [hE, hX]; linear_combination key
  have hX0 : X = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact not_mul_between E (-X) (-((2 ^ s * 2 ^ d) * ((2 : ℤ) ^ u * b ^ 2 - (2 ^ d - 1) * b
        - (2 ^ d - 1) ^ 2 * A) - 2 * b * m)) (by rw [← hXk]; ring) (by linarith) (by linarith)
    · exact not_mul_between E X _ hXk hpos hhi
  exact close_contra (2 ^ d) (2 ^ s) B m (two_le_two_pow hd) (two_pow_even hd)
    (by exact_mod_cast hm1) hmZ hBZ hX0

/-- **Pairs with a far lower occurrence are impossible.**  If `2 ^ (L-1) ≤ n < 2 ^ L`,
two occurrences of `n` at bit positions `s` and `s + d` with `1 ≤ d < s` and
`s + d < L` cannot coexist. -/
theorem not_occ_pair_of_far {n L s d : ℕ} (hn : 2 ^ (L - 1) ≤ n) (hnL : n < 2 ^ L)
    (hd : 0 < d) (hfar : d < s) (htop : s + d < L) (h1 : Occ n L s) (h2 : Occ n L (s + d)) :
    False := by
  obtain ⟨u, rfl⟩ : ∃ u, L = s + d + u := ⟨L - (s + d), by omega⟩
  have hu : 1 ≤ u := by omega
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  obtain ⟨A, B, m, b, hm, hB, e2n, e1, e2⟩ := pair_data_int h1 h2
  have hm1 : 1 ≤ m := low_block_pos hn0 hnL hd e2n
  have key := key_identity (n : ℤ) A B m b (2 ^ s) (2 ^ d) (2 ^ u)
    (by rw [e1]; ring) (by rw [e2])
  have hmZ : (m : ℤ) ≤ 2 ^ d - 1 := by
    have : (m : ℤ) < 2 ^ d := by exact_mod_cast hm
    linarith
  have hBZ : (B : ℤ) ≤ 2 ^ s - 1 := by
    have : (B : ℤ) < 2 ^ s := by exact_mod_cast hB
    linarith
  have hPD : 2 * (2 : ℤ) ^ d ≤ 2 ^ s := by
    calc 2 * (2 : ℤ) ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
  have hU : (2 : ℤ) ≤ 2 ^ u := two_le_two_pow (by omega)
  -- bounds on the top block `b` from `n (2^d - 1) + m = 2^L b`
  have hnZ : (n : ℤ) ≤ 2 ^ s * 2 ^ d * 2 ^ u - 1 := by
    have : (n : ℤ) < 2 ^ (s + d + u) := by exact_mod_cast hnL
    rw [pow_add, pow_add] at this
    linarith
  have hn2 : 2 ^ s * 2 ^ d * 2 ^ u ≤ 2 * (n : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hn
    push_cast at h
    have : (2 : ℤ) ^ (s + d + u) = 2 * 2 ^ (s + d + u - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [pow_add, pow_add] at this
    linarith
  have hb : (b : ℤ) ≤ 2 ^ d - 1 := by
    have hD1 : (0 : ℤ) ≤ 2 ^ d - 1 := by linarith [two_le_two_pow hd]
    have : (2 ^ s * 2 ^ d * 2 ^ u : ℤ) * b ≤ (2 ^ s * 2 ^ d * 2 ^ u) * (2 ^ d - 1) := by
      have := mul_le_mul_of_nonneg_left hnZ hD1
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hb2 : (2 : ℤ) ^ d ≤ 2 * b := by
    have hD1 : (0 : ℤ) ≤ 2 ^ d - 1 := by linarith [two_le_two_pow hd]
    have hm1Z : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    have h3 : (2 ^ s * 2 ^ d * 2 ^ u : ℤ) * (2 ^ d - 1) < (2 ^ s * 2 ^ d * 2 ^ u) * (2 * b) := by
      have := mul_le_mul_of_nonneg_right hn2 hD1
      nlinarith
    have h4 := lt_of_mul_lt_mul_left h3 (by positivity)
    linarith
  obtain ⟨hlo, hhi⟩ := far_bounds (2 ^ d) (2 ^ s) (2 ^ u) B m b (two_le_two_pow hd) hPD hU
    (by exact_mod_cast hm1) hmZ (by positivity) hBZ hb hb2
  exact not_mul_between _ _ _ (by rw [← key]) hlo (by linarith)

/-! ### Elementary facts about single occurrences -/

/-- An occurrence lies inside the square: `2 ^ t ≤ n`, hence `t < L` when `n < 2 ^ L`. -/
theorem occ_lt {n L t : ℕ} (hn0 : 0 < n) (hnL : n < 2 ^ L) (h : Occ n L t) : t < L := by
  have h1 : n ≤ n ^ 2 / 2 ^ t := by
    unfold Occ at h
    calc n = n ^ 2 / 2 ^ t % 2 ^ L := h.symm
      _ ≤ n ^ 2 / 2 ^ t := Nat.mod_le _ _
  have h2 : n * 2 ^ t ≤ n * n := by
    rw [Nat.le_div_iff_mul_le (by positivity)] at h1
    calc n * 2 ^ t = 2 ^ t * n := by ring
      _ ≤ _ := by nlinarith
  have h3 : 2 ^ t ≤ n := Nat.le_of_mul_le_mul_left h2 hn0
  have h4 : 2 ^ t < 2 ^ L := lt_of_le_of_lt h3 hnL
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4

private lemma sq_mod_eight {n : ℕ} (hodd : Odd n) : n ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hodd
  have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [this]
  rcases Nat.even_mul_succ_self k with ⟨j, hj⟩
  rw [hj]
  omega

/-- For odd `n ≥ 3` every occurrence starts at bit position `3` or higher. -/
theorem three_le_of_occ {n L s : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) (hnL : n < 2 ^ L)
    (h : Occ n L s) : 3 ≤ s := by
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp at hnL; omega
    · exact hL
  have h8 := sq_mod_eight hodd
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  -- the lowest window bit is bit `s` of `n ^ 2` and must equal the lowest bit of `n`
  have hbit : n ^ 2 / 2 ^ s % 2 = 1 := by
    have hdvd : 2 ∣ 2 ^ L := dvd_pow_self 2 (by omega)
    unfold Occ at h
    rw [← Nat.mod_mod_of_dvd _ hdvd, h, hn2]
  by_contra hs
  push Not at hs
  interval_cases s
  · -- s = 0: `n ^ 2 ≡ n (mod 2 ^ L)` forces `2 ^ L ∣ n - 1`
    unfold Occ at h
    simp only [pow_zero, Nat.div_one] at h
    have hmul : n * (n - 1) = 2 ^ L * (n ^ 2 / 2 ^ L) := by
      have := Nat.div_add_mod (n ^ 2) (2 ^ L)
      rw [h] at this
      have e : n * (n - 1) = n ^ 2 - n := by
        rw [Nat.mul_sub_one, sq]
      rw [e]; omega
    have hcop : Nat.Coprime (2 ^ L) n :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hdvd : 2 ^ L ∣ n - 1 :=
      hcop.dvd_of_dvd_mul_left ⟨n ^ 2 / 2 ^ L, by rw [← hmul]⟩
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · simp only [pow_one] at hbit; omega
  · norm_num at hbit; omega

/-! ### Pair geometry -/

/-- **Pair geometry.**  Two occurrences `s < t` of an odd `n ≥ 3` of bit length `L` satisfy
`3 ≤ s`, `2 s ≤ t`, `L + s ≤ 2 t` and `t < L`. -/
theorem pair_geometry {n L s t : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) (hn : 2 ^ (L - 1) ≤ n)
    (hnL : n < 2 ^ L) (hst : s < t) (h1 : Occ n L s) (h2 : Occ n L t) :
    3 ≤ s ∧ 2 * s ≤ t ∧ L + s ≤ 2 * t ∧ t < L := by
  have hn0 : 0 < n := by omega
  have hs3 := three_le_of_occ hodd h3 hnL h1
  have htL := occ_lt hn0 hnL h2
  obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
  refine ⟨hs3, ?_, ?_, htL⟩
  · by_contra hfar
    exact not_occ_pair_of_far hn hnL (by omega) (by omega) htL h1 h2
  · by_contra hclose
    exact not_occ_pair_of_close hn0 hnL (by omega) (by omega) h1 h2

/-- **Coverage.**  With `σ = L / 3 + 1`, one of two occurrences of an odd `n ≥ 3` of bit
length `L` lies in `[3, σ]` or the upper one lies in `[τ, L - 1]`, where
`τ = max (2 σ + 2) ⌈(L + σ + 1) / 2⌉`.  These are the positions searched in reduced mode. -/
theorem pair_covered {n L s t : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) (hn : 2 ^ (L - 1) ≤ n)
    (hnL : n < 2 ^ L) (hst : s < t) (h1 : Occ n L s) (h2 : Occ n L t) :
    (3 ≤ s ∧ s ≤ L / 3 + 1) ∨
      (2 * (L / 3 + 1) + 2 ≤ t ∧ L + (L / 3 + 1) + 1 ≤ 2 * t ∧ t < L) := by
  obtain ⟨h3s, h2s, hLs, htL⟩ := pair_geometry hodd h3 hn hnL hst h1 h2
  omega

/-! ### Even `n` -/

/-- An occurrence of `2 n` (bit length `L + 1`) at position `t` gives `1 ≤ t` and an occurrence
of `n` at position `t - 1`. -/
theorem occ_of_occ_two_mul {n L t : ℕ} (hn0 : 0 < n) (hnL : n < 2 ^ L)
    (h : Occ (2 * n) (L + 1) t) : 1 ≤ t ∧ Occ n L (t - 1) := by
  unfold Occ at h
  rcases Nat.eq_zero_or_pos t with ht | ht
  · -- t = 0: `4 n ^ 2 ≡ 2 n (mod 2 ^ (L + 1))` forces `2 ^ L ∣ n`
    subst ht
    exfalso
    simp only [pow_zero, Nat.div_one] at h
    have hsplit := Nat.div_add_mod ((2 * n) ^ 2) (2 ^ (L + 1))
    rw [h] at hsplit
    set Q := (2 * n) ^ 2 / 2 ^ (L + 1) with hQ
    have h4 : 2 ^ L * Q + n = 2 * n ^ 2 := by
      have : 2 * (2 ^ L * Q + n) = 2 * (2 * n ^ 2) := by
        rw [pow_succ] at hsplit
        linarith
      omega
    have hmul : n * (2 * n - 1) = 2 ^ L * Q := by
      have e1 : n * (2 * n) = 2 * n ^ 2 := by ring
      rw [Nat.mul_sub_one, e1]
      omega
    have hodd : Odd (2 * n - 1) := by
      refine ⟨n - 1, ?_⟩; omega
    have hcop : Nat.Coprime (2 ^ L) (2 * n - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hdvd : 2 ^ L ∣ n :=
      hcop.dvd_of_dvd_mul_right ⟨Q, hmul⟩
    exact absurd (Nat.le_of_dvd hn0 hdvd) (by omega)
  · refine ⟨ht, ?_⟩
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    unfold Occ
    simp only [Nat.add_sub_cancel]
    have e1 : (2 * n) ^ 2 / 2 ^ (u + 1) / 2 = n ^ 2 / 2 ^ u := by
      rw [Nat.div_div_eq_div_mul]
      have : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
      rw [this, show 2 ^ (u + 1) * 2 = 4 * 2 ^ u by ring, Nat.mul_div_mul_left _ _ (by norm_num)]
    have e2 : (2 * n) ^ 2 / 2 ^ (u + 1) % (2 * 2 ^ L) / 2 = (2 * n) ^ 2 / 2 ^ (u + 1) / 2 % 2 ^ L :=
      Nat.mod_mul_right_div_self _ _ _
    rw [← e1, ← e2, ← pow_succ', h]
    omega

/-- **Descent to the odd part.**  For `0 < n` of bit length `L` there are an odd `k ≤ n` of bit
length `K` and a shift `j` such that every occurrence of `n` at `s` has `j ≤ s` and gives an
occurrence of `k` at `s - j`. -/
theorem occ_descent : ∀ (n L : ℕ), 0 < n → 2 ^ (L - 1) ≤ n → n < 2 ^ L →
    ∃ k K j, k ≤ n ∧ Odd k ∧ 2 ^ (K - 1) ≤ k ∧ k < 2 ^ K ∧
      ∀ s, Occ n L s → j ≤ s ∧ Occ k K (s - j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn0 hlo hhi
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
    · -- n = 2 m with bit length L = (L - 1) + 1
      have hm0 : 0 < m := by omega
      have hL : 2 ≤ L := by
        by_contra hL
        push Not at hL
        interval_cases L <;> simp at hlo hhi <;> omega
      obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
      have hmK : m < 2 ^ K := by rw [pow_succ] at hhi; omega
      have hmlo : 2 ^ (K - 1) ≤ m := by
        have : 2 ^ K = 2 * 2 ^ (K - 1) := by
          rw [← pow_succ']; congr 1; omega
        simp only [Nat.add_sub_cancel] at hlo
        omega
      have hnm : n = 2 * m := by omega
      subst hnm
      obtain ⟨k, K', j, hk, hodd, hklo, hkhi, hmap⟩ := ih m (by omega) K hm0 hmlo hmK
      refine ⟨k, K', j + 1, by omega, hodd, hklo, hkhi, fun s hs => ?_⟩
      obtain ⟨hs1, hs'⟩ := occ_of_occ_two_mul hm0 hmK hs
      obtain ⟨hj, hk'⟩ := hmap (s - 1) hs'
      exact ⟨by omega, by rwa [show s - (j + 1) = s - 1 - j by omega]⟩
    · refine ⟨n, L, 0, le_rfl, hodd, hlo, hhi, fun s hs => ?_⟩
      simpa using hs

/-- Two occurrences descend from an even number to its odd part. -/
theorem exists_odd_of_two_occ : ∀ (n L : ℕ), 0 < n → 2 ^ (L - 1) ≤ n → n < 2 ^ L →
    ∀ s t, s < t → Occ n L s → Occ n L t →
      ∃ k K s' t', k ≤ n ∧ Odd k ∧ 2 ^ (K - 1) ≤ k ∧ k < 2 ^ K ∧ s' < t' ∧
        Occ k K s' ∧ Occ k K t' := by
  intro n L hn0 hlo hhi s t hst h1 h2
  obtain ⟨k, K, j, hkn, hodd, hklo, hkhi, hmap⟩ := occ_descent n L hn0 hlo hhi
  obtain ⟨hj1, h1'⟩ := hmap s h1
  obtain ⟨hj2, h2'⟩ := hmap t h2
  exact ⟨k, K, s - j, t - j, hkn, hodd, hklo, hkhi, by omega, h1', h2'⟩

/-! ### Bridge from the upstream count to `Occ` -/

private lemma binary_pattern_nat_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    binary_pattern_nat k = (Nat.digits 2 k).reverse := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rfl

private lemma lt_two_of_mem_digits {x d : ℕ} (h : d ∈ Nat.digits 2 x) : d < 2 :=
  Nat.digits_lt_base (by norm_num) h

private lemma ofDigits_window (x s L : ℕ) :
    Nat.ofDigits 2 (((Nat.digits 2 x).drop s).take L) = x / 2 ^ s % 2 ^ L := by
  rw [Nat.self_div_pow_eq_ofDigits_drop s x le_rfl,
    Nat.ofDigits_mod_pow_eq_ofDigits_take L (by norm_num) _
      (fun l hl => lt_two_of_mem_digits (List.mem_of_mem_drop hl))]

private lemma window_eq_iff {x n s : ℕ}
    (hs : s + (Nat.digits 2 n).length ≤ (Nat.digits 2 x).length) :
    ((Nat.digits 2 x).drop s).take (Nat.digits 2 n).length = Nat.digits 2 n ↔
      x / 2 ^ s % 2 ^ (Nat.digits 2 n).length = n := by
  constructor
  · intro h
    have := congrArg (Nat.ofDigits 2) h
    rwa [ofDigits_window, Nat.ofDigits_digits] at this
  · intro h
    apply Nat.ofDigits_inj_of_len_eq (b := 2) (by norm_num)
    · simp only [List.length_take, List.length_drop]; omega
    · intro l hl
      exact lt_two_of_mem_digits (List.mem_of_mem_drop (List.mem_of_mem_take hl))
    · intro l hl; exact lt_two_of_mem_digits hl
    · rw [ofDigits_window, Nat.ofDigits_digits]; exact h

private lemma reverse_window {T : List ℕ} {i k : ℕ} (h : i + k ≤ T.length) :
    (T.reverse.drop i).take k = ((T.drop (T.length - k - i)).take k).reverse := by
  rw [List.drop_reverse, List.take_reverse, List.length_take, List.drop_take]
  have e1 : min (T.length - i) T.length - k = T.length - k - i := by omega
  have e2 : T.length - i - (T.length - k - i) = k := by omega
  rw [e1, e2]

/-- **Bridge to the upstream count.**  For `n ≠ 0` let `L` and `M` be the binary lengths of `n`
and `n ^ 2`.  Then `a n` counts the `i ≤ M - L` such that `n` occurs at bit position
`M - L - i` (`i` is the window offset from the most significant end used upstream). -/
theorem a_eq_countP {n : ℕ} (hn : n ≠ 0) :
    a n = (List.range ((Nat.digits 2 (n ^ 2)).length - (Nat.digits 2 n).length + 1)).countP
      (fun i => decide (Occ n (Nat.digits 2 n).length
        ((Nat.digits 2 (n ^ 2)).length - (Nat.digits 2 n).length - i))) := by
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hLM : (Nat.digits 2 n).length ≤ (Nat.digits 2 (n ^ 2)).length :=
    Nat.le_length_digits_le 2 n (n ^ 2) (Nat.le_self_pow two_ne_zero n)
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  simp only [a, list_count_infix, binary_pattern_nat_of_ne_zero hn,
    binary_pattern_nat_of_ne_zero hn2, List.isEmpty_reverse, List.length_reverse]
  rw [if_neg (by simpa using hne), if_neg (by omega)]
  apply List.countP_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [decide_eq_true_eq]
  rw [reverse_window (by omega), List.reverse_inj, window_eq_iff (by omega)]
  rfl

/-- `a 0 = 1` (the patterns of `0` and `0 ^ 2` are both `[0]`). -/
theorem a_zero : a 0 = 1 := by decide

private lemma exists_pair_of_two_le_countP {l : List ℕ} {p : ℕ → Bool} (hl : l.Nodup)
    (h : 2 ≤ l.countP p) : ∃ x ∈ l, ∃ y ∈ l, x < y ∧ p x ∧ p y := by
  rw [List.countP_eq_length_filter] at h
  have hnd : (l.filter p).Nodup := hl.filter p
  rcases hf : l.filter p with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp at h
  · have hx : x ∈ l.filter p := by rw [hf]; simp
    have hy : y ∈ l.filter p := by rw [hf]; simp
    rw [List.mem_filter] at hx hy
    have hne : x ≠ y := by
      rw [hf] at hnd
      intro he
      subst he
      simp at hnd
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨x, hx.1, y, hy.1, hlt, hx.2, hy.2⟩
    · exact ⟨y, hy.1, x, hx.1, hlt, hy.2, hx.2⟩

private lemma exists_three_of_two_lt_countP {N : ℕ} {p : ℕ → Bool}
    (h : 2 < (List.range N).countP p) :
    ∃ x y z, x < y ∧ y < z ∧ z < N ∧ p x ∧ p y ∧ p z := by
  rw [List.countP_eq_length_filter] at h
  have hpw : ((List.range N).filter p).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter p
  rcases hf : (List.range N).filter p with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp at h
  · have hx : x ∈ (List.range N).filter p := by rw [hf]; simp
    have hy : y ∈ (List.range N).filter p := by rw [hf]; simp
    have hz : z ∈ (List.range N).filter p := by rw [hf]; simp
    rw [hf] at hpw
    have hxy : x < y := List.rel_of_pairwise_cons hpw (by simp)
    have hyz : y < z := List.rel_of_pairwise_cons hpw.of_cons (by simp)
    rw [List.mem_filter, List.mem_range] at hx hy hz
    exact ⟨x, y, z, hxy, hyz, hz.1, hx.2, hy.2, hz.2⟩

/-- If `2 ≤ a n` then `n ≠ 0` and `n` (of bit length `L`) occurs at two bit positions. -/
theorem exists_two_occ_of_two_le_a {n : ℕ} (h : 2 ≤ a n) :
    0 < n ∧ ∃ s t, s < t ∧ Occ n (Nat.digits 2 n).length s ∧
      Occ n (Nat.digits 2 n).length t := by
  have hn : n ≠ 0 := by
    rintro rfl
    rw [a_zero] at h
    omega
  refine ⟨Nat.pos_of_ne_zero hn, ?_⟩
  rw [a_eq_countP hn] at h
  obtain ⟨x, hx, y, hy, hxy, px, py⟩ := exists_pair_of_two_le_countP List.nodup_range h
  rw [List.mem_range] at hx hy
  simp only [decide_eq_true_eq] at px py
  refine ⟨_, _, ?_, py, px⟩
  omega

/-! ### The reduction -/

private lemma digits_length_bounds {n : ℕ} (hn0 : 0 < n) :
    2 ^ ((Nat.digits 2 n).length - 1) ≤ n ∧ n < 2 ^ (Nat.digits 2 n).length := by
  refine ⟨?_, Nat.lt_base_pow_length_digits (by norm_num)⟩
  have h2n := Nat.base_pow_length_digits_le 2 n (by norm_num) hn0.ne'
  have hL : (Nat.digits 2 n).length ≠ 0 := by
    rw [Ne, List.length_eq_zero_iff]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hn0.ne'
  have e : 2 ^ (Nat.digits 2 n).length = 2 * 2 ^ ((Nat.digits 2 n).length - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- An odd number with two occurrences is at least `3`: `1` has only the window at `0`. -/
private lemma three_le_of_two_occ {k K s t : ℕ} (hodd : Odd k) (hklo : 2 ^ (K - 1) ≤ k)
    (hkhi : k < 2 ^ K) (hst : s < t) (h2 : Occ k K t) : 3 ≤ k := by
  by_contra hk
  have hk1 : k = 1 := by
    rcases hodd with ⟨j, hj⟩
    omega
  subst hk1
  have hK : K - 1 = 0 := by
    by_contra hK
    have : 2 ^ 1 ≤ 2 ^ (K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := occ_lt (by norm_num) hkhi h2
  omega

/-- **Reduction.**  If the upstream conjecture fails at `n`, then some odd `k ≤ n` with `k ≥ 3`
and bit length `L` has two occurrences `s < t` with `3 ≤ s`, `2 s ≤ t`, `L + s ≤ 2 t` and
`t < L`. -/
theorem reduction {n : ℕ} (h : 2 ≤ a n) :
    ∃ k L s t, k ≤ n ∧ Odd k ∧ 3 ≤ k ∧ 2 ^ (L - 1) ≤ k ∧ k < 2 ^ L ∧ s < t ∧
      Occ k L s ∧ Occ k L t ∧ 3 ≤ s ∧ 2 * s ≤ t ∧ L + s ≤ 2 * t ∧ t < L := by
  obtain ⟨hn0, s, t, hst, h1, h2⟩ := exists_two_occ_of_two_le_a h
  obtain ⟨hlo, hhi⟩ := digits_length_bounds hn0
  obtain ⟨k, K, s', t', hkn, hodd, hklo, hkhi, hst', h1', h2'⟩ :=
    exists_odd_of_two_occ n _ hn0 hlo hhi s t hst h1 h2
  have hk3 := three_le_of_two_occ hodd hklo hkhi hst' h2'
  obtain ⟨g1, g2, g3, g4⟩ := pair_geometry hodd hk3 hklo hkhi hst' h1' h2'
  exact ⟨k, K, s', t', hkn, hodd, hk3, hklo, hkhi, hst', h1', h2', g1, g2, g3, g4⟩

/-! ### An unconditional bound -/

/-- **`a n ≤ 2` for every `n`.**  Three occurrences of `n` descend to three occurrences
`s₁ < s₂ < s₃` of its odd part `k ≥ 3`, of bit length `K`, and `pair_geometry` gives
`K + s₁ ≤ 2 s₂ ≤ s₃ < K`. -/
theorem a_le_two (n : ℕ) : a n ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hn : n ≠ 0 := by
    rintro rfl
    rw [a_zero] at hcon
    omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  rw [a_eq_countP hn] at hcon
  obtain ⟨x, y, z, hxy, hyz, hz, px, py, pz⟩ := exists_three_of_two_lt_countP hcon
  clear hcon
  simp only [decide_eq_true_eq] at px py pz
  obtain ⟨hlo, hhi⟩ := digits_length_bounds hn0
  set L := (Nat.digits 2 n).length
  set M := (Nat.digits 2 (n ^ 2)).length
  obtain ⟨k, K, j, -, hodd, hklo, hkhi, hmap⟩ := occ_descent n L hn0 hlo hhi
  obtain ⟨hjx, hx⟩ := hmap _ px
  obtain ⟨hjy, hy⟩ := hmap _ py
  obtain ⟨hjz, hz'⟩ := hmap _ pz
  have h12 : M - L - z - j < M - L - y - j := by omega
  have h23 : M - L - y - j < M - L - x - j := by omega
  have hk3 := three_le_of_two_occ hodd hklo hkhi h12 hy
  obtain ⟨-, -, hA, -⟩ := pair_geometry hodd hk3 hklo hkhi h12 hz' hy
  obtain ⟨-, hB, -, hC⟩ := pair_geometry hodd hk3 hklo hkhi h23 hy hx
  omega

/-- The bit positions searched in reduced mode for bit length `L`: `[3, σ]` and `[τ, L - 1]`
with `σ = L / 3 + 1` and `τ = max (2 σ + 2) ⌈(L + σ + 1) / 2⌉`. -/
def SearchedPos (L p : ℕ) : Prop :=
  (3 ≤ p ∧ p ≤ L / 3 + 1) ∨
    (2 * (L / 3 + 1) + 2 ≤ p ∧ L + (L / 3 + 1) + 1 ≤ 2 * p ∧ p < L)

/-- **Finite form of the reduction used by the searches.**  If, for every bit length `L ≤ N`,
every odd `k` of bit length `L` that occurs at a searched position occurs nowhere else, then
`a n ≤ 1` for all `n < 2 ^ N`. -/
theorem a_le_one_of_search {N : ℕ}
    (hsearch : ∀ L ≤ N, ∀ k, Odd k → 2 ^ (L - 1) ≤ k → k < 2 ^ L → ∀ p q,
      SearchedPos L p → Occ k L p → Occ k L q → q = p) :
    ∀ n < 2 ^ N, a n ≤ 1 := by
  intro n hn
  by_contra hcon
  push Not at hcon
  obtain ⟨k, L, s, t, hkn, hodd, hk3, hklo, hkhi, hst, h1, h2, -, -, -, -⟩ := reduction hcon
  have hLN : L ≤ N := by
    have : 2 ^ (L - 1) < 2 ^ N := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  rcases pair_covered hodd hk3 hklo hkhi hst h1 h2 with hs | ht
  · have := hsearch L hLN k hodd hklo hkhi s t (Or.inl hs) h1 h2
    omega
  · have := hsearch L hLN k hodd hklo hkhi t s (Or.inr ht) h2 h1
    omega

end AgenticConjectures.OeisA076141
